/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate539 : CompactCertificate where
  left := 410
  right := 411
  center := 821 / 2
  grid := fun i =>
    match i.val with
    | 0 => 131
    | 1 => 96
    | 2 => 156
    | 3 => 28
    | 4 => 75
    | 5 => 205
    | 6 => 151
    | 7 => 259
    | 8 => 191
    | 9 => 292
    | 10 => 169
    | 11 => 299
    | 12 => 280
    | 13 => 200
    | 14 => 226
    | 15 => 189
    | 16 => 167
    | 17 => 242
    | 18 => 134
    | 19 => 113
    | 20 => 71
    | 21 => 38
    | 22 => 104
    | 23 => 141
    | 24 => 60
    | 25 => 243
    | _ => 162
  point := fun i =>
    match i.val with
    | 0 => 821 / 2
    | 1 => 1209489768226721 / 4000000000000
    | 2 => 391124140508993 / 800000000000
    | 3 => 352926097858147 / 4000000000000
    | 4 => 948009142009159 / 4000000000000
    | 5 => 2574029234596203 / 4000000000000
    | 6 => 1896018284019139 / 4000000000000
    | 7 => 3248859646263247 / 4000000000000
    | 8 => 2393095310936173 / 4000000000000
    | 9 => 3671623619054179 / 4000000000000
    | 10 => 2119812884823691 / 4000000000000
    | 11 => 3761645163282119 / 4000000000000
    | 12 => 3514616859315011 / 4000000000000
    | 13 => 2508196430371763 / 4000000000000
    | 14 => 2844027426027477 / 4000000000000
    | 15 => 2371053563057413 / 4000000000000
    | 16 => 2094897729801673 / 4000000000000
    | 17 => 607183014657627 / 800000000000
    | 18 => 1679500172834369 / 4000000000000
    | 19 => 1423730896466809 / 4000000000000
    | 20 => 890904689063827 / 4000000000000
    | 21 => 479131504793709 / 4000000000000
    | 22 => 1300935239868127 / 4000000000000
    | 23 => 1776315849665279 / 4000000000000
    | 24 => 751095310936173 / 4000000000000
    | 25 => 3053160739390733 / 4000000000000
    | _ => 2039369878037347 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (10258818559 / 1000000000000) (10258818594 / 1000000000000), orderedInterval (-38033509699 / 1000000000000) (-38033509665 / 1000000000000))
    | 1 => (orderedInterval (45883880411 / 1000000000000) (45883880541 / 1000000000000), orderedInterval (211559113 / 1000000000000) (211559244 / 1000000000000))
    | 2 => (orderedInterval (-13990207876 / 1000000000000) (-13990207741 / 1000000000000), orderedInterval (33277019309 / 1000000000000) (33277019444 / 1000000000000))
    | 3 => (orderedInterval (73719539197 / 1000000000000) (73719539198 / 1000000000000), orderedInterval (41780630948 / 1000000000000) (41780630949 / 1000000000000))
    | 4 => (orderedInterval (-42865608552 / 1000000000000) (-42865544793 / 1000000000000), orderedInterval (29222400867 / 1000000000000) (29222464625 / 1000000000000))
    | 5 => (orderedInterval (-8268769397 / 1000000000000) (-8268769396 / 1000000000000), orderedInterval (-30340314592 / 1000000000000) (-30340314591 / 1000000000000))
    | 6 => (orderedInterval (-14581784117 / 1000000000000) (-14581784116 / 1000000000000), orderedInterval (-33606617575 / 1000000000000) (-33606617574 / 1000000000000))
    | 7 => (orderedInterval (17436799715 / 1000000000000) (17436800286 / 1000000000000), orderedInterval (-21914274897 / 1000000000000) (-21914274326 / 1000000000000))
    | 8 => (orderedInterval (27184932350 / 1000000000000) (27184978819 / 1000000000000), orderedInterval (-18052504252 / 1000000000000) (-18052457783 / 1000000000000))
    | 9 => (orderedInterval (25673506187 / 1000000000000) (25673506636 / 1000000000000), orderedInterval (5853523470 / 1000000000000) (5853523919 / 1000000000000))
    | 10 => (orderedInterval (6572112561 / 1000000000000) (6572112566 / 1000000000000), orderedInterval (-34036822762 / 1000000000000) (-34036822757 / 1000000000000))
    | 11 => (orderedInterval (-24935348556 / 1000000000000) (-24935251780 / 1000000000000), orderedInterval (7442175474 / 1000000000000) (7442272249 / 1000000000000))
    | 12 => (orderedInterval (-5518266315 / 1000000000000) (-5518266314 / 1000000000000), orderedInterval (26348698500 / 1000000000000) (26348698501 / 1000000000000))
    | 13 => (orderedInterval (-14833014207 / 1000000000000) (-14833014039 / 1000000000000), orderedInterval (28211914377 / 1000000000000) (28211914545 / 1000000000000))
    | 14 => (orderedInterval (29192838983 / 1000000000000) (29192857654 / 1000000000000), orderedInterval (-6589801498 / 1000000000000) (-6589782827 / 1000000000000))
    | 15 => (orderedInterval (6909567359 / 1000000000000) (6909567363 / 1000000000000), orderedInterval (-32040880107 / 1000000000000) (-32040880103 / 1000000000000))
    | 16 => (orderedInterval (4740192173 / 1000000000000) (4740192175 / 1000000000000), orderedInterval (-34545712416 / 1000000000000) (-34545712414 / 1000000000000))
    | 17 => (orderedInterval (-13921102246 / 1000000000000) (-13921102162 / 1000000000000), orderedInterval (25405779001 / 1000000000000) (25405779085 / 1000000000000))
    | 18 => (orderedInterval (-11999810787 / 1000000000000) (-11999810721 / 1000000000000), orderedInterval (37057748936 / 1000000000000) (37057749003 / 1000000000000))
    | 19 => (orderedInterval (-41835623566 / 1000000000000) (-41835622277 / 1000000000000), orderedInterval (6253504329 / 1000000000000) (6253505618 / 1000000000000))
    | 20 => (orderedInterval (-23635651295 / 1000000000000) (-23635651294 / 1000000000000), orderedInterval (-47901787401 / 1000000000000) (-47901787400 / 1000000000000))
    | 21 => (orderedInterval (67590658249 / 1000000000000) (67590658250 / 1000000000000), orderedInterval (27035457537 / 1000000000000) (27035457538 / 1000000000000))
    | 22 => (orderedInterval (-28731810438 / 1000000000000) (-28731797830 / 1000000000000), orderedInterval (33687969957 / 1000000000000) (33687982566 / 1000000000000))
    | 23 => (orderedInterval (-35835271519 / 1000000000000) (-35835257238 / 1000000000000), orderedInterval (12263533907 / 1000000000000) (12263548189 / 1000000000000))
    | 24 => (orderedInterval (3665910468 / 1000000000000) (3665910470 / 1000000000000), orderedInterval (58101572691 / 1000000000000) (58101572692 / 1000000000000))
    | 25 => (orderedInterval (-17897850855 / 1000000000000) (-17897850854 / 1000000000000), orderedInterval (-22653531731 / 1000000000000) (-22653531730 / 1000000000000))
    | _ => (orderedInterval (35087236389 / 1000000000000) (35087238663 / 1000000000000), orderedInterval (-4223077879 / 1000000000000) (-4223075605 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (3672823936 / 1000000000000) (3672823987 / 1000000000000)
      | 1 => orderedInterval (-1777079122 / 1000000000000) (-1777076744 / 1000000000000)
      | 2 => orderedInterval (119185482 / 1000000000000) (119186646 / 1000000000000)
      | 3 => orderedInterval (-7619639486 / 1000000000000) (-7619625486 / 1000000000000)
      | 4 => orderedInterval (-1450763298 / 1000000000000) (-1450763138 / 1000000000000)
      | 5 => orderedInterval (-547911269 / 1000000000000) (-547911226 / 1000000000000)
      | 6 => orderedInterval (3517108335 / 1000000000000) (3517108522 / 1000000000000)
      | 7 => orderedInterval (2150138516 / 1000000000000) (2150139946 / 1000000000000)
      | _ => orderedInterval (-5104280615 / 1000000000000) (-5104280074 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-12747995785 / 1000000000000) (-12747995729 / 1000000000000)
      | 1 => orderedInterval (3899749196 / 1000000000000) (3899750596 / 1000000000000)
      | 2 => orderedInterval (701516524 / 1000000000000) (701518236 / 1000000000000)
      | 3 => orderedInterval (-3157780596 / 1000000000000) (-3157748564 / 1000000000000)
      | 4 => orderedInterval (3114732927 / 1000000000000) (3114733195 / 1000000000000)
      | 5 => orderedInterval (3190635006 / 1000000000000) (3190635068 / 1000000000000)
      | 6 => orderedInterval (-7213592231 / 1000000000000) (-7213592061 / 1000000000000)
      | 7 => orderedInterval (-1767939463 / 1000000000000) (-1767938007 / 1000000000000)
      | _ => orderedInterval (4573164317 / 1000000000000) (4573165007 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-3102641625 / 1000000000000) (-3102641562 / 1000000000000)
      | 1 => orderedInterval (-895386456 / 1000000000000) (-895385599 / 1000000000000)
      | 2 => orderedInterval (708235417 / 1000000000000) (708237947 / 1000000000000)
      | 3 => orderedInterval (40608700108 / 1000000000000) (40608773508 / 1000000000000)
      | 4 => orderedInterval (3252046364 / 1000000000000) (3252046816 / 1000000000000)
      | 5 => orderedInterval (1485864995 / 1000000000000) (1485865088 / 1000000000000)
      | 6 => orderedInterval (-3543438444 / 1000000000000) (-3543438287 / 1000000000000)
      | 7 => orderedInterval (-3512653320 / 1000000000000) (-3512651812 / 1000000000000)
      | _ => orderedInterval (5102265920 / 1000000000000) (5102266816 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (11782883938 / 1000000000000) (11782884009 / 1000000000000)
      | 1 => orderedInterval (-8507605261 / 1000000000000) (-8507604695 / 1000000000000)
      | 2 => orderedInterval (-3886743219 / 1000000000000) (-3886739470 / 1000000000000)
      | 3 => orderedInterval (4235964096 / 1000000000000) (4236132151 / 1000000000000)
      | 4 => orderedInterval (-5025110064 / 1000000000000) (-5025109292 / 1000000000000)
      | 5 => orderedInterval (-7106404788 / 1000000000000) (-7106404644 / 1000000000000)
      | 6 => orderedInterval (6828964656 / 1000000000000) (6828964803 / 1000000000000)
      | 7 => orderedInterval (1590936044 / 1000000000000) (1590937622 / 1000000000000)
      | _ => orderedInterval (-13418936108 / 1000000000000) (-13418934924 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (2482832529 / 1000000000000) (2482832610 / 1000000000000)
      | 1 => orderedInterval (3415675374 / 1000000000000) (3415675814 / 1000000000000)
      | 2 => orderedInterval (-5259480430 / 1000000000000) (-5259474835 / 1000000000000)
      | 3 => orderedInterval (-210348125816 / 1000000000000) (-210347740572 / 1000000000000)
      | 4 => orderedInterval (-6850661374 / 1000000000000) (-6850660048 / 1000000000000)
      | 5 => orderedInterval (-4502467943 / 1000000000000) (-4502467711 / 1000000000000)
      | 6 => orderedInterval (3338460985 / 1000000000000) (3338461125 / 1000000000000)
      | 7 => orderedInterval (4001407296 / 1000000000000) (4001408963 / 1000000000000)
      | _ => orderedInterval (1816912468 / 1000000000000) (1816914072 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-7040417521 / 1000000000000) (-7040397567 / 1000000000000)
    | 1 => orderedInterval (-9407510105 / 1000000000000) (-9407472259 / 1000000000000)
    | 2 => orderedInterval (40102992959 / 1000000000000) (40103072915 / 1000000000000)
    | 3 => orderedInterval (-13506050706 / 1000000000000) (-13505874440 / 1000000000000)
    | _ => orderedInterval (-211905446911 / 1000000000000) (-211905050582 / 1000000000000)

theorem compactCertificate539_stateChecks0 :
    compactCertificate539.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 131 12 (821 / 2)) (orderedInterval (10258818559 / 1000000000000) (10258818594 / 1000000000000), orderedInterval (-38033509699 / 1000000000000) (-38033509665 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 96 12 (1209489768226721 / 4000000000000)) (orderedInterval (45883880411 / 1000000000000) (45883880541 / 1000000000000), orderedInterval (211559113 / 1000000000000) (211559244 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 156 12 (391124140508993 / 800000000000)) (orderedInterval (-13990207876 / 1000000000000) (-13990207741 / 1000000000000), orderedInterval (33277019309 / 1000000000000) (33277019444 / 1000000000000))) = true
  rfl'

theorem compactCertificate539_stateChecks1 :
    compactCertificate539.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 28 12 (352926097858147 / 4000000000000)) (orderedInterval (73719539197 / 1000000000000) (73719539198 / 1000000000000), orderedInterval (41780630948 / 1000000000000) (41780630949 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 75 12 (948009142009159 / 4000000000000)) (orderedInterval (-42865608552 / 1000000000000) (-42865544793 / 1000000000000), orderedInterval (29222400867 / 1000000000000) (29222464625 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 205 12 (2574029234596203 / 4000000000000)) (orderedInterval (-8268769397 / 1000000000000) (-8268769396 / 1000000000000), orderedInterval (-30340314592 / 1000000000000) (-30340314591 / 1000000000000))) = true
  rfl'

theorem compactCertificate539_stateChecks2 :
    compactCertificate539.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 151 12 (1896018284019139 / 4000000000000)) (orderedInterval (-14581784117 / 1000000000000) (-14581784116 / 1000000000000), orderedInterval (-33606617575 / 1000000000000) (-33606617574 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 259 12 (3248859646263247 / 4000000000000)) (orderedInterval (17436799715 / 1000000000000) (17436800286 / 1000000000000), orderedInterval (-21914274897 / 1000000000000) (-21914274326 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 191 12 (2393095310936173 / 4000000000000)) (orderedInterval (27184932350 / 1000000000000) (27184978819 / 1000000000000), orderedInterval (-18052504252 / 1000000000000) (-18052457783 / 1000000000000))) = true
  rfl'

theorem compactCertificate539_stateChecks3 :
    compactCertificate539.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 292 12 (3671623619054179 / 4000000000000)) (orderedInterval (25673506187 / 1000000000000) (25673506636 / 1000000000000), orderedInterval (5853523470 / 1000000000000) (5853523919 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 169 12 (2119812884823691 / 4000000000000)) (orderedInterval (6572112561 / 1000000000000) (6572112566 / 1000000000000), orderedInterval (-34036822762 / 1000000000000) (-34036822757 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 299 12 (3761645163282119 / 4000000000000)) (orderedInterval (-24935348556 / 1000000000000) (-24935251780 / 1000000000000), orderedInterval (7442175474 / 1000000000000) (7442272249 / 1000000000000))) = true
  rfl'

theorem compactCertificate539_stateChecks4 :
    compactCertificate539.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 280 12 (3514616859315011 / 4000000000000)) (orderedInterval (-5518266315 / 1000000000000) (-5518266314 / 1000000000000), orderedInterval (26348698500 / 1000000000000) (26348698501 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 200 12 (2508196430371763 / 4000000000000)) (orderedInterval (-14833014207 / 1000000000000) (-14833014039 / 1000000000000), orderedInterval (28211914377 / 1000000000000) (28211914545 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 226 12 (2844027426027477 / 4000000000000)) (orderedInterval (29192838983 / 1000000000000) (29192857654 / 1000000000000), orderedInterval (-6589801498 / 1000000000000) (-6589782827 / 1000000000000))) = true
  rfl'

theorem compactCertificate539_stateChecks5 :
    compactCertificate539.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 189 12 (2371053563057413 / 4000000000000)) (orderedInterval (6909567359 / 1000000000000) (6909567363 / 1000000000000), orderedInterval (-32040880107 / 1000000000000) (-32040880103 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 167 12 (2094897729801673 / 4000000000000)) (orderedInterval (4740192173 / 1000000000000) (4740192175 / 1000000000000), orderedInterval (-34545712416 / 1000000000000) (-34545712414 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 242 12 (607183014657627 / 800000000000)) (orderedInterval (-13921102246 / 1000000000000) (-13921102162 / 1000000000000), orderedInterval (25405779001 / 1000000000000) (25405779085 / 1000000000000))) = true
  rfl'

theorem compactCertificate539_stateChecks6 :
    compactCertificate539.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 134 12 (1679500172834369 / 4000000000000)) (orderedInterval (-11999810787 / 1000000000000) (-11999810721 / 1000000000000), orderedInterval (37057748936 / 1000000000000) (37057749003 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 113 12 (1423730896466809 / 4000000000000)) (orderedInterval (-41835623566 / 1000000000000) (-41835622277 / 1000000000000), orderedInterval (6253504329 / 1000000000000) (6253505618 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (890904689063827 / 4000000000000)) (orderedInterval (-23635651295 / 1000000000000) (-23635651294 / 1000000000000), orderedInterval (-47901787401 / 1000000000000) (-47901787400 / 1000000000000))) = true
  rfl'

theorem compactCertificate539_stateChecks7 :
    compactCertificate539.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (479131504793709 / 4000000000000)) (orderedInterval (67590658249 / 1000000000000) (67590658250 / 1000000000000), orderedInterval (27035457537 / 1000000000000) (27035457538 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 104 12 (1300935239868127 / 4000000000000)) (orderedInterval (-28731810438 / 1000000000000) (-28731797830 / 1000000000000), orderedInterval (33687969957 / 1000000000000) (33687982566 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 141 12 (1776315849665279 / 4000000000000)) (orderedInterval (-35835271519 / 1000000000000) (-35835257238 / 1000000000000), orderedInterval (12263533907 / 1000000000000) (12263548189 / 1000000000000))) = true
  rfl'

theorem compactCertificate539_stateChecks8 :
    compactCertificate539.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 60 12 (751095310936173 / 4000000000000)) (orderedInterval (3665910468 / 1000000000000) (3665910470 / 1000000000000), orderedInterval (58101572691 / 1000000000000) (58101572692 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 243 12 (3053160739390733 / 4000000000000)) (orderedInterval (-17897850855 / 1000000000000) (-17897850854 / 1000000000000), orderedInterval (-22653531731 / 1000000000000) (-22653531730 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 162 12 (2039369878037347 / 4000000000000)) (orderedInterval (35087236389 / 1000000000000) (35087238663 / 1000000000000), orderedInterval (-4223077879 / 1000000000000) (-4223075605 / 1000000000000))) = true
  rfl'

theorem compactCertificate539_states : ∀ j,
    BesselStateValid (compactCertificate539.point j) (compactCertificate539.state j) :=
  compactCertificate539.statesValid_of_checks3 compactCertificate539_stateChecks0
    compactCertificate539_stateChecks1 compactCertificate539_stateChecks2
    compactCertificate539_stateChecks3 compactCertificate539_stateChecks4
    compactCertificate539_stateChecks5 compactCertificate539_stateChecks6
    compactCertificate539_stateChecks7 compactCertificate539_stateChecks8

theorem compactCertificate539_chunkChecks0_0 :
    compactCertificate539.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (821 / 2) 0 (IntervalRat.scale (821 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (10258818559 / 1000000000000) (10258818594 / 1000000000000), orderedInterval (-38033509699 / 1000000000000) (-38033509665 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1209489768226721 / 4000000000000) 0 (IntervalRat.scale (821 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (45883880411 / 1000000000000) (45883880541 / 1000000000000), orderedInterval (211559113 / 1000000000000) (211559244 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (391124140508993 / 800000000000) 0 (IntervalRat.scale (821 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-13990207876 / 1000000000000) (-13990207741 / 1000000000000), orderedInterval (33277019309 / 1000000000000) (33277019444 / 1000000000000)))) (orderedInterval (3672823936 / 1000000000000) (3672823987 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (352926097858147 / 4000000000000) 0 (IntervalRat.scale (821 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (73719539197 / 1000000000000) (73719539198 / 1000000000000), orderedInterval (41780630948 / 1000000000000) (41780630949 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (948009142009159 / 4000000000000) 0 (IntervalRat.scale (821 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-42865608552 / 1000000000000) (-42865544793 / 1000000000000), orderedInterval (29222400867 / 1000000000000) (29222464625 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2574029234596203 / 4000000000000) 0 (IntervalRat.scale (821 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-8268769397 / 1000000000000) (-8268769396 / 1000000000000), orderedInterval (-30340314592 / 1000000000000) (-30340314591 / 1000000000000)))) (orderedInterval (-1777079122 / 1000000000000) (-1777076744 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1896018284019139 / 4000000000000) 0 (IntervalRat.scale (821 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-14581784117 / 1000000000000) (-14581784116 / 1000000000000), orderedInterval (-33606617575 / 1000000000000) (-33606617574 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3248859646263247 / 4000000000000) 0 (IntervalRat.scale (821 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (17436799715 / 1000000000000) (17436800286 / 1000000000000), orderedInterval (-21914274897 / 1000000000000) (-21914274326 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2393095310936173 / 4000000000000) 0 (IntervalRat.scale (821 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (27184932350 / 1000000000000) (27184978819 / 1000000000000), orderedInterval (-18052504252 / 1000000000000) (-18052457783 / 1000000000000)))) (orderedInterval (119185482 / 1000000000000) (119186646 / 1000000000000))) = true
  rfl'

theorem compactCertificate539_chunkChecks0_1 :
    compactCertificate539.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3671623619054179 / 4000000000000) 0 (IntervalRat.scale (821 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (25673506187 / 1000000000000) (25673506636 / 1000000000000), orderedInterval (5853523470 / 1000000000000) (5853523919 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2119812884823691 / 4000000000000) 0 (IntervalRat.scale (821 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (6572112561 / 1000000000000) (6572112566 / 1000000000000), orderedInterval (-34036822762 / 1000000000000) (-34036822757 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3761645163282119 / 4000000000000) 0 (IntervalRat.scale (821 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-24935348556 / 1000000000000) (-24935251780 / 1000000000000), orderedInterval (7442175474 / 1000000000000) (7442272249 / 1000000000000)))) (orderedInterval (-7619639486 / 1000000000000) (-7619625486 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3514616859315011 / 4000000000000) 0 (IntervalRat.scale (821 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-5518266315 / 1000000000000) (-5518266314 / 1000000000000), orderedInterval (26348698500 / 1000000000000) (26348698501 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2508196430371763 / 4000000000000) 0 (IntervalRat.scale (821 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-14833014207 / 1000000000000) (-14833014039 / 1000000000000), orderedInterval (28211914377 / 1000000000000) (28211914545 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2844027426027477 / 4000000000000) 0 (IntervalRat.scale (821 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (29192838983 / 1000000000000) (29192857654 / 1000000000000), orderedInterval (-6589801498 / 1000000000000) (-6589782827 / 1000000000000)))) (orderedInterval (-1450763298 / 1000000000000) (-1450763138 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2371053563057413 / 4000000000000) 0 (IntervalRat.scale (821 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (6909567359 / 1000000000000) (6909567363 / 1000000000000), orderedInterval (-32040880107 / 1000000000000) (-32040880103 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2094897729801673 / 4000000000000) 0 (IntervalRat.scale (821 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (4740192173 / 1000000000000) (4740192175 / 1000000000000), orderedInterval (-34545712416 / 1000000000000) (-34545712414 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (607183014657627 / 800000000000) 0 (IntervalRat.scale (821 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-13921102246 / 1000000000000) (-13921102162 / 1000000000000), orderedInterval (25405779001 / 1000000000000) (25405779085 / 1000000000000)))) (orderedInterval (-547911269 / 1000000000000) (-547911226 / 1000000000000))) = true
  rfl'

theorem compactCertificate539_chunkChecks0_2 :
    compactCertificate539.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1679500172834369 / 4000000000000) 0 (IntervalRat.scale (821 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-11999810787 / 1000000000000) (-11999810721 / 1000000000000), orderedInterval (37057748936 / 1000000000000) (37057749003 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1423730896466809 / 4000000000000) 0 (IntervalRat.scale (821 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-41835623566 / 1000000000000) (-41835622277 / 1000000000000), orderedInterval (6253504329 / 1000000000000) (6253505618 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (890904689063827 / 4000000000000) 0 (IntervalRat.scale (821 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-23635651295 / 1000000000000) (-23635651294 / 1000000000000), orderedInterval (-47901787401 / 1000000000000) (-47901787400 / 1000000000000)))) (orderedInterval (3517108335 / 1000000000000) (3517108522 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (479131504793709 / 4000000000000) 0 (IntervalRat.scale (821 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (67590658249 / 1000000000000) (67590658250 / 1000000000000), orderedInterval (27035457537 / 1000000000000) (27035457538 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1300935239868127 / 4000000000000) 0 (IntervalRat.scale (821 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-28731810438 / 1000000000000) (-28731797830 / 1000000000000), orderedInterval (33687969957 / 1000000000000) (33687982566 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1776315849665279 / 4000000000000) 0 (IntervalRat.scale (821 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-35835271519 / 1000000000000) (-35835257238 / 1000000000000), orderedInterval (12263533907 / 1000000000000) (12263548189 / 1000000000000)))) (orderedInterval (2150138516 / 1000000000000) (2150139946 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (751095310936173 / 4000000000000) 0 (IntervalRat.scale (821 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (3665910468 / 1000000000000) (3665910470 / 1000000000000), orderedInterval (58101572691 / 1000000000000) (58101572692 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3053160739390733 / 4000000000000) 0 (IntervalRat.scale (821 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-17897850855 / 1000000000000) (-17897850854 / 1000000000000), orderedInterval (-22653531731 / 1000000000000) (-22653531730 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2039369878037347 / 4000000000000) 0 (IntervalRat.scale (821 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (35087236389 / 1000000000000) (35087238663 / 1000000000000), orderedInterval (-4223077879 / 1000000000000) (-4223075605 / 1000000000000)))) (orderedInterval (-5104280615 / 1000000000000) (-5104280074 / 1000000000000))) = true
  rfl'

theorem compactCertificate539_chunkChecks0 :
    compactCertificate539.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate539.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate539_chunkChecks0_0
    compactCertificate539_chunkChecks0_1 compactCertificate539_chunkChecks0_2

theorem compactCertificate539_chunkChecks1_0 :
    compactCertificate539.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (821 / 2) 1 (IntervalRat.scale (821 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (10258818559 / 1000000000000) (10258818594 / 1000000000000), orderedInterval (-38033509699 / 1000000000000) (-38033509665 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1209489768226721 / 4000000000000) 1 (IntervalRat.scale (821 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (45883880411 / 1000000000000) (45883880541 / 1000000000000), orderedInterval (211559113 / 1000000000000) (211559244 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (391124140508993 / 800000000000) 1 (IntervalRat.scale (821 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-13990207876 / 1000000000000) (-13990207741 / 1000000000000), orderedInterval (33277019309 / 1000000000000) (33277019444 / 1000000000000)))) (orderedInterval (-12747995785 / 1000000000000) (-12747995729 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (352926097858147 / 4000000000000) 1 (IntervalRat.scale (821 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (73719539197 / 1000000000000) (73719539198 / 1000000000000), orderedInterval (41780630948 / 1000000000000) (41780630949 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (948009142009159 / 4000000000000) 1 (IntervalRat.scale (821 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-42865608552 / 1000000000000) (-42865544793 / 1000000000000), orderedInterval (29222400867 / 1000000000000) (29222464625 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2574029234596203 / 4000000000000) 1 (IntervalRat.scale (821 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-8268769397 / 1000000000000) (-8268769396 / 1000000000000), orderedInterval (-30340314592 / 1000000000000) (-30340314591 / 1000000000000)))) (orderedInterval (3899749196 / 1000000000000) (3899750596 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1896018284019139 / 4000000000000) 1 (IntervalRat.scale (821 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-14581784117 / 1000000000000) (-14581784116 / 1000000000000), orderedInterval (-33606617575 / 1000000000000) (-33606617574 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3248859646263247 / 4000000000000) 1 (IntervalRat.scale (821 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (17436799715 / 1000000000000) (17436800286 / 1000000000000), orderedInterval (-21914274897 / 1000000000000) (-21914274326 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2393095310936173 / 4000000000000) 1 (IntervalRat.scale (821 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (27184932350 / 1000000000000) (27184978819 / 1000000000000), orderedInterval (-18052504252 / 1000000000000) (-18052457783 / 1000000000000)))) (orderedInterval (701516524 / 1000000000000) (701518236 / 1000000000000))) = true
  rfl'

theorem compactCertificate539_chunkChecks1_1 :
    compactCertificate539.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3671623619054179 / 4000000000000) 1 (IntervalRat.scale (821 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (25673506187 / 1000000000000) (25673506636 / 1000000000000), orderedInterval (5853523470 / 1000000000000) (5853523919 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2119812884823691 / 4000000000000) 1 (IntervalRat.scale (821 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (6572112561 / 1000000000000) (6572112566 / 1000000000000), orderedInterval (-34036822762 / 1000000000000) (-34036822757 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3761645163282119 / 4000000000000) 1 (IntervalRat.scale (821 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-24935348556 / 1000000000000) (-24935251780 / 1000000000000), orderedInterval (7442175474 / 1000000000000) (7442272249 / 1000000000000)))) (orderedInterval (-3157780596 / 1000000000000) (-3157748564 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3514616859315011 / 4000000000000) 1 (IntervalRat.scale (821 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-5518266315 / 1000000000000) (-5518266314 / 1000000000000), orderedInterval (26348698500 / 1000000000000) (26348698501 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2508196430371763 / 4000000000000) 1 (IntervalRat.scale (821 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-14833014207 / 1000000000000) (-14833014039 / 1000000000000), orderedInterval (28211914377 / 1000000000000) (28211914545 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2844027426027477 / 4000000000000) 1 (IntervalRat.scale (821 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (29192838983 / 1000000000000) (29192857654 / 1000000000000), orderedInterval (-6589801498 / 1000000000000) (-6589782827 / 1000000000000)))) (orderedInterval (3114732927 / 1000000000000) (3114733195 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2371053563057413 / 4000000000000) 1 (IntervalRat.scale (821 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (6909567359 / 1000000000000) (6909567363 / 1000000000000), orderedInterval (-32040880107 / 1000000000000) (-32040880103 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2094897729801673 / 4000000000000) 1 (IntervalRat.scale (821 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (4740192173 / 1000000000000) (4740192175 / 1000000000000), orderedInterval (-34545712416 / 1000000000000) (-34545712414 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (607183014657627 / 800000000000) 1 (IntervalRat.scale (821 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-13921102246 / 1000000000000) (-13921102162 / 1000000000000), orderedInterval (25405779001 / 1000000000000) (25405779085 / 1000000000000)))) (orderedInterval (3190635006 / 1000000000000) (3190635068 / 1000000000000))) = true
  rfl'

theorem compactCertificate539_chunkChecks1_2 :
    compactCertificate539.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1679500172834369 / 4000000000000) 1 (IntervalRat.scale (821 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-11999810787 / 1000000000000) (-11999810721 / 1000000000000), orderedInterval (37057748936 / 1000000000000) (37057749003 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1423730896466809 / 4000000000000) 1 (IntervalRat.scale (821 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-41835623566 / 1000000000000) (-41835622277 / 1000000000000), orderedInterval (6253504329 / 1000000000000) (6253505618 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (890904689063827 / 4000000000000) 1 (IntervalRat.scale (821 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-23635651295 / 1000000000000) (-23635651294 / 1000000000000), orderedInterval (-47901787401 / 1000000000000) (-47901787400 / 1000000000000)))) (orderedInterval (-7213592231 / 1000000000000) (-7213592061 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (479131504793709 / 4000000000000) 1 (IntervalRat.scale (821 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (67590658249 / 1000000000000) (67590658250 / 1000000000000), orderedInterval (27035457537 / 1000000000000) (27035457538 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1300935239868127 / 4000000000000) 1 (IntervalRat.scale (821 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-28731810438 / 1000000000000) (-28731797830 / 1000000000000), orderedInterval (33687969957 / 1000000000000) (33687982566 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1776315849665279 / 4000000000000) 1 (IntervalRat.scale (821 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-35835271519 / 1000000000000) (-35835257238 / 1000000000000), orderedInterval (12263533907 / 1000000000000) (12263548189 / 1000000000000)))) (orderedInterval (-1767939463 / 1000000000000) (-1767938007 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (751095310936173 / 4000000000000) 1 (IntervalRat.scale (821 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (3665910468 / 1000000000000) (3665910470 / 1000000000000), orderedInterval (58101572691 / 1000000000000) (58101572692 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3053160739390733 / 4000000000000) 1 (IntervalRat.scale (821 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-17897850855 / 1000000000000) (-17897850854 / 1000000000000), orderedInterval (-22653531731 / 1000000000000) (-22653531730 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2039369878037347 / 4000000000000) 1 (IntervalRat.scale (821 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (35087236389 / 1000000000000) (35087238663 / 1000000000000), orderedInterval (-4223077879 / 1000000000000) (-4223075605 / 1000000000000)))) (orderedInterval (4573164317 / 1000000000000) (4573165007 / 1000000000000))) = true
  rfl'

theorem compactCertificate539_chunkChecks1 :
    compactCertificate539.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate539.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate539_chunkChecks1_0
    compactCertificate539_chunkChecks1_1 compactCertificate539_chunkChecks1_2

theorem compactCertificate539_chunkChecks2_0 :
    compactCertificate539.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (821 / 2) 2 (IntervalRat.scale (821 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (10258818559 / 1000000000000) (10258818594 / 1000000000000), orderedInterval (-38033509699 / 1000000000000) (-38033509665 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1209489768226721 / 4000000000000) 2 (IntervalRat.scale (821 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (45883880411 / 1000000000000) (45883880541 / 1000000000000), orderedInterval (211559113 / 1000000000000) (211559244 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (391124140508993 / 800000000000) 2 (IntervalRat.scale (821 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-13990207876 / 1000000000000) (-13990207741 / 1000000000000), orderedInterval (33277019309 / 1000000000000) (33277019444 / 1000000000000)))) (orderedInterval (-3102641625 / 1000000000000) (-3102641562 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (352926097858147 / 4000000000000) 2 (IntervalRat.scale (821 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (73719539197 / 1000000000000) (73719539198 / 1000000000000), orderedInterval (41780630948 / 1000000000000) (41780630949 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (948009142009159 / 4000000000000) 2 (IntervalRat.scale (821 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-42865608552 / 1000000000000) (-42865544793 / 1000000000000), orderedInterval (29222400867 / 1000000000000) (29222464625 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2574029234596203 / 4000000000000) 2 (IntervalRat.scale (821 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-8268769397 / 1000000000000) (-8268769396 / 1000000000000), orderedInterval (-30340314592 / 1000000000000) (-30340314591 / 1000000000000)))) (orderedInterval (-895386456 / 1000000000000) (-895385599 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1896018284019139 / 4000000000000) 2 (IntervalRat.scale (821 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-14581784117 / 1000000000000) (-14581784116 / 1000000000000), orderedInterval (-33606617575 / 1000000000000) (-33606617574 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3248859646263247 / 4000000000000) 2 (IntervalRat.scale (821 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (17436799715 / 1000000000000) (17436800286 / 1000000000000), orderedInterval (-21914274897 / 1000000000000) (-21914274326 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2393095310936173 / 4000000000000) 2 (IntervalRat.scale (821 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (27184932350 / 1000000000000) (27184978819 / 1000000000000), orderedInterval (-18052504252 / 1000000000000) (-18052457783 / 1000000000000)))) (orderedInterval (708235417 / 1000000000000) (708237947 / 1000000000000))) = true
  rfl'

theorem compactCertificate539_chunkChecks2_1 :
    compactCertificate539.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3671623619054179 / 4000000000000) 2 (IntervalRat.scale (821 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (25673506187 / 1000000000000) (25673506636 / 1000000000000), orderedInterval (5853523470 / 1000000000000) (5853523919 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2119812884823691 / 4000000000000) 2 (IntervalRat.scale (821 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (6572112561 / 1000000000000) (6572112566 / 1000000000000), orderedInterval (-34036822762 / 1000000000000) (-34036822757 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3761645163282119 / 4000000000000) 2 (IntervalRat.scale (821 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-24935348556 / 1000000000000) (-24935251780 / 1000000000000), orderedInterval (7442175474 / 1000000000000) (7442272249 / 1000000000000)))) (orderedInterval (40608700108 / 1000000000000) (40608773508 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3514616859315011 / 4000000000000) 2 (IntervalRat.scale (821 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-5518266315 / 1000000000000) (-5518266314 / 1000000000000), orderedInterval (26348698500 / 1000000000000) (26348698501 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2508196430371763 / 4000000000000) 2 (IntervalRat.scale (821 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-14833014207 / 1000000000000) (-14833014039 / 1000000000000), orderedInterval (28211914377 / 1000000000000) (28211914545 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2844027426027477 / 4000000000000) 2 (IntervalRat.scale (821 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (29192838983 / 1000000000000) (29192857654 / 1000000000000), orderedInterval (-6589801498 / 1000000000000) (-6589782827 / 1000000000000)))) (orderedInterval (3252046364 / 1000000000000) (3252046816 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2371053563057413 / 4000000000000) 2 (IntervalRat.scale (821 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (6909567359 / 1000000000000) (6909567363 / 1000000000000), orderedInterval (-32040880107 / 1000000000000) (-32040880103 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2094897729801673 / 4000000000000) 2 (IntervalRat.scale (821 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (4740192173 / 1000000000000) (4740192175 / 1000000000000), orderedInterval (-34545712416 / 1000000000000) (-34545712414 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (607183014657627 / 800000000000) 2 (IntervalRat.scale (821 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-13921102246 / 1000000000000) (-13921102162 / 1000000000000), orderedInterval (25405779001 / 1000000000000) (25405779085 / 1000000000000)))) (orderedInterval (1485864995 / 1000000000000) (1485865088 / 1000000000000))) = true
  rfl'

theorem compactCertificate539_chunkChecks2_2 :
    compactCertificate539.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1679500172834369 / 4000000000000) 2 (IntervalRat.scale (821 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-11999810787 / 1000000000000) (-11999810721 / 1000000000000), orderedInterval (37057748936 / 1000000000000) (37057749003 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1423730896466809 / 4000000000000) 2 (IntervalRat.scale (821 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-41835623566 / 1000000000000) (-41835622277 / 1000000000000), orderedInterval (6253504329 / 1000000000000) (6253505618 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (890904689063827 / 4000000000000) 2 (IntervalRat.scale (821 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-23635651295 / 1000000000000) (-23635651294 / 1000000000000), orderedInterval (-47901787401 / 1000000000000) (-47901787400 / 1000000000000)))) (orderedInterval (-3543438444 / 1000000000000) (-3543438287 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (479131504793709 / 4000000000000) 2 (IntervalRat.scale (821 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (67590658249 / 1000000000000) (67590658250 / 1000000000000), orderedInterval (27035457537 / 1000000000000) (27035457538 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1300935239868127 / 4000000000000) 2 (IntervalRat.scale (821 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-28731810438 / 1000000000000) (-28731797830 / 1000000000000), orderedInterval (33687969957 / 1000000000000) (33687982566 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1776315849665279 / 4000000000000) 2 (IntervalRat.scale (821 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-35835271519 / 1000000000000) (-35835257238 / 1000000000000), orderedInterval (12263533907 / 1000000000000) (12263548189 / 1000000000000)))) (orderedInterval (-3512653320 / 1000000000000) (-3512651812 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (751095310936173 / 4000000000000) 2 (IntervalRat.scale (821 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (3665910468 / 1000000000000) (3665910470 / 1000000000000), orderedInterval (58101572691 / 1000000000000) (58101572692 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3053160739390733 / 4000000000000) 2 (IntervalRat.scale (821 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-17897850855 / 1000000000000) (-17897850854 / 1000000000000), orderedInterval (-22653531731 / 1000000000000) (-22653531730 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2039369878037347 / 4000000000000) 2 (IntervalRat.scale (821 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (35087236389 / 1000000000000) (35087238663 / 1000000000000), orderedInterval (-4223077879 / 1000000000000) (-4223075605 / 1000000000000)))) (orderedInterval (5102265920 / 1000000000000) (5102266816 / 1000000000000))) = true
  rfl'

theorem compactCertificate539_chunkChecks2 :
    compactCertificate539.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate539.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate539_chunkChecks2_0
    compactCertificate539_chunkChecks2_1 compactCertificate539_chunkChecks2_2

theorem compactCertificate539_chunkChecks3_0 :
    compactCertificate539.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (821 / 2) 3 (IntervalRat.scale (821 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (10258818559 / 1000000000000) (10258818594 / 1000000000000), orderedInterval (-38033509699 / 1000000000000) (-38033509665 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1209489768226721 / 4000000000000) 3 (IntervalRat.scale (821 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (45883880411 / 1000000000000) (45883880541 / 1000000000000), orderedInterval (211559113 / 1000000000000) (211559244 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (391124140508993 / 800000000000) 3 (IntervalRat.scale (821 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-13990207876 / 1000000000000) (-13990207741 / 1000000000000), orderedInterval (33277019309 / 1000000000000) (33277019444 / 1000000000000)))) (orderedInterval (11782883938 / 1000000000000) (11782884009 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (352926097858147 / 4000000000000) 3 (IntervalRat.scale (821 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (73719539197 / 1000000000000) (73719539198 / 1000000000000), orderedInterval (41780630948 / 1000000000000) (41780630949 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (948009142009159 / 4000000000000) 3 (IntervalRat.scale (821 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-42865608552 / 1000000000000) (-42865544793 / 1000000000000), orderedInterval (29222400867 / 1000000000000) (29222464625 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2574029234596203 / 4000000000000) 3 (IntervalRat.scale (821 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-8268769397 / 1000000000000) (-8268769396 / 1000000000000), orderedInterval (-30340314592 / 1000000000000) (-30340314591 / 1000000000000)))) (orderedInterval (-8507605261 / 1000000000000) (-8507604695 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1896018284019139 / 4000000000000) 3 (IntervalRat.scale (821 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-14581784117 / 1000000000000) (-14581784116 / 1000000000000), orderedInterval (-33606617575 / 1000000000000) (-33606617574 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3248859646263247 / 4000000000000) 3 (IntervalRat.scale (821 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (17436799715 / 1000000000000) (17436800286 / 1000000000000), orderedInterval (-21914274897 / 1000000000000) (-21914274326 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2393095310936173 / 4000000000000) 3 (IntervalRat.scale (821 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (27184932350 / 1000000000000) (27184978819 / 1000000000000), orderedInterval (-18052504252 / 1000000000000) (-18052457783 / 1000000000000)))) (orderedInterval (-3886743219 / 1000000000000) (-3886739470 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate539_chunkChecks3_1 :
    compactCertificate539.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3671623619054179 / 4000000000000) 3 (IntervalRat.scale (821 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (25673506187 / 1000000000000) (25673506636 / 1000000000000), orderedInterval (5853523470 / 1000000000000) (5853523919 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2119812884823691 / 4000000000000) 3 (IntervalRat.scale (821 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (6572112561 / 1000000000000) (6572112566 / 1000000000000), orderedInterval (-34036822762 / 1000000000000) (-34036822757 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3761645163282119 / 4000000000000) 3 (IntervalRat.scale (821 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-24935348556 / 1000000000000) (-24935251780 / 1000000000000), orderedInterval (7442175474 / 1000000000000) (7442272249 / 1000000000000)))) (orderedInterval (4235964096 / 1000000000000) (4236132151 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3514616859315011 / 4000000000000) 3 (IntervalRat.scale (821 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-5518266315 / 1000000000000) (-5518266314 / 1000000000000), orderedInterval (26348698500 / 1000000000000) (26348698501 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2508196430371763 / 4000000000000) 3 (IntervalRat.scale (821 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-14833014207 / 1000000000000) (-14833014039 / 1000000000000), orderedInterval (28211914377 / 1000000000000) (28211914545 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2844027426027477 / 4000000000000) 3 (IntervalRat.scale (821 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (29192838983 / 1000000000000) (29192857654 / 1000000000000), orderedInterval (-6589801498 / 1000000000000) (-6589782827 / 1000000000000)))) (orderedInterval (-5025110064 / 1000000000000) (-5025109292 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2371053563057413 / 4000000000000) 3 (IntervalRat.scale (821 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (6909567359 / 1000000000000) (6909567363 / 1000000000000), orderedInterval (-32040880107 / 1000000000000) (-32040880103 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2094897729801673 / 4000000000000) 3 (IntervalRat.scale (821 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (4740192173 / 1000000000000) (4740192175 / 1000000000000), orderedInterval (-34545712416 / 1000000000000) (-34545712414 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (607183014657627 / 800000000000) 3 (IntervalRat.scale (821 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-13921102246 / 1000000000000) (-13921102162 / 1000000000000), orderedInterval (25405779001 / 1000000000000) (25405779085 / 1000000000000)))) (orderedInterval (-7106404788 / 1000000000000) (-7106404644 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate539_chunkChecks3_2 :
    compactCertificate539.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1679500172834369 / 4000000000000) 3 (IntervalRat.scale (821 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-11999810787 / 1000000000000) (-11999810721 / 1000000000000), orderedInterval (37057748936 / 1000000000000) (37057749003 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1423730896466809 / 4000000000000) 3 (IntervalRat.scale (821 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-41835623566 / 1000000000000) (-41835622277 / 1000000000000), orderedInterval (6253504329 / 1000000000000) (6253505618 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (890904689063827 / 4000000000000) 3 (IntervalRat.scale (821 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-23635651295 / 1000000000000) (-23635651294 / 1000000000000), orderedInterval (-47901787401 / 1000000000000) (-47901787400 / 1000000000000)))) (orderedInterval (6828964656 / 1000000000000) (6828964803 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (479131504793709 / 4000000000000) 3 (IntervalRat.scale (821 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (67590658249 / 1000000000000) (67590658250 / 1000000000000), orderedInterval (27035457537 / 1000000000000) (27035457538 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1300935239868127 / 4000000000000) 3 (IntervalRat.scale (821 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-28731810438 / 1000000000000) (-28731797830 / 1000000000000), orderedInterval (33687969957 / 1000000000000) (33687982566 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1776315849665279 / 4000000000000) 3 (IntervalRat.scale (821 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-35835271519 / 1000000000000) (-35835257238 / 1000000000000), orderedInterval (12263533907 / 1000000000000) (12263548189 / 1000000000000)))) (orderedInterval (1590936044 / 1000000000000) (1590937622 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (751095310936173 / 4000000000000) 3 (IntervalRat.scale (821 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (3665910468 / 1000000000000) (3665910470 / 1000000000000), orderedInterval (58101572691 / 1000000000000) (58101572692 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3053160739390733 / 4000000000000) 3 (IntervalRat.scale (821 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-17897850855 / 1000000000000) (-17897850854 / 1000000000000), orderedInterval (-22653531731 / 1000000000000) (-22653531730 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2039369878037347 / 4000000000000) 3 (IntervalRat.scale (821 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (35087236389 / 1000000000000) (35087238663 / 1000000000000), orderedInterval (-4223077879 / 1000000000000) (-4223075605 / 1000000000000)))) (orderedInterval (-13418936108 / 1000000000000) (-13418934924 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate539_chunkChecks3 :
    compactCertificate539.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate539.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate539_chunkChecks3_0
    compactCertificate539_chunkChecks3_1 compactCertificate539_chunkChecks3_2

theorem compactCertificate539_chunkChecks4_0 :
    compactCertificate539.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (821 / 2) 4 (IntervalRat.scale (821 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (10258818559 / 1000000000000) (10258818594 / 1000000000000), orderedInterval (-38033509699 / 1000000000000) (-38033509665 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1209489768226721 / 4000000000000) 4 (IntervalRat.scale (821 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (45883880411 / 1000000000000) (45883880541 / 1000000000000), orderedInterval (211559113 / 1000000000000) (211559244 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (391124140508993 / 800000000000) 4 (IntervalRat.scale (821 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-13990207876 / 1000000000000) (-13990207741 / 1000000000000), orderedInterval (33277019309 / 1000000000000) (33277019444 / 1000000000000)))) (orderedInterval (2482832529 / 1000000000000) (2482832610 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (352926097858147 / 4000000000000) 4 (IntervalRat.scale (821 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (73719539197 / 1000000000000) (73719539198 / 1000000000000), orderedInterval (41780630948 / 1000000000000) (41780630949 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (948009142009159 / 4000000000000) 4 (IntervalRat.scale (821 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-42865608552 / 1000000000000) (-42865544793 / 1000000000000), orderedInterval (29222400867 / 1000000000000) (29222464625 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2574029234596203 / 4000000000000) 4 (IntervalRat.scale (821 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-8268769397 / 1000000000000) (-8268769396 / 1000000000000), orderedInterval (-30340314592 / 1000000000000) (-30340314591 / 1000000000000)))) (orderedInterval (3415675374 / 1000000000000) (3415675814 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1896018284019139 / 4000000000000) 4 (IntervalRat.scale (821 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-14581784117 / 1000000000000) (-14581784116 / 1000000000000), orderedInterval (-33606617575 / 1000000000000) (-33606617574 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3248859646263247 / 4000000000000) 4 (IntervalRat.scale (821 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (17436799715 / 1000000000000) (17436800286 / 1000000000000), orderedInterval (-21914274897 / 1000000000000) (-21914274326 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2393095310936173 / 4000000000000) 4 (IntervalRat.scale (821 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (27184932350 / 1000000000000) (27184978819 / 1000000000000), orderedInterval (-18052504252 / 1000000000000) (-18052457783 / 1000000000000)))) (orderedInterval (-5259480430 / 1000000000000) (-5259474835 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate539_chunkChecks4_1 :
    compactCertificate539.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3671623619054179 / 4000000000000) 4 (IntervalRat.scale (821 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (25673506187 / 1000000000000) (25673506636 / 1000000000000), orderedInterval (5853523470 / 1000000000000) (5853523919 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2119812884823691 / 4000000000000) 4 (IntervalRat.scale (821 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (6572112561 / 1000000000000) (6572112566 / 1000000000000), orderedInterval (-34036822762 / 1000000000000) (-34036822757 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3761645163282119 / 4000000000000) 4 (IntervalRat.scale (821 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-24935348556 / 1000000000000) (-24935251780 / 1000000000000), orderedInterval (7442175474 / 1000000000000) (7442272249 / 1000000000000)))) (orderedInterval (-210348125816 / 1000000000000) (-210347740572 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3514616859315011 / 4000000000000) 4 (IntervalRat.scale (821 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-5518266315 / 1000000000000) (-5518266314 / 1000000000000), orderedInterval (26348698500 / 1000000000000) (26348698501 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2508196430371763 / 4000000000000) 4 (IntervalRat.scale (821 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-14833014207 / 1000000000000) (-14833014039 / 1000000000000), orderedInterval (28211914377 / 1000000000000) (28211914545 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2844027426027477 / 4000000000000) 4 (IntervalRat.scale (821 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (29192838983 / 1000000000000) (29192857654 / 1000000000000), orderedInterval (-6589801498 / 1000000000000) (-6589782827 / 1000000000000)))) (orderedInterval (-6850661374 / 1000000000000) (-6850660048 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2371053563057413 / 4000000000000) 4 (IntervalRat.scale (821 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (6909567359 / 1000000000000) (6909567363 / 1000000000000), orderedInterval (-32040880107 / 1000000000000) (-32040880103 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2094897729801673 / 4000000000000) 4 (IntervalRat.scale (821 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (4740192173 / 1000000000000) (4740192175 / 1000000000000), orderedInterval (-34545712416 / 1000000000000) (-34545712414 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (607183014657627 / 800000000000) 4 (IntervalRat.scale (821 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-13921102246 / 1000000000000) (-13921102162 / 1000000000000), orderedInterval (25405779001 / 1000000000000) (25405779085 / 1000000000000)))) (orderedInterval (-4502467943 / 1000000000000) (-4502467711 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate539_chunkChecks4_2 :
    compactCertificate539.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1679500172834369 / 4000000000000) 4 (IntervalRat.scale (821 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-11999810787 / 1000000000000) (-11999810721 / 1000000000000), orderedInterval (37057748936 / 1000000000000) (37057749003 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1423730896466809 / 4000000000000) 4 (IntervalRat.scale (821 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-41835623566 / 1000000000000) (-41835622277 / 1000000000000), orderedInterval (6253504329 / 1000000000000) (6253505618 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (890904689063827 / 4000000000000) 4 (IntervalRat.scale (821 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-23635651295 / 1000000000000) (-23635651294 / 1000000000000), orderedInterval (-47901787401 / 1000000000000) (-47901787400 / 1000000000000)))) (orderedInterval (3338460985 / 1000000000000) (3338461125 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (479131504793709 / 4000000000000) 4 (IntervalRat.scale (821 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (67590658249 / 1000000000000) (67590658250 / 1000000000000), orderedInterval (27035457537 / 1000000000000) (27035457538 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1300935239868127 / 4000000000000) 4 (IntervalRat.scale (821 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-28731810438 / 1000000000000) (-28731797830 / 1000000000000), orderedInterval (33687969957 / 1000000000000) (33687982566 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1776315849665279 / 4000000000000) 4 (IntervalRat.scale (821 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-35835271519 / 1000000000000) (-35835257238 / 1000000000000), orderedInterval (12263533907 / 1000000000000) (12263548189 / 1000000000000)))) (orderedInterval (4001407296 / 1000000000000) (4001408963 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (751095310936173 / 4000000000000) 4 (IntervalRat.scale (821 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (3665910468 / 1000000000000) (3665910470 / 1000000000000), orderedInterval (58101572691 / 1000000000000) (58101572692 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3053160739390733 / 4000000000000) 4 (IntervalRat.scale (821 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-17897850855 / 1000000000000) (-17897850854 / 1000000000000), orderedInterval (-22653531731 / 1000000000000) (-22653531730 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2039369878037347 / 4000000000000) 4 (IntervalRat.scale (821 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (35087236389 / 1000000000000) (35087238663 / 1000000000000), orderedInterval (-4223077879 / 1000000000000) (-4223075605 / 1000000000000)))) (orderedInterval (1816912468 / 1000000000000) (1816914072 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate539_chunkChecks4 :
    compactCertificate539.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate539.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate539_chunkChecks4_0
    compactCertificate539_chunkChecks4_1 compactCertificate539_chunkChecks4_2

theorem compactCertificate539_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate539.chunkCheck r b = true :=
  compactCertificate539.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate539_chunkChecks0
    · exact compactCertificate539_chunkChecks1
    · exact compactCertificate539_chunkChecks2
    · exact compactCertificate539_chunkChecks3
    · exact compactCertificate539_chunkChecks4)

theorem compactCertificate539_coefficient0 :
    compactCertificate539.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate539_coefficient1 :
    compactCertificate539.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate539_coefficient2 :
    compactCertificate539.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate539_coefficient3 :
    compactCertificate539.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate539_coefficient4 :
    compactCertificate539.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate539_coefficients : ∀ r : Fin 5,
    compactCertificate539.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate539_coefficient0
  · exact compactCertificate539_coefficient1
  · exact compactCertificate539_coefficient2
  · exact compactCertificate539_coefficient3
  · exact compactCertificate539_coefficient4

theorem compactCertificate539_lower : (1 : ℚ) ≤ compactCertificate539.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate539, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate539_proves {t : ℝ} (ht : t ∈ compactCertificate539.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate539.proves compactCertificate539_states compactCertificate539_chunks
    compactCertificate539_coefficients compactCertificate539_lower ht

end Erdos232
