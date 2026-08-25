/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate581 : CompactCertificate where
  left := 452
  right := 453
  center := 905 / 2
  grid := fun i =>
    match i.val with
    | 0 => 144
    | 1 => 106
    | 2 => 172
    | 3 => 31
    | 4 => 83
    | 5 => 226
    | 6 => 166
    | 7 => 285
    | 8 => 210
    | 9 => 322
    | 10 => 186
    | 11 => 330
    | 12 => 308
    | 13 => 220
    | 14 => 250
    | 15 => 208
    | 16 => 184
    | 17 => 266
    | 18 => 147
    | 19 => 125
    | 20 => 78
    | 21 => 42
    | 22 => 114
    | 23 => 156
    | 24 => 66
    | 25 => 268
    | _ => 179
  point := fun i =>
    match i.val with
    | 0 => 905 / 2
    | 1 => 266647561570081 / 800000000000
    | 2 => 86228342791873 / 160000000000
    | 3 => 77807093437667 / 800000000000
    | 4 => 209000797446599 / 800000000000
    | 5 => 567477821512683 / 800000000000
    | 6 => 418001594893379 / 800000000000
    | 7 => 716252857458767 / 800000000000
    | 8 => 527588613007853 / 800000000000
    | 9 => 809456607854819 / 800000000000
    | 10 => 467339990442251 / 800000000000
    | 11 => 829303014073159 / 800000000000
    | 12 => 774842450104771 / 800000000000
    | 13 => 552964133857843 / 800000000000
    | 14 => 627002392339797 / 800000000000
    | 15 => 522729226447493 / 800000000000
    | 16 => 461847124353353 / 800000000000
    | 17 => 133861297993947 / 160000000000
    | 18 => 370267394985409 / 800000000000
    | 19 => 313879771328249 / 800000000000
    | 20 => 196411386992147 / 800000000000
    | 21 => 105630697159149 / 800000000000
    | 22 => 286807890884447 / 800000000000
    | 23 => 391611655041919 / 800000000000
    | 24 => 165588613007853 / 800000000000
    | 25 => 673108518672013 / 800000000000
    | _ => 449605295888867 / 800000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (29282822811 / 1000000000000) (29282822812 / 1000000000000), orderedInterval (23407153236 / 1000000000000) (23407153237 / 1000000000000))
    | 1 => (orderedInterval (38660468414 / 1000000000000) (38660468415 / 1000000000000), orderedInterval (20322464656 / 1000000000000) (20322464657 / 1000000000000))
    | 2 => (orderedInterval (-20570237344 / 1000000000000) (-20570235302 / 1000000000000), orderedInterval (27553388261 / 1000000000000) (27553390303 / 1000000000000))
    | 3 => (orderedInterval (-49194324424 / 1000000000000) (-49194324423 / 1000000000000), orderedInterval (-63977647672 / 1000000000000) (-63977647671 / 1000000000000))
    | 4 => (orderedInterval (-47343943063 / 1000000000000) (-47343943061 / 1000000000000), orderedInterval (-13886518205 / 1000000000000) (-13886518203 / 1000000000000))
    | 5 => (orderedInterval (3959565565 / 1000000000000) (3959565566 / 1000000000000), orderedInterval (29692237118 / 1000000000000) (29692237119 / 1000000000000))
    | 6 => (orderedInterval (34124378711 / 1000000000000) (34124385326 / 1000000000000), orderedInterval (-7376528621 / 1000000000000) (-7376522006 / 1000000000000))
    | 7 => (orderedInterval (-18126007971 / 1000000000000) (-18126007970 / 1000000000000), orderedInterval (-19547580154 / 1000000000000) (-19547580153 / 1000000000000))
    | 8 => (orderedInterval (15881161744 / 1000000000000) (15881161745 / 1000000000000), orderedInterval (26692198320 / 1000000000000) (26692198321 / 1000000000000))
    | 9 => (orderedInterval (21284093771 / 1000000000000) (21284093778 / 1000000000000), orderedInterval (13262374851 / 1000000000000) (13262374858 / 1000000000000))
    | 10 => (orderedInterval (19286658893 / 1000000000000) (19286658894 / 1000000000000), orderedInterval (26775295783 / 1000000000000) (26775295784 / 1000000000000))
    | 11 => (orderedInterval (15745105225 / 1000000000000) (15745105226 / 1000000000000), orderedInterval (19129197439 / 1000000000000) (19129197440 / 1000000000000))
    | 12 => (orderedInterval (25322323558 / 1000000000000) (25322358089 / 1000000000000), orderedInterval (-4021638447 / 1000000000000) (-4021603916 / 1000000000000))
    | 13 => (orderedInterval (22598781843 / 1000000000000) (22598781844 / 1000000000000), orderedInterval (20240100932 / 1000000000000) (20240100933 / 1000000000000))
    | 14 => (orderedInterval (-21597570154 / 1000000000000) (-21597564490 / 1000000000000), orderedInterval (18609903809 / 1000000000000) (18609909474 / 1000000000000))
    | 15 => (orderedInterval (21172809649 / 1000000000000) (21172809650 / 1000000000000), orderedInterval (22918783677 / 1000000000000) (22918783678 / 1000000000000))
    | 16 => (orderedInterval (1362413180 / 1000000000000) (1362413181 / 1000000000000), orderedInterval (33178347423 / 1000000000000) (33178347424 / 1000000000000))
    | 17 => (orderedInterval (27119722765 / 1000000000000) (27119746675 / 1000000000000), orderedInterval (-5061067250 / 1000000000000) (-5061043340 / 1000000000000))
    | 18 => (orderedInterval (-36072795607 / 1000000000000) (-36072789500 / 1000000000000), orderedInterval (8654884872 / 1000000000000) (8654890979 / 1000000000000))
    | 19 => (orderedInterval (-17000954679 / 1000000000000) (-17000954678 / 1000000000000), orderedInterval (-36496150242 / 1000000000000) (-36496150241 / 1000000000000))
    | 20 => (orderedInterval (48401760558 / 1000000000000) (48401760560 / 1000000000000), orderedInterval (15721377393 / 1000000000000) (15721377394 / 1000000000000))
    | 21 => (orderedInterval (53337044900 / 1000000000000) (53337044901 / 1000000000000), orderedInterval (44257322348 / 1000000000000) (44257322349 / 1000000000000))
    | 22 => (orderedInterval (38520868076 / 1000000000000) (38520868078 / 1000000000000), orderedInterval (17030774674 / 1000000000000) (17030774676 / 1000000000000))
    | 23 => (orderedInterval (7561959600 / 1000000000000) (7561959601 / 1000000000000), orderedInterval (35253158040 / 1000000000000) (35253158041 / 1000000000000))
    | 24 => (orderedInterval (22889249235 / 1000000000000) (22889249236 / 1000000000000), orderedInterval (50459632139 / 1000000000000) (50459632140 / 1000000000000))
    | 25 => (orderedInterval (6111950293 / 1000000000000) (6111950294 / 1000000000000), orderedInterval (26815703087 / 1000000000000) (26815703088 / 1000000000000))
    | _ => (orderedInterval (-14539661059 / 1000000000000) (-14539661058 / 1000000000000), orderedInterval (-30340986674 / 1000000000000) (-30340986673 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (10759841430 / 1000000000000) (10759841582 / 1000000000000)
      | 1 => orderedInterval (-1476370604 / 1000000000000) (-1476370550 / 1000000000000)
      | 2 => orderedInterval (942894941 / 1000000000000) (942894967 / 1000000000000)
      | 3 => orderedInterval (-114684378 / 1000000000000) (-114684197 / 1000000000000)
      | 4 => orderedInterval (1789154960 / 1000000000000) (1789155667 / 1000000000000)
      | 5 => orderedInterval (860902244 / 1000000000000) (860902900 / 1000000000000)
      | 6 => orderedInterval (8305752065 / 1000000000000) (8305753155 / 1000000000000)
      | 7 => orderedInterval (-2438332459 / 1000000000000) (-2438332404 / 1000000000000)
      | _ => orderedInterval (2368486333 / 1000000000000) (2368486458 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (11342946234 / 1000000000000) (11342946413 / 1000000000000)
      | 1 => orderedInterval (-3452483687 / 1000000000000) (-3452483625 / 1000000000000)
      | 2 => orderedInterval (2133130940 / 1000000000000) (2133130985 / 1000000000000)
      | 3 => orderedInterval (3521362988 / 1000000000000) (3521363363 / 1000000000000)
      | 4 => orderedInterval (2915907656 / 1000000000000) (2915909128 / 1000000000000)
      | 5 => orderedInterval (-2279804247 / 1000000000000) (-2279803052 / 1000000000000)
      | 6 => orderedInterval (653332031 / 1000000000000) (653333135 / 1000000000000)
      | 7 => orderedInterval (-3467348311 / 1000000000000) (-3467348261 / 1000000000000)
      | _ => orderedInterval (3150770903 / 1000000000000) (3150771079 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-10114985265 / 1000000000000) (-10114985054 / 1000000000000)
      | 1 => orderedInterval (1250902890 / 1000000000000) (1250902976 / 1000000000000)
      | 2 => orderedInterval (-3008687297 / 1000000000000) (-3008687218 / 1000000000000)
      | 3 => orderedInterval (4773406598 / 1000000000000) (4773407401 / 1000000000000)
      | 4 => orderedInterval (-3226254524 / 1000000000000) (-3226251433 / 1000000000000)
      | 5 => orderedInterval (-2751563933 / 1000000000000) (-2751561744 / 1000000000000)
      | 6 => orderedInterval (-7222975927 / 1000000000000) (-7222974803 / 1000000000000)
      | 7 => orderedInterval (1318325791 / 1000000000000) (1318325840 / 1000000000000)
      | _ => orderedInterval (-2523862342 / 1000000000000) (-2523862082 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-12062591352 / 1000000000000) (-12062591102 / 1000000000000)
      | 1 => orderedInterval (8219394053 / 1000000000000) (8219394182 / 1000000000000)
      | 2 => orderedInterval (-6660594879 / 1000000000000) (-6660594736 / 1000000000000)
      | 3 => orderedInterval (-10626438377 / 1000000000000) (-10626436616 / 1000000000000)
      | 4 => orderedInterval (-7037272887 / 1000000000000) (-7037266372 / 1000000000000)
      | 5 => orderedInterval (3971176881 / 1000000000000) (3971180899 / 1000000000000)
      | 6 => orderedInterval (68496627 / 1000000000000) (68497771 / 1000000000000)
      | 7 => orderedInterval (3630020007 / 1000000000000) (3630020058 / 1000000000000)
      | _ => orderedInterval (3102868482 / 1000000000000) (3102868884 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (9337245998 / 1000000000000) (9337246296 / 1000000000000)
      | 1 => orderedInterval (-1927119261 / 1000000000000) (-1927119064 / 1000000000000)
      | 2 => orderedInterval (10329602438 / 1000000000000) (10329602702 / 1000000000000)
      | 3 => orderedInterval (-28882338077 / 1000000000000) (-28882334165 / 1000000000000)
      | 4 => orderedInterval (3053899233 / 1000000000000) (3053913030 / 1000000000000)
      | 5 => orderedInterval (8953326443 / 1000000000000) (8953333842 / 1000000000000)
      | 6 => orderedInterval (6993098235 / 1000000000000) (6993099405 / 1000000000000)
      | 7 => orderedInterval (-1161256203 / 1000000000000) (-1161256150 / 1000000000000)
      | _ => orderedInterval (536438238 / 1000000000000) (536438883 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (20997644532 / 1000000000000) (20997647578 / 1000000000000)
    | 1 => orderedInterval (14517814507 / 1000000000000) (14517819165 / 1000000000000)
    | 2 => orderedInterval (-21505694009 / 1000000000000) (-21505686117 / 1000000000000)
    | 3 => orderedInterval (-17394941445 / 1000000000000) (-17394927032 / 1000000000000)
    | _ => orderedInterval (7232897044 / 1000000000000) (7232924779 / 1000000000000)

theorem compactCertificate581_stateChecks0 :
    compactCertificate581.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 144 12 (905 / 2)) (orderedInterval (29282822811 / 1000000000000) (29282822812 / 1000000000000), orderedInterval (23407153236 / 1000000000000) (23407153237 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 106 12 (266647561570081 / 800000000000)) (orderedInterval (38660468414 / 1000000000000) (38660468415 / 1000000000000), orderedInterval (20322464656 / 1000000000000) (20322464657 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 172 12 (86228342791873 / 160000000000)) (orderedInterval (-20570237344 / 1000000000000) (-20570235302 / 1000000000000), orderedInterval (27553388261 / 1000000000000) (27553390303 / 1000000000000))) = true
  rfl'

theorem compactCertificate581_stateChecks1 :
    compactCertificate581.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 31 12 (77807093437667 / 800000000000)) (orderedInterval (-49194324424 / 1000000000000) (-49194324423 / 1000000000000), orderedInterval (-63977647672 / 1000000000000) (-63977647671 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 83 12 (209000797446599 / 800000000000)) (orderedInterval (-47343943063 / 1000000000000) (-47343943061 / 1000000000000), orderedInterval (-13886518205 / 1000000000000) (-13886518203 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 226 12 (567477821512683 / 800000000000)) (orderedInterval (3959565565 / 1000000000000) (3959565566 / 1000000000000), orderedInterval (29692237118 / 1000000000000) (29692237119 / 1000000000000))) = true
  rfl'

theorem compactCertificate581_stateChecks2 :
    compactCertificate581.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 166 12 (418001594893379 / 800000000000)) (orderedInterval (34124378711 / 1000000000000) (34124385326 / 1000000000000), orderedInterval (-7376528621 / 1000000000000) (-7376522006 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 285 12 (716252857458767 / 800000000000)) (orderedInterval (-18126007971 / 1000000000000) (-18126007970 / 1000000000000), orderedInterval (-19547580154 / 1000000000000) (-19547580153 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 210 12 (527588613007853 / 800000000000)) (orderedInterval (15881161744 / 1000000000000) (15881161745 / 1000000000000), orderedInterval (26692198320 / 1000000000000) (26692198321 / 1000000000000))) = true
  rfl'

theorem compactCertificate581_stateChecks3 :
    compactCertificate581.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 322 12 (809456607854819 / 800000000000)) (orderedInterval (21284093771 / 1000000000000) (21284093778 / 1000000000000), orderedInterval (13262374851 / 1000000000000) (13262374858 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 186 12 (467339990442251 / 800000000000)) (orderedInterval (19286658893 / 1000000000000) (19286658894 / 1000000000000), orderedInterval (26775295783 / 1000000000000) (26775295784 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 330 12 (829303014073159 / 800000000000)) (orderedInterval (15745105225 / 1000000000000) (15745105226 / 1000000000000), orderedInterval (19129197439 / 1000000000000) (19129197440 / 1000000000000))) = true
  rfl'

theorem compactCertificate581_stateChecks4 :
    compactCertificate581.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 308 12 (774842450104771 / 800000000000)) (orderedInterval (25322323558 / 1000000000000) (25322358089 / 1000000000000), orderedInterval (-4021638447 / 1000000000000) (-4021603916 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 220 12 (552964133857843 / 800000000000)) (orderedInterval (22598781843 / 1000000000000) (22598781844 / 1000000000000), orderedInterval (20240100932 / 1000000000000) (20240100933 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 250 12 (627002392339797 / 800000000000)) (orderedInterval (-21597570154 / 1000000000000) (-21597564490 / 1000000000000), orderedInterval (18609903809 / 1000000000000) (18609909474 / 1000000000000))) = true
  rfl'

theorem compactCertificate581_stateChecks5 :
    compactCertificate581.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 208 12 (522729226447493 / 800000000000)) (orderedInterval (21172809649 / 1000000000000) (21172809650 / 1000000000000), orderedInterval (22918783677 / 1000000000000) (22918783678 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 184 12 (461847124353353 / 800000000000)) (orderedInterval (1362413180 / 1000000000000) (1362413181 / 1000000000000), orderedInterval (33178347423 / 1000000000000) (33178347424 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 266 12 (133861297993947 / 160000000000)) (orderedInterval (27119722765 / 1000000000000) (27119746675 / 1000000000000), orderedInterval (-5061067250 / 1000000000000) (-5061043340 / 1000000000000))) = true
  rfl'

theorem compactCertificate581_stateChecks6 :
    compactCertificate581.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 147 12 (370267394985409 / 800000000000)) (orderedInterval (-36072795607 / 1000000000000) (-36072789500 / 1000000000000), orderedInterval (8654884872 / 1000000000000) (8654890979 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 125 12 (313879771328249 / 800000000000)) (orderedInterval (-17000954679 / 1000000000000) (-17000954678 / 1000000000000), orderedInterval (-36496150242 / 1000000000000) (-36496150241 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 78 12 (196411386992147 / 800000000000)) (orderedInterval (48401760558 / 1000000000000) (48401760560 / 1000000000000), orderedInterval (15721377393 / 1000000000000) (15721377394 / 1000000000000))) = true
  rfl'

theorem compactCertificate581_stateChecks7 :
    compactCertificate581.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 42 12 (105630697159149 / 800000000000)) (orderedInterval (53337044900 / 1000000000000) (53337044901 / 1000000000000), orderedInterval (44257322348 / 1000000000000) (44257322349 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 114 12 (286807890884447 / 800000000000)) (orderedInterval (38520868076 / 1000000000000) (38520868078 / 1000000000000), orderedInterval (17030774674 / 1000000000000) (17030774676 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 156 12 (391611655041919 / 800000000000)) (orderedInterval (7561959600 / 1000000000000) (7561959601 / 1000000000000), orderedInterval (35253158040 / 1000000000000) (35253158041 / 1000000000000))) = true
  rfl'

theorem compactCertificate581_stateChecks8 :
    compactCertificate581.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (165588613007853 / 800000000000)) (orderedInterval (22889249235 / 1000000000000) (22889249236 / 1000000000000), orderedInterval (50459632139 / 1000000000000) (50459632140 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 268 12 (673108518672013 / 800000000000)) (orderedInterval (6111950293 / 1000000000000) (6111950294 / 1000000000000), orderedInterval (26815703087 / 1000000000000) (26815703088 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 179 12 (449605295888867 / 800000000000)) (orderedInterval (-14539661059 / 1000000000000) (-14539661058 / 1000000000000), orderedInterval (-30340986674 / 1000000000000) (-30340986673 / 1000000000000))) = true
  rfl'

theorem compactCertificate581_states : ∀ j,
    BesselStateValid (compactCertificate581.point j) (compactCertificate581.state j) :=
  compactCertificate581.statesValid_of_checks3 compactCertificate581_stateChecks0
    compactCertificate581_stateChecks1 compactCertificate581_stateChecks2
    compactCertificate581_stateChecks3 compactCertificate581_stateChecks4
    compactCertificate581_stateChecks5 compactCertificate581_stateChecks6
    compactCertificate581_stateChecks7 compactCertificate581_stateChecks8

theorem compactCertificate581_chunkChecks0_0 :
    compactCertificate581.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (905 / 2) 0 (IntervalRat.scale (905 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (29282822811 / 1000000000000) (29282822812 / 1000000000000), orderedInterval (23407153236 / 1000000000000) (23407153237 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (266647561570081 / 800000000000) 0 (IntervalRat.scale (905 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (38660468414 / 1000000000000) (38660468415 / 1000000000000), orderedInterval (20322464656 / 1000000000000) (20322464657 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (86228342791873 / 160000000000) 0 (IntervalRat.scale (905 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-20570237344 / 1000000000000) (-20570235302 / 1000000000000), orderedInterval (27553388261 / 1000000000000) (27553390303 / 1000000000000)))) (orderedInterval (10759841430 / 1000000000000) (10759841582 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (77807093437667 / 800000000000) 0 (IntervalRat.scale (905 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-49194324424 / 1000000000000) (-49194324423 / 1000000000000), orderedInterval (-63977647672 / 1000000000000) (-63977647671 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (209000797446599 / 800000000000) 0 (IntervalRat.scale (905 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-47343943063 / 1000000000000) (-47343943061 / 1000000000000), orderedInterval (-13886518205 / 1000000000000) (-13886518203 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (567477821512683 / 800000000000) 0 (IntervalRat.scale (905 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (3959565565 / 1000000000000) (3959565566 / 1000000000000), orderedInterval (29692237118 / 1000000000000) (29692237119 / 1000000000000)))) (orderedInterval (-1476370604 / 1000000000000) (-1476370550 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (418001594893379 / 800000000000) 0 (IntervalRat.scale (905 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (34124378711 / 1000000000000) (34124385326 / 1000000000000), orderedInterval (-7376528621 / 1000000000000) (-7376522006 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (716252857458767 / 800000000000) 0 (IntervalRat.scale (905 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-18126007971 / 1000000000000) (-18126007970 / 1000000000000), orderedInterval (-19547580154 / 1000000000000) (-19547580153 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (527588613007853 / 800000000000) 0 (IntervalRat.scale (905 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (15881161744 / 1000000000000) (15881161745 / 1000000000000), orderedInterval (26692198320 / 1000000000000) (26692198321 / 1000000000000)))) (orderedInterval (942894941 / 1000000000000) (942894967 / 1000000000000))) = true
  rfl'

theorem compactCertificate581_chunkChecks0_1 :
    compactCertificate581.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (809456607854819 / 800000000000) 0 (IntervalRat.scale (905 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (21284093771 / 1000000000000) (21284093778 / 1000000000000), orderedInterval (13262374851 / 1000000000000) (13262374858 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (467339990442251 / 800000000000) 0 (IntervalRat.scale (905 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (19286658893 / 1000000000000) (19286658894 / 1000000000000), orderedInterval (26775295783 / 1000000000000) (26775295784 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (829303014073159 / 800000000000) 0 (IntervalRat.scale (905 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (15745105225 / 1000000000000) (15745105226 / 1000000000000), orderedInterval (19129197439 / 1000000000000) (19129197440 / 1000000000000)))) (orderedInterval (-114684378 / 1000000000000) (-114684197 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (774842450104771 / 800000000000) 0 (IntervalRat.scale (905 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (25322323558 / 1000000000000) (25322358089 / 1000000000000), orderedInterval (-4021638447 / 1000000000000) (-4021603916 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (552964133857843 / 800000000000) 0 (IntervalRat.scale (905 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (22598781843 / 1000000000000) (22598781844 / 1000000000000), orderedInterval (20240100932 / 1000000000000) (20240100933 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (627002392339797 / 800000000000) 0 (IntervalRat.scale (905 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-21597570154 / 1000000000000) (-21597564490 / 1000000000000), orderedInterval (18609903809 / 1000000000000) (18609909474 / 1000000000000)))) (orderedInterval (1789154960 / 1000000000000) (1789155667 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (522729226447493 / 800000000000) 0 (IntervalRat.scale (905 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (21172809649 / 1000000000000) (21172809650 / 1000000000000), orderedInterval (22918783677 / 1000000000000) (22918783678 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (461847124353353 / 800000000000) 0 (IntervalRat.scale (905 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (1362413180 / 1000000000000) (1362413181 / 1000000000000), orderedInterval (33178347423 / 1000000000000) (33178347424 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (133861297993947 / 160000000000) 0 (IntervalRat.scale (905 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (27119722765 / 1000000000000) (27119746675 / 1000000000000), orderedInterval (-5061067250 / 1000000000000) (-5061043340 / 1000000000000)))) (orderedInterval (860902244 / 1000000000000) (860902900 / 1000000000000))) = true
  rfl'

theorem compactCertificate581_chunkChecks0_2 :
    compactCertificate581.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (370267394985409 / 800000000000) 0 (IntervalRat.scale (905 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-36072795607 / 1000000000000) (-36072789500 / 1000000000000), orderedInterval (8654884872 / 1000000000000) (8654890979 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (313879771328249 / 800000000000) 0 (IntervalRat.scale (905 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-17000954679 / 1000000000000) (-17000954678 / 1000000000000), orderedInterval (-36496150242 / 1000000000000) (-36496150241 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (196411386992147 / 800000000000) 0 (IntervalRat.scale (905 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (48401760558 / 1000000000000) (48401760560 / 1000000000000), orderedInterval (15721377393 / 1000000000000) (15721377394 / 1000000000000)))) (orderedInterval (8305752065 / 1000000000000) (8305753155 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (105630697159149 / 800000000000) 0 (IntervalRat.scale (905 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (53337044900 / 1000000000000) (53337044901 / 1000000000000), orderedInterval (44257322348 / 1000000000000) (44257322349 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (286807890884447 / 800000000000) 0 (IntervalRat.scale (905 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (38520868076 / 1000000000000) (38520868078 / 1000000000000), orderedInterval (17030774674 / 1000000000000) (17030774676 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (391611655041919 / 800000000000) 0 (IntervalRat.scale (905 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (7561959600 / 1000000000000) (7561959601 / 1000000000000), orderedInterval (35253158040 / 1000000000000) (35253158041 / 1000000000000)))) (orderedInterval (-2438332459 / 1000000000000) (-2438332404 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (165588613007853 / 800000000000) 0 (IntervalRat.scale (905 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (22889249235 / 1000000000000) (22889249236 / 1000000000000), orderedInterval (50459632139 / 1000000000000) (50459632140 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (673108518672013 / 800000000000) 0 (IntervalRat.scale (905 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (6111950293 / 1000000000000) (6111950294 / 1000000000000), orderedInterval (26815703087 / 1000000000000) (26815703088 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (449605295888867 / 800000000000) 0 (IntervalRat.scale (905 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-14539661059 / 1000000000000) (-14539661058 / 1000000000000), orderedInterval (-30340986674 / 1000000000000) (-30340986673 / 1000000000000)))) (orderedInterval (2368486333 / 1000000000000) (2368486458 / 1000000000000))) = true
  rfl'

theorem compactCertificate581_chunkChecks0 :
    compactCertificate581.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate581.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate581_chunkChecks0_0
    compactCertificate581_chunkChecks0_1 compactCertificate581_chunkChecks0_2

theorem compactCertificate581_chunkChecks1_0 :
    compactCertificate581.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (905 / 2) 1 (IntervalRat.scale (905 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (29282822811 / 1000000000000) (29282822812 / 1000000000000), orderedInterval (23407153236 / 1000000000000) (23407153237 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (266647561570081 / 800000000000) 1 (IntervalRat.scale (905 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (38660468414 / 1000000000000) (38660468415 / 1000000000000), orderedInterval (20322464656 / 1000000000000) (20322464657 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (86228342791873 / 160000000000) 1 (IntervalRat.scale (905 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-20570237344 / 1000000000000) (-20570235302 / 1000000000000), orderedInterval (27553388261 / 1000000000000) (27553390303 / 1000000000000)))) (orderedInterval (11342946234 / 1000000000000) (11342946413 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (77807093437667 / 800000000000) 1 (IntervalRat.scale (905 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-49194324424 / 1000000000000) (-49194324423 / 1000000000000), orderedInterval (-63977647672 / 1000000000000) (-63977647671 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (209000797446599 / 800000000000) 1 (IntervalRat.scale (905 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-47343943063 / 1000000000000) (-47343943061 / 1000000000000), orderedInterval (-13886518205 / 1000000000000) (-13886518203 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (567477821512683 / 800000000000) 1 (IntervalRat.scale (905 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (3959565565 / 1000000000000) (3959565566 / 1000000000000), orderedInterval (29692237118 / 1000000000000) (29692237119 / 1000000000000)))) (orderedInterval (-3452483687 / 1000000000000) (-3452483625 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (418001594893379 / 800000000000) 1 (IntervalRat.scale (905 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (34124378711 / 1000000000000) (34124385326 / 1000000000000), orderedInterval (-7376528621 / 1000000000000) (-7376522006 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (716252857458767 / 800000000000) 1 (IntervalRat.scale (905 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-18126007971 / 1000000000000) (-18126007970 / 1000000000000), orderedInterval (-19547580154 / 1000000000000) (-19547580153 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (527588613007853 / 800000000000) 1 (IntervalRat.scale (905 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (15881161744 / 1000000000000) (15881161745 / 1000000000000), orderedInterval (26692198320 / 1000000000000) (26692198321 / 1000000000000)))) (orderedInterval (2133130940 / 1000000000000) (2133130985 / 1000000000000))) = true
  rfl'

theorem compactCertificate581_chunkChecks1_1 :
    compactCertificate581.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (809456607854819 / 800000000000) 1 (IntervalRat.scale (905 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (21284093771 / 1000000000000) (21284093778 / 1000000000000), orderedInterval (13262374851 / 1000000000000) (13262374858 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (467339990442251 / 800000000000) 1 (IntervalRat.scale (905 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (19286658893 / 1000000000000) (19286658894 / 1000000000000), orderedInterval (26775295783 / 1000000000000) (26775295784 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (829303014073159 / 800000000000) 1 (IntervalRat.scale (905 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (15745105225 / 1000000000000) (15745105226 / 1000000000000), orderedInterval (19129197439 / 1000000000000) (19129197440 / 1000000000000)))) (orderedInterval (3521362988 / 1000000000000) (3521363363 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (774842450104771 / 800000000000) 1 (IntervalRat.scale (905 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (25322323558 / 1000000000000) (25322358089 / 1000000000000), orderedInterval (-4021638447 / 1000000000000) (-4021603916 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (552964133857843 / 800000000000) 1 (IntervalRat.scale (905 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (22598781843 / 1000000000000) (22598781844 / 1000000000000), orderedInterval (20240100932 / 1000000000000) (20240100933 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (627002392339797 / 800000000000) 1 (IntervalRat.scale (905 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-21597570154 / 1000000000000) (-21597564490 / 1000000000000), orderedInterval (18609903809 / 1000000000000) (18609909474 / 1000000000000)))) (orderedInterval (2915907656 / 1000000000000) (2915909128 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (522729226447493 / 800000000000) 1 (IntervalRat.scale (905 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (21172809649 / 1000000000000) (21172809650 / 1000000000000), orderedInterval (22918783677 / 1000000000000) (22918783678 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (461847124353353 / 800000000000) 1 (IntervalRat.scale (905 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (1362413180 / 1000000000000) (1362413181 / 1000000000000), orderedInterval (33178347423 / 1000000000000) (33178347424 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (133861297993947 / 160000000000) 1 (IntervalRat.scale (905 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (27119722765 / 1000000000000) (27119746675 / 1000000000000), orderedInterval (-5061067250 / 1000000000000) (-5061043340 / 1000000000000)))) (orderedInterval (-2279804247 / 1000000000000) (-2279803052 / 1000000000000))) = true
  rfl'

theorem compactCertificate581_chunkChecks1_2 :
    compactCertificate581.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (370267394985409 / 800000000000) 1 (IntervalRat.scale (905 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-36072795607 / 1000000000000) (-36072789500 / 1000000000000), orderedInterval (8654884872 / 1000000000000) (8654890979 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (313879771328249 / 800000000000) 1 (IntervalRat.scale (905 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-17000954679 / 1000000000000) (-17000954678 / 1000000000000), orderedInterval (-36496150242 / 1000000000000) (-36496150241 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (196411386992147 / 800000000000) 1 (IntervalRat.scale (905 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (48401760558 / 1000000000000) (48401760560 / 1000000000000), orderedInterval (15721377393 / 1000000000000) (15721377394 / 1000000000000)))) (orderedInterval (653332031 / 1000000000000) (653333135 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (105630697159149 / 800000000000) 1 (IntervalRat.scale (905 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (53337044900 / 1000000000000) (53337044901 / 1000000000000), orderedInterval (44257322348 / 1000000000000) (44257322349 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (286807890884447 / 800000000000) 1 (IntervalRat.scale (905 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (38520868076 / 1000000000000) (38520868078 / 1000000000000), orderedInterval (17030774674 / 1000000000000) (17030774676 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (391611655041919 / 800000000000) 1 (IntervalRat.scale (905 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (7561959600 / 1000000000000) (7561959601 / 1000000000000), orderedInterval (35253158040 / 1000000000000) (35253158041 / 1000000000000)))) (orderedInterval (-3467348311 / 1000000000000) (-3467348261 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (165588613007853 / 800000000000) 1 (IntervalRat.scale (905 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (22889249235 / 1000000000000) (22889249236 / 1000000000000), orderedInterval (50459632139 / 1000000000000) (50459632140 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (673108518672013 / 800000000000) 1 (IntervalRat.scale (905 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (6111950293 / 1000000000000) (6111950294 / 1000000000000), orderedInterval (26815703087 / 1000000000000) (26815703088 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (449605295888867 / 800000000000) 1 (IntervalRat.scale (905 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-14539661059 / 1000000000000) (-14539661058 / 1000000000000), orderedInterval (-30340986674 / 1000000000000) (-30340986673 / 1000000000000)))) (orderedInterval (3150770903 / 1000000000000) (3150771079 / 1000000000000))) = true
  rfl'

theorem compactCertificate581_chunkChecks1 :
    compactCertificate581.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate581.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate581_chunkChecks1_0
    compactCertificate581_chunkChecks1_1 compactCertificate581_chunkChecks1_2

theorem compactCertificate581_chunkChecks2_0 :
    compactCertificate581.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (905 / 2) 2 (IntervalRat.scale (905 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (29282822811 / 1000000000000) (29282822812 / 1000000000000), orderedInterval (23407153236 / 1000000000000) (23407153237 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (266647561570081 / 800000000000) 2 (IntervalRat.scale (905 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (38660468414 / 1000000000000) (38660468415 / 1000000000000), orderedInterval (20322464656 / 1000000000000) (20322464657 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (86228342791873 / 160000000000) 2 (IntervalRat.scale (905 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-20570237344 / 1000000000000) (-20570235302 / 1000000000000), orderedInterval (27553388261 / 1000000000000) (27553390303 / 1000000000000)))) (orderedInterval (-10114985265 / 1000000000000) (-10114985054 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (77807093437667 / 800000000000) 2 (IntervalRat.scale (905 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-49194324424 / 1000000000000) (-49194324423 / 1000000000000), orderedInterval (-63977647672 / 1000000000000) (-63977647671 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (209000797446599 / 800000000000) 2 (IntervalRat.scale (905 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-47343943063 / 1000000000000) (-47343943061 / 1000000000000), orderedInterval (-13886518205 / 1000000000000) (-13886518203 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (567477821512683 / 800000000000) 2 (IntervalRat.scale (905 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (3959565565 / 1000000000000) (3959565566 / 1000000000000), orderedInterval (29692237118 / 1000000000000) (29692237119 / 1000000000000)))) (orderedInterval (1250902890 / 1000000000000) (1250902976 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (418001594893379 / 800000000000) 2 (IntervalRat.scale (905 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (34124378711 / 1000000000000) (34124385326 / 1000000000000), orderedInterval (-7376528621 / 1000000000000) (-7376522006 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (716252857458767 / 800000000000) 2 (IntervalRat.scale (905 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-18126007971 / 1000000000000) (-18126007970 / 1000000000000), orderedInterval (-19547580154 / 1000000000000) (-19547580153 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (527588613007853 / 800000000000) 2 (IntervalRat.scale (905 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (15881161744 / 1000000000000) (15881161745 / 1000000000000), orderedInterval (26692198320 / 1000000000000) (26692198321 / 1000000000000)))) (orderedInterval (-3008687297 / 1000000000000) (-3008687218 / 1000000000000))) = true
  rfl'

theorem compactCertificate581_chunkChecks2_1 :
    compactCertificate581.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (809456607854819 / 800000000000) 2 (IntervalRat.scale (905 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (21284093771 / 1000000000000) (21284093778 / 1000000000000), orderedInterval (13262374851 / 1000000000000) (13262374858 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (467339990442251 / 800000000000) 2 (IntervalRat.scale (905 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (19286658893 / 1000000000000) (19286658894 / 1000000000000), orderedInterval (26775295783 / 1000000000000) (26775295784 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (829303014073159 / 800000000000) 2 (IntervalRat.scale (905 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (15745105225 / 1000000000000) (15745105226 / 1000000000000), orderedInterval (19129197439 / 1000000000000) (19129197440 / 1000000000000)))) (orderedInterval (4773406598 / 1000000000000) (4773407401 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (774842450104771 / 800000000000) 2 (IntervalRat.scale (905 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (25322323558 / 1000000000000) (25322358089 / 1000000000000), orderedInterval (-4021638447 / 1000000000000) (-4021603916 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (552964133857843 / 800000000000) 2 (IntervalRat.scale (905 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (22598781843 / 1000000000000) (22598781844 / 1000000000000), orderedInterval (20240100932 / 1000000000000) (20240100933 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (627002392339797 / 800000000000) 2 (IntervalRat.scale (905 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-21597570154 / 1000000000000) (-21597564490 / 1000000000000), orderedInterval (18609903809 / 1000000000000) (18609909474 / 1000000000000)))) (orderedInterval (-3226254524 / 1000000000000) (-3226251433 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (522729226447493 / 800000000000) 2 (IntervalRat.scale (905 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (21172809649 / 1000000000000) (21172809650 / 1000000000000), orderedInterval (22918783677 / 1000000000000) (22918783678 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (461847124353353 / 800000000000) 2 (IntervalRat.scale (905 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (1362413180 / 1000000000000) (1362413181 / 1000000000000), orderedInterval (33178347423 / 1000000000000) (33178347424 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (133861297993947 / 160000000000) 2 (IntervalRat.scale (905 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (27119722765 / 1000000000000) (27119746675 / 1000000000000), orderedInterval (-5061067250 / 1000000000000) (-5061043340 / 1000000000000)))) (orderedInterval (-2751563933 / 1000000000000) (-2751561744 / 1000000000000))) = true
  rfl'

theorem compactCertificate581_chunkChecks2_2 :
    compactCertificate581.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (370267394985409 / 800000000000) 2 (IntervalRat.scale (905 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-36072795607 / 1000000000000) (-36072789500 / 1000000000000), orderedInterval (8654884872 / 1000000000000) (8654890979 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (313879771328249 / 800000000000) 2 (IntervalRat.scale (905 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-17000954679 / 1000000000000) (-17000954678 / 1000000000000), orderedInterval (-36496150242 / 1000000000000) (-36496150241 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (196411386992147 / 800000000000) 2 (IntervalRat.scale (905 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (48401760558 / 1000000000000) (48401760560 / 1000000000000), orderedInterval (15721377393 / 1000000000000) (15721377394 / 1000000000000)))) (orderedInterval (-7222975927 / 1000000000000) (-7222974803 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (105630697159149 / 800000000000) 2 (IntervalRat.scale (905 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (53337044900 / 1000000000000) (53337044901 / 1000000000000), orderedInterval (44257322348 / 1000000000000) (44257322349 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (286807890884447 / 800000000000) 2 (IntervalRat.scale (905 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (38520868076 / 1000000000000) (38520868078 / 1000000000000), orderedInterval (17030774674 / 1000000000000) (17030774676 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (391611655041919 / 800000000000) 2 (IntervalRat.scale (905 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (7561959600 / 1000000000000) (7561959601 / 1000000000000), orderedInterval (35253158040 / 1000000000000) (35253158041 / 1000000000000)))) (orderedInterval (1318325791 / 1000000000000) (1318325840 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (165588613007853 / 800000000000) 2 (IntervalRat.scale (905 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (22889249235 / 1000000000000) (22889249236 / 1000000000000), orderedInterval (50459632139 / 1000000000000) (50459632140 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (673108518672013 / 800000000000) 2 (IntervalRat.scale (905 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (6111950293 / 1000000000000) (6111950294 / 1000000000000), orderedInterval (26815703087 / 1000000000000) (26815703088 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (449605295888867 / 800000000000) 2 (IntervalRat.scale (905 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-14539661059 / 1000000000000) (-14539661058 / 1000000000000), orderedInterval (-30340986674 / 1000000000000) (-30340986673 / 1000000000000)))) (orderedInterval (-2523862342 / 1000000000000) (-2523862082 / 1000000000000))) = true
  rfl'

theorem compactCertificate581_chunkChecks2 :
    compactCertificate581.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate581.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate581_chunkChecks2_0
    compactCertificate581_chunkChecks2_1 compactCertificate581_chunkChecks2_2

theorem compactCertificate581_chunkChecks3_0 :
    compactCertificate581.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (905 / 2) 3 (IntervalRat.scale (905 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (29282822811 / 1000000000000) (29282822812 / 1000000000000), orderedInterval (23407153236 / 1000000000000) (23407153237 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (266647561570081 / 800000000000) 3 (IntervalRat.scale (905 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (38660468414 / 1000000000000) (38660468415 / 1000000000000), orderedInterval (20322464656 / 1000000000000) (20322464657 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (86228342791873 / 160000000000) 3 (IntervalRat.scale (905 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-20570237344 / 1000000000000) (-20570235302 / 1000000000000), orderedInterval (27553388261 / 1000000000000) (27553390303 / 1000000000000)))) (orderedInterval (-12062591352 / 1000000000000) (-12062591102 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (77807093437667 / 800000000000) 3 (IntervalRat.scale (905 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-49194324424 / 1000000000000) (-49194324423 / 1000000000000), orderedInterval (-63977647672 / 1000000000000) (-63977647671 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (209000797446599 / 800000000000) 3 (IntervalRat.scale (905 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-47343943063 / 1000000000000) (-47343943061 / 1000000000000), orderedInterval (-13886518205 / 1000000000000) (-13886518203 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (567477821512683 / 800000000000) 3 (IntervalRat.scale (905 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (3959565565 / 1000000000000) (3959565566 / 1000000000000), orderedInterval (29692237118 / 1000000000000) (29692237119 / 1000000000000)))) (orderedInterval (8219394053 / 1000000000000) (8219394182 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (418001594893379 / 800000000000) 3 (IntervalRat.scale (905 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (34124378711 / 1000000000000) (34124385326 / 1000000000000), orderedInterval (-7376528621 / 1000000000000) (-7376522006 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (716252857458767 / 800000000000) 3 (IntervalRat.scale (905 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-18126007971 / 1000000000000) (-18126007970 / 1000000000000), orderedInterval (-19547580154 / 1000000000000) (-19547580153 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (527588613007853 / 800000000000) 3 (IntervalRat.scale (905 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (15881161744 / 1000000000000) (15881161745 / 1000000000000), orderedInterval (26692198320 / 1000000000000) (26692198321 / 1000000000000)))) (orderedInterval (-6660594879 / 1000000000000) (-6660594736 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate581_chunkChecks3_1 :
    compactCertificate581.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (809456607854819 / 800000000000) 3 (IntervalRat.scale (905 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (21284093771 / 1000000000000) (21284093778 / 1000000000000), orderedInterval (13262374851 / 1000000000000) (13262374858 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (467339990442251 / 800000000000) 3 (IntervalRat.scale (905 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (19286658893 / 1000000000000) (19286658894 / 1000000000000), orderedInterval (26775295783 / 1000000000000) (26775295784 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (829303014073159 / 800000000000) 3 (IntervalRat.scale (905 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (15745105225 / 1000000000000) (15745105226 / 1000000000000), orderedInterval (19129197439 / 1000000000000) (19129197440 / 1000000000000)))) (orderedInterval (-10626438377 / 1000000000000) (-10626436616 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (774842450104771 / 800000000000) 3 (IntervalRat.scale (905 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (25322323558 / 1000000000000) (25322358089 / 1000000000000), orderedInterval (-4021638447 / 1000000000000) (-4021603916 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (552964133857843 / 800000000000) 3 (IntervalRat.scale (905 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (22598781843 / 1000000000000) (22598781844 / 1000000000000), orderedInterval (20240100932 / 1000000000000) (20240100933 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (627002392339797 / 800000000000) 3 (IntervalRat.scale (905 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-21597570154 / 1000000000000) (-21597564490 / 1000000000000), orderedInterval (18609903809 / 1000000000000) (18609909474 / 1000000000000)))) (orderedInterval (-7037272887 / 1000000000000) (-7037266372 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (522729226447493 / 800000000000) 3 (IntervalRat.scale (905 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (21172809649 / 1000000000000) (21172809650 / 1000000000000), orderedInterval (22918783677 / 1000000000000) (22918783678 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (461847124353353 / 800000000000) 3 (IntervalRat.scale (905 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (1362413180 / 1000000000000) (1362413181 / 1000000000000), orderedInterval (33178347423 / 1000000000000) (33178347424 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (133861297993947 / 160000000000) 3 (IntervalRat.scale (905 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (27119722765 / 1000000000000) (27119746675 / 1000000000000), orderedInterval (-5061067250 / 1000000000000) (-5061043340 / 1000000000000)))) (orderedInterval (3971176881 / 1000000000000) (3971180899 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate581_chunkChecks3_2 :
    compactCertificate581.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (370267394985409 / 800000000000) 3 (IntervalRat.scale (905 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-36072795607 / 1000000000000) (-36072789500 / 1000000000000), orderedInterval (8654884872 / 1000000000000) (8654890979 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (313879771328249 / 800000000000) 3 (IntervalRat.scale (905 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-17000954679 / 1000000000000) (-17000954678 / 1000000000000), orderedInterval (-36496150242 / 1000000000000) (-36496150241 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (196411386992147 / 800000000000) 3 (IntervalRat.scale (905 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (48401760558 / 1000000000000) (48401760560 / 1000000000000), orderedInterval (15721377393 / 1000000000000) (15721377394 / 1000000000000)))) (orderedInterval (68496627 / 1000000000000) (68497771 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (105630697159149 / 800000000000) 3 (IntervalRat.scale (905 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (53337044900 / 1000000000000) (53337044901 / 1000000000000), orderedInterval (44257322348 / 1000000000000) (44257322349 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (286807890884447 / 800000000000) 3 (IntervalRat.scale (905 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (38520868076 / 1000000000000) (38520868078 / 1000000000000), orderedInterval (17030774674 / 1000000000000) (17030774676 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (391611655041919 / 800000000000) 3 (IntervalRat.scale (905 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (7561959600 / 1000000000000) (7561959601 / 1000000000000), orderedInterval (35253158040 / 1000000000000) (35253158041 / 1000000000000)))) (orderedInterval (3630020007 / 1000000000000) (3630020058 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (165588613007853 / 800000000000) 3 (IntervalRat.scale (905 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (22889249235 / 1000000000000) (22889249236 / 1000000000000), orderedInterval (50459632139 / 1000000000000) (50459632140 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (673108518672013 / 800000000000) 3 (IntervalRat.scale (905 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (6111950293 / 1000000000000) (6111950294 / 1000000000000), orderedInterval (26815703087 / 1000000000000) (26815703088 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (449605295888867 / 800000000000) 3 (IntervalRat.scale (905 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-14539661059 / 1000000000000) (-14539661058 / 1000000000000), orderedInterval (-30340986674 / 1000000000000) (-30340986673 / 1000000000000)))) (orderedInterval (3102868482 / 1000000000000) (3102868884 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate581_chunkChecks3 :
    compactCertificate581.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate581.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate581_chunkChecks3_0
    compactCertificate581_chunkChecks3_1 compactCertificate581_chunkChecks3_2

theorem compactCertificate581_chunkChecks4_0 :
    compactCertificate581.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (905 / 2) 4 (IntervalRat.scale (905 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (29282822811 / 1000000000000) (29282822812 / 1000000000000), orderedInterval (23407153236 / 1000000000000) (23407153237 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (266647561570081 / 800000000000) 4 (IntervalRat.scale (905 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (38660468414 / 1000000000000) (38660468415 / 1000000000000), orderedInterval (20322464656 / 1000000000000) (20322464657 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (86228342791873 / 160000000000) 4 (IntervalRat.scale (905 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-20570237344 / 1000000000000) (-20570235302 / 1000000000000), orderedInterval (27553388261 / 1000000000000) (27553390303 / 1000000000000)))) (orderedInterval (9337245998 / 1000000000000) (9337246296 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (77807093437667 / 800000000000) 4 (IntervalRat.scale (905 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-49194324424 / 1000000000000) (-49194324423 / 1000000000000), orderedInterval (-63977647672 / 1000000000000) (-63977647671 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (209000797446599 / 800000000000) 4 (IntervalRat.scale (905 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-47343943063 / 1000000000000) (-47343943061 / 1000000000000), orderedInterval (-13886518205 / 1000000000000) (-13886518203 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (567477821512683 / 800000000000) 4 (IntervalRat.scale (905 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (3959565565 / 1000000000000) (3959565566 / 1000000000000), orderedInterval (29692237118 / 1000000000000) (29692237119 / 1000000000000)))) (orderedInterval (-1927119261 / 1000000000000) (-1927119064 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (418001594893379 / 800000000000) 4 (IntervalRat.scale (905 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (34124378711 / 1000000000000) (34124385326 / 1000000000000), orderedInterval (-7376528621 / 1000000000000) (-7376522006 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (716252857458767 / 800000000000) 4 (IntervalRat.scale (905 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-18126007971 / 1000000000000) (-18126007970 / 1000000000000), orderedInterval (-19547580154 / 1000000000000) (-19547580153 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (527588613007853 / 800000000000) 4 (IntervalRat.scale (905 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (15881161744 / 1000000000000) (15881161745 / 1000000000000), orderedInterval (26692198320 / 1000000000000) (26692198321 / 1000000000000)))) (orderedInterval (10329602438 / 1000000000000) (10329602702 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate581_chunkChecks4_1 :
    compactCertificate581.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (809456607854819 / 800000000000) 4 (IntervalRat.scale (905 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (21284093771 / 1000000000000) (21284093778 / 1000000000000), orderedInterval (13262374851 / 1000000000000) (13262374858 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (467339990442251 / 800000000000) 4 (IntervalRat.scale (905 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (19286658893 / 1000000000000) (19286658894 / 1000000000000), orderedInterval (26775295783 / 1000000000000) (26775295784 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (829303014073159 / 800000000000) 4 (IntervalRat.scale (905 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (15745105225 / 1000000000000) (15745105226 / 1000000000000), orderedInterval (19129197439 / 1000000000000) (19129197440 / 1000000000000)))) (orderedInterval (-28882338077 / 1000000000000) (-28882334165 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (774842450104771 / 800000000000) 4 (IntervalRat.scale (905 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (25322323558 / 1000000000000) (25322358089 / 1000000000000), orderedInterval (-4021638447 / 1000000000000) (-4021603916 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (552964133857843 / 800000000000) 4 (IntervalRat.scale (905 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (22598781843 / 1000000000000) (22598781844 / 1000000000000), orderedInterval (20240100932 / 1000000000000) (20240100933 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (627002392339797 / 800000000000) 4 (IntervalRat.scale (905 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-21597570154 / 1000000000000) (-21597564490 / 1000000000000), orderedInterval (18609903809 / 1000000000000) (18609909474 / 1000000000000)))) (orderedInterval (3053899233 / 1000000000000) (3053913030 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (522729226447493 / 800000000000) 4 (IntervalRat.scale (905 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (21172809649 / 1000000000000) (21172809650 / 1000000000000), orderedInterval (22918783677 / 1000000000000) (22918783678 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (461847124353353 / 800000000000) 4 (IntervalRat.scale (905 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (1362413180 / 1000000000000) (1362413181 / 1000000000000), orderedInterval (33178347423 / 1000000000000) (33178347424 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (133861297993947 / 160000000000) 4 (IntervalRat.scale (905 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (27119722765 / 1000000000000) (27119746675 / 1000000000000), orderedInterval (-5061067250 / 1000000000000) (-5061043340 / 1000000000000)))) (orderedInterval (8953326443 / 1000000000000) (8953333842 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate581_chunkChecks4_2 :
    compactCertificate581.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (370267394985409 / 800000000000) 4 (IntervalRat.scale (905 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-36072795607 / 1000000000000) (-36072789500 / 1000000000000), orderedInterval (8654884872 / 1000000000000) (8654890979 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (313879771328249 / 800000000000) 4 (IntervalRat.scale (905 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-17000954679 / 1000000000000) (-17000954678 / 1000000000000), orderedInterval (-36496150242 / 1000000000000) (-36496150241 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (196411386992147 / 800000000000) 4 (IntervalRat.scale (905 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (48401760558 / 1000000000000) (48401760560 / 1000000000000), orderedInterval (15721377393 / 1000000000000) (15721377394 / 1000000000000)))) (orderedInterval (6993098235 / 1000000000000) (6993099405 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (105630697159149 / 800000000000) 4 (IntervalRat.scale (905 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (53337044900 / 1000000000000) (53337044901 / 1000000000000), orderedInterval (44257322348 / 1000000000000) (44257322349 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (286807890884447 / 800000000000) 4 (IntervalRat.scale (905 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (38520868076 / 1000000000000) (38520868078 / 1000000000000), orderedInterval (17030774674 / 1000000000000) (17030774676 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (391611655041919 / 800000000000) 4 (IntervalRat.scale (905 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (7561959600 / 1000000000000) (7561959601 / 1000000000000), orderedInterval (35253158040 / 1000000000000) (35253158041 / 1000000000000)))) (orderedInterval (-1161256203 / 1000000000000) (-1161256150 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (165588613007853 / 800000000000) 4 (IntervalRat.scale (905 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (22889249235 / 1000000000000) (22889249236 / 1000000000000), orderedInterval (50459632139 / 1000000000000) (50459632140 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (673108518672013 / 800000000000) 4 (IntervalRat.scale (905 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (6111950293 / 1000000000000) (6111950294 / 1000000000000), orderedInterval (26815703087 / 1000000000000) (26815703088 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (449605295888867 / 800000000000) 4 (IntervalRat.scale (905 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-14539661059 / 1000000000000) (-14539661058 / 1000000000000), orderedInterval (-30340986674 / 1000000000000) (-30340986673 / 1000000000000)))) (orderedInterval (536438238 / 1000000000000) (536438883 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate581_chunkChecks4 :
    compactCertificate581.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate581.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate581_chunkChecks4_0
    compactCertificate581_chunkChecks4_1 compactCertificate581_chunkChecks4_2

theorem compactCertificate581_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate581.chunkCheck r b = true :=
  compactCertificate581.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate581_chunkChecks0
    · exact compactCertificate581_chunkChecks1
    · exact compactCertificate581_chunkChecks2
    · exact compactCertificate581_chunkChecks3
    · exact compactCertificate581_chunkChecks4)

theorem compactCertificate581_coefficient0 :
    compactCertificate581.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate581_coefficient1 :
    compactCertificate581.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate581_coefficient2 :
    compactCertificate581.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate581_coefficient3 :
    compactCertificate581.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate581_coefficient4 :
    compactCertificate581.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate581_coefficients : ∀ r : Fin 5,
    compactCertificate581.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate581_coefficient0
  · exact compactCertificate581_coefficient1
  · exact compactCertificate581_coefficient2
  · exact compactCertificate581_coefficient3
  · exact compactCertificate581_coefficient4

theorem compactCertificate581_lower : (1 : ℚ) ≤ compactCertificate581.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate581, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate581_proves {t : ℝ} (ht : t ∈ compactCertificate581.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate581.proves compactCertificate581_states compactCertificate581_chunks
    compactCertificate581_coefficients compactCertificate581_lower ht

end Erdos232
