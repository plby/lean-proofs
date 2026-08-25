/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate488 : CompactCertificate where
  left := 359
  right := 360
  center := 719 / 2
  grid := fun i =>
    match i.val with
    | 0 => 114
    | 1 => 84
    | 2 => 136
    | 3 => 25
    | 4 => 66
    | 5 => 179
    | 6 => 132
    | 7 => 227
    | 8 => 167
    | 9 => 256
    | 10 => 148
    | 11 => 262
    | 12 => 245
    | 13 => 175
    | 14 => 198
    | 15 => 165
    | 16 => 146
    | 17 => 212
    | 18 => 117
    | 19 => 99
    | 20 => 62
    | 21 => 33
    | 22 => 91
    | 23 => 124
    | 24 => 52
    | 25 => 213
    | _ => 142
  point := fun i =>
    match i.val with
    | 0 => 719 / 2
    | 1 => 1059224291540819 / 4000000000000
    | 2 => 342531372747827 / 800000000000
    | 3 => 309079006528633 / 4000000000000
    | 4 => 830229687094501 / 4000000000000
    | 5 => 2254235103136017 / 4000000000000
    | 6 => 1660459374189721 / 4000000000000
    | 7 => 2845225439297533 / 4000000000000
    | 8 => 2095780180953847 / 4000000000000
    | 9 => 3215465751644281 / 4000000000000
    | 10 => 1856450017281649 / 4000000000000
    | 11 => 3294303133251941 / 4000000000000
    | 12 => 3077965312847129 / 4000000000000
    | 13 => 2196581283114857 / 4000000000000
    | 14 => 2490689061283503 / 4000000000000
    | 15 => 2076476871910207 / 4000000000000
    | 16 => 1834630289558347 / 4000000000000
    | 17 => 531747366064353 / 800000000000
    | 18 => 1470841198864691 / 4000000000000
    | 19 => 1246848373397851 / 4000000000000
    | 20 => 780219819046153 / 4000000000000
    | 21 => 419604813576951 / 4000000000000
    | 22 => 1139308693623853 / 4000000000000
    | 23 => 1555628618647181 / 4000000000000
    | 24 => 657780180953847 / 4000000000000
    | 25 => 2673839916713687 / 4000000000000
    | _ => 1786001147757433 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (35367093657 / 1000000000000) (35367181666 / 1000000000000), orderedInterval (-22853015412 / 1000000000000) (-22852927404 / 1000000000000))
    | 1 => (orderedInterval (48640270225 / 1000000000000) (48640270803 / 1000000000000), orderedInterval (-6273913550 / 1000000000000) (-6273912972 / 1000000000000))
    | 2 => (orderedInterval (38273541270 / 1000000000000) (38273542743 / 1000000000000), orderedInterval (-4734460012 / 1000000000000) (-4734458540 / 1000000000000))
    | 3 => (orderedInterval (42419681267 / 1000000000000) (42419686018 / 1000000000000), orderedInterval (-80521560259 / 1000000000000) (-80521555509 / 1000000000000))
    | 4 => (orderedInterval (46515628616 / 1000000000000) (46515628617 / 1000000000000), orderedInterval (29946071888 / 1000000000000) (29946071889 / 1000000000000))
    | 5 => (orderedInterval (-30577472411 / 1000000000000) (-30577410562 / 1000000000000), orderedInterval (13979227067 / 1000000000000) (13979288916 / 1000000000000))
    | 6 => (orderedInterval (36635820588 / 1000000000000) (36635820590 / 1000000000000), orderedInterval (13791152555 / 1000000000000) (13791152557 / 1000000000000))
    | 7 => (orderedInterval (25949551249 / 1000000000000) (25949600890 / 1000000000000), orderedInterval (-14905178063 / 1000000000000) (-14905128421 / 1000000000000))
    | 8 => (orderedInterval (-2932640813 / 1000000000000) (-2932640812 / 1000000000000), orderedInterval (-34731202339 / 1000000000000) (-34731202338 / 1000000000000))
    | 9 => (orderedInterval (11061427069 / 1000000000000) (11061427070 / 1000000000000), orderedInterval (25869598258 / 1000000000000) (25869598259 / 1000000000000))
    | 10 => (orderedInterval (-2149847049 / 1000000000000) (-2149847047 / 1000000000000), orderedInterval (36976249204 / 1000000000000) (36976249206 / 1000000000000))
    | 11 => (orderedInterval (26502495010 / 1000000000000) (26502495088 / 1000000000000), orderedInterval (8387029058 / 1000000000000) (8387029135 / 1000000000000))
    | 12 => (orderedInterval (-15915745549 / 1000000000000) (-15915745548 / 1000000000000), orderedInterval (-23948259614 / 1000000000000) (-23948259613 / 1000000000000))
    | 13 => (orderedInterval (-5147939254 / 1000000000000) (-5147939253 / 1000000000000), orderedInterval (-33652275966 / 1000000000000) (-33652275965 / 1000000000000))
    | 14 => (orderedInterval (31622216154 / 1000000000000) (31622216325 / 1000000000000), orderedInterval (4711121070 / 1000000000000) (4711121241 / 1000000000000))
    | 15 => (orderedInterval (-35004277907 / 1000000000000) (-35004277495 / 1000000000000), orderedInterval (-989010166 / 1000000000000) (-989009754 / 1000000000000))
    | 16 => (orderedInterval (25939742457 / 1000000000000) (25939742458 / 1000000000000), orderedInterval (26713757627 / 1000000000000) (26713757628 / 1000000000000))
    | 17 => (orderedInterval (-16129254342 / 1000000000000) (-16129254037 / 1000000000000), orderedInterval (26424725962 / 1000000000000) (26424726267 / 1000000000000))
    | 18 => (orderedInterval (-33330123125 / 1000000000000) (-33330123124 / 1000000000000), orderedInterval (-24862717947 / 1000000000000) (-24862717946 / 1000000000000))
    | 19 => (orderedInterval (-45003598380 / 1000000000000) (-45003598339 / 1000000000000), orderedInterval (-4051664816 / 1000000000000) (-4051664775 / 1000000000000))
    | 20 => (orderedInterval (49864281925 / 1000000000000) (49864281926 / 1000000000000), orderedInterval (27753082754 / 1000000000000) (27753082755 / 1000000000000))
    | 21 => (orderedInterval (-70413391428 / 1000000000000) (-70413383378 / 1000000000000), orderedInterval (33662273960 / 1000000000000) (33662282010 / 1000000000000))
    | 22 => (orderedInterval (12737709900 / 1000000000000) (12737709999 / 1000000000000), orderedInterval (-45551061969 / 1000000000000) (-45551061870 / 1000000000000))
    | 23 => (orderedInterval (5435082673 / 1000000000000) (5435082674 / 1000000000000), orderedInterval (40085487558 / 1000000000000) (40085487559 / 1000000000000))
    | 24 => (orderedInterval (59512672214 / 1000000000000) (59512674555 / 1000000000000), orderedInterval (-18334438489 / 1000000000000) (-18334436148 / 1000000000000))
    | 25 => (orderedInterval (-2649349082 / 1000000000000) (-2649349081 / 1000000000000), orderedInterval (-30744547081 / 1000000000000) (-30744547080 / 1000000000000))
    | _ => (orderedInterval (34902065892 / 1000000000000) (34902065894 / 1000000000000), orderedInterval (14370787928 / 1000000000000) (14370787929 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (16717445807 / 1000000000000) (16717480808 / 1000000000000)
      | 1 => orderedInterval (3411880417 / 1000000000000) (3411884909 / 1000000000000)
      | 2 => orderedInterval (-871265669 / 1000000000000) (-871264117 / 1000000000000)
      | 3 => orderedInterval (1642717737 / 1000000000000) (1642717891 / 1000000000000)
      | 4 => orderedInterval (-359502217 / 1000000000000) (-359502173 / 1000000000000)
      | 5 => orderedInterval (-2301635752 / 1000000000000) (-2301635705 / 1000000000000)
      | 6 => orderedInterval (9499781630 / 1000000000000) (9499781723 / 1000000000000)
      | 7 => orderedInterval (594674077 / 1000000000000) (594674272 / 1000000000000)
      | _ => orderedInterval (-5974129827 / 1000000000000) (-5974129713 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-9432084779 / 1000000000000) (-9432049760 / 1000000000000)
      | 1 => orderedInterval (-738837566 / 1000000000000) (-738830613 / 1000000000000)
      | 2 => orderedInterval (-313713086 / 1000000000000) (-313710021 / 1000000000000)
      | 3 => orderedInterval (-4010361270 / 1000000000000) (-4010360949 / 1000000000000)
      | 4 => orderedInterval (-3976868059 / 1000000000000) (-3976867988 / 1000000000000)
      | 5 => orderedInterval (-715956726 / 1000000000000) (-715956654 / 1000000000000)
      | 6 => orderedInterval (4755210198 / 1000000000000) (4755210284 / 1000000000000)
      | 7 => orderedInterval (-2686022351 / 1000000000000) (-2686022266 / 1000000000000)
      | _ => orderedInterval (1254064089 / 1000000000000) (1254064236 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-17423800139 / 1000000000000) (-17423764999 / 1000000000000)
      | 1 => orderedInterval (-5884617212 / 1000000000000) (-5884606318 / 1000000000000)
      | 2 => orderedInterval (3284822446 / 1000000000000) (3284828511 / 1000000000000)
      | 3 => orderedInterval (-9668430354 / 1000000000000) (-9668429662 / 1000000000000)
      | 4 => orderedInterval (310617077 / 1000000000000) (310617195 / 1000000000000)
      | 5 => orderedInterval (4672842169 / 1000000000000) (4672842280 / 1000000000000)
      | 6 => orderedInterval (-7981567983 / 1000000000000) (-7981567901 / 1000000000000)
      | 7 => orderedInterval (565634616 / 1000000000000) (565634669 / 1000000000000)
      | _ => orderedInterval (9277430637 / 1000000000000) (9277430848 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (9599215264 / 1000000000000) (9599250430 / 1000000000000)
      | 1 => orderedInterval (3625606375 / 1000000000000) (3625623445 / 1000000000000)
      | 2 => orderedInterval (-971722950 / 1000000000000) (-971710959 / 1000000000000)
      | 3 => orderedInterval (31190295592 / 1000000000000) (31190297113 / 1000000000000)
      | 4 => orderedInterval (7225516681 / 1000000000000) (7225516882 / 1000000000000)
      | 5 => orderedInterval (-1080204729 / 1000000000000) (-1080204551 / 1000000000000)
      | 6 => orderedInterval (-4525563022 / 1000000000000) (-4525562942 / 1000000000000)
      | 7 => orderedInterval (3389252673 / 1000000000000) (3389252718 / 1000000000000)
      | _ => orderedInterval (-10938441570 / 1000000000000) (-10938441249 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (18617172711 / 1000000000000) (18617208009 / 1000000000000)
      | 1 => orderedInterval (13294594767 / 1000000000000) (13294621570 / 1000000000000)
      | 2 => orderedInterval (-12581182516 / 1000000000000) (-12581158773 / 1000000000000)
      | 3 => orderedInterval (54016533615 / 1000000000000) (54016537006 / 1000000000000)
      | 4 => orderedInterval (1900305689 / 1000000000000) (1900306036 / 1000000000000)
      | 5 => orderedInterval (-10510414318 / 1000000000000) (-10510414025 / 1000000000000)
      | 6 => orderedInterval (7438539360 / 1000000000000) (7438539438 / 1000000000000)
      | 7 => orderedInterval (-693775211 / 1000000000000) (-693775167 / 1000000000000)
      | _ => orderedInterval (-12927876934 / 1000000000000) (-12927876420 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (22359966203 / 1000000000000) (22360007895 / 1000000000000)
    | 1 => orderedInterval (-15864569550 / 1000000000000) (-15864523731 / 1000000000000)
    | 2 => orderedInterval (-22847068743 / 1000000000000) (-22847015377 / 1000000000000)
    | 3 => orderedInterval (37513954314 / 1000000000000) (37514020887 / 1000000000000)
    | _ => orderedInterval (58553897163 / 1000000000000) (58553987674 / 1000000000000)

theorem compactCertificate488_stateChecks0 :
    compactCertificate488.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 114 12 (719 / 2)) (orderedInterval (35367093657 / 1000000000000) (35367181666 / 1000000000000), orderedInterval (-22853015412 / 1000000000000) (-22852927404 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 84 12 (1059224291540819 / 4000000000000)) (orderedInterval (48640270225 / 1000000000000) (48640270803 / 1000000000000), orderedInterval (-6273913550 / 1000000000000) (-6273912972 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 136 12 (342531372747827 / 800000000000)) (orderedInterval (38273541270 / 1000000000000) (38273542743 / 1000000000000), orderedInterval (-4734460012 / 1000000000000) (-4734458540 / 1000000000000))) = true
  rfl'

theorem compactCertificate488_stateChecks1 :
    compactCertificate488.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 25 12 (309079006528633 / 4000000000000)) (orderedInterval (42419681267 / 1000000000000) (42419686018 / 1000000000000), orderedInterval (-80521560259 / 1000000000000) (-80521555509 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (830229687094501 / 4000000000000)) (orderedInterval (46515628616 / 1000000000000) (46515628617 / 1000000000000), orderedInterval (29946071888 / 1000000000000) (29946071889 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 179 12 (2254235103136017 / 4000000000000)) (orderedInterval (-30577472411 / 1000000000000) (-30577410562 / 1000000000000), orderedInterval (13979227067 / 1000000000000) (13979288916 / 1000000000000))) = true
  rfl'

theorem compactCertificate488_stateChecks2 :
    compactCertificate488.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 132 12 (1660459374189721 / 4000000000000)) (orderedInterval (36635820588 / 1000000000000) (36635820590 / 1000000000000), orderedInterval (13791152555 / 1000000000000) (13791152557 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 227 12 (2845225439297533 / 4000000000000)) (orderedInterval (25949551249 / 1000000000000) (25949600890 / 1000000000000), orderedInterval (-14905178063 / 1000000000000) (-14905128421 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 167 12 (2095780180953847 / 4000000000000)) (orderedInterval (-2932640813 / 1000000000000) (-2932640812 / 1000000000000), orderedInterval (-34731202339 / 1000000000000) (-34731202338 / 1000000000000))) = true
  rfl'

theorem compactCertificate488_stateChecks3 :
    compactCertificate488.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 256 12 (3215465751644281 / 4000000000000)) (orderedInterval (11061427069 / 1000000000000) (11061427070 / 1000000000000), orderedInterval (25869598258 / 1000000000000) (25869598259 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 148 12 (1856450017281649 / 4000000000000)) (orderedInterval (-2149847049 / 1000000000000) (-2149847047 / 1000000000000), orderedInterval (36976249204 / 1000000000000) (36976249206 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 262 12 (3294303133251941 / 4000000000000)) (orderedInterval (26502495010 / 1000000000000) (26502495088 / 1000000000000), orderedInterval (8387029058 / 1000000000000) (8387029135 / 1000000000000))) = true
  rfl'

theorem compactCertificate488_stateChecks4 :
    compactCertificate488.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 245 12 (3077965312847129 / 4000000000000)) (orderedInterval (-15915745549 / 1000000000000) (-15915745548 / 1000000000000), orderedInterval (-23948259614 / 1000000000000) (-23948259613 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 175 12 (2196581283114857 / 4000000000000)) (orderedInterval (-5147939254 / 1000000000000) (-5147939253 / 1000000000000), orderedInterval (-33652275966 / 1000000000000) (-33652275965 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 198 12 (2490689061283503 / 4000000000000)) (orderedInterval (31622216154 / 1000000000000) (31622216325 / 1000000000000), orderedInterval (4711121070 / 1000000000000) (4711121241 / 1000000000000))) = true
  rfl'

theorem compactCertificate488_stateChecks5 :
    compactCertificate488.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 165 12 (2076476871910207 / 4000000000000)) (orderedInterval (-35004277907 / 1000000000000) (-35004277495 / 1000000000000), orderedInterval (-989010166 / 1000000000000) (-989009754 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 146 12 (1834630289558347 / 4000000000000)) (orderedInterval (25939742457 / 1000000000000) (25939742458 / 1000000000000), orderedInterval (26713757627 / 1000000000000) (26713757628 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 212 12 (531747366064353 / 800000000000)) (orderedInterval (-16129254342 / 1000000000000) (-16129254037 / 1000000000000), orderedInterval (26424725962 / 1000000000000) (26424726267 / 1000000000000))) = true
  rfl'

theorem compactCertificate488_stateChecks6 :
    compactCertificate488.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 117 12 (1470841198864691 / 4000000000000)) (orderedInterval (-33330123125 / 1000000000000) (-33330123124 / 1000000000000), orderedInterval (-24862717947 / 1000000000000) (-24862717946 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 99 12 (1246848373397851 / 4000000000000)) (orderedInterval (-45003598380 / 1000000000000) (-45003598339 / 1000000000000), orderedInterval (-4051664816 / 1000000000000) (-4051664775 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (780219819046153 / 4000000000000)) (orderedInterval (49864281925 / 1000000000000) (49864281926 / 1000000000000), orderedInterval (27753082754 / 1000000000000) (27753082755 / 1000000000000))) = true
  rfl'

theorem compactCertificate488_stateChecks7 :
    compactCertificate488.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 33 12 (419604813576951 / 4000000000000)) (orderedInterval (-70413391428 / 1000000000000) (-70413383378 / 1000000000000), orderedInterval (33662273960 / 1000000000000) (33662282010 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 91 12 (1139308693623853 / 4000000000000)) (orderedInterval (12737709900 / 1000000000000) (12737709999 / 1000000000000), orderedInterval (-45551061969 / 1000000000000) (-45551061870 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 124 12 (1555628618647181 / 4000000000000)) (orderedInterval (5435082673 / 1000000000000) (5435082674 / 1000000000000), orderedInterval (40085487558 / 1000000000000) (40085487559 / 1000000000000))) = true
  rfl'

theorem compactCertificate488_stateChecks8 :
    compactCertificate488.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 52 12 (657780180953847 / 4000000000000)) (orderedInterval (59512672214 / 1000000000000) (59512674555 / 1000000000000), orderedInterval (-18334438489 / 1000000000000) (-18334436148 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 213 12 (2673839916713687 / 4000000000000)) (orderedInterval (-2649349082 / 1000000000000) (-2649349081 / 1000000000000), orderedInterval (-30744547081 / 1000000000000) (-30744547080 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 142 12 (1786001147757433 / 4000000000000)) (orderedInterval (34902065892 / 1000000000000) (34902065894 / 1000000000000), orderedInterval (14370787928 / 1000000000000) (14370787929 / 1000000000000))) = true
  rfl'

theorem compactCertificate488_states : ∀ j,
    BesselStateValid (compactCertificate488.point j) (compactCertificate488.state j) :=
  compactCertificate488.statesValid_of_checks3 compactCertificate488_stateChecks0
    compactCertificate488_stateChecks1 compactCertificate488_stateChecks2
    compactCertificate488_stateChecks3 compactCertificate488_stateChecks4
    compactCertificate488_stateChecks5 compactCertificate488_stateChecks6
    compactCertificate488_stateChecks7 compactCertificate488_stateChecks8

theorem compactCertificate488_chunkChecks0_0 :
    compactCertificate488.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (719 / 2) 0 (IntervalRat.scale (719 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (35367093657 / 1000000000000) (35367181666 / 1000000000000), orderedInterval (-22853015412 / 1000000000000) (-22852927404 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1059224291540819 / 4000000000000) 0 (IntervalRat.scale (719 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (48640270225 / 1000000000000) (48640270803 / 1000000000000), orderedInterval (-6273913550 / 1000000000000) (-6273912972 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (342531372747827 / 800000000000) 0 (IntervalRat.scale (719 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (38273541270 / 1000000000000) (38273542743 / 1000000000000), orderedInterval (-4734460012 / 1000000000000) (-4734458540 / 1000000000000)))) (orderedInterval (16717445807 / 1000000000000) (16717480808 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (309079006528633 / 4000000000000) 0 (IntervalRat.scale (719 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (42419681267 / 1000000000000) (42419686018 / 1000000000000), orderedInterval (-80521560259 / 1000000000000) (-80521555509 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (830229687094501 / 4000000000000) 0 (IntervalRat.scale (719 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (46515628616 / 1000000000000) (46515628617 / 1000000000000), orderedInterval (29946071888 / 1000000000000) (29946071889 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2254235103136017 / 4000000000000) 0 (IntervalRat.scale (719 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30577472411 / 1000000000000) (-30577410562 / 1000000000000), orderedInterval (13979227067 / 1000000000000) (13979288916 / 1000000000000)))) (orderedInterval (3411880417 / 1000000000000) (3411884909 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1660459374189721 / 4000000000000) 0 (IntervalRat.scale (719 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (36635820588 / 1000000000000) (36635820590 / 1000000000000), orderedInterval (13791152555 / 1000000000000) (13791152557 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2845225439297533 / 4000000000000) 0 (IntervalRat.scale (719 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (25949551249 / 1000000000000) (25949600890 / 1000000000000), orderedInterval (-14905178063 / 1000000000000) (-14905128421 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2095780180953847 / 4000000000000) 0 (IntervalRat.scale (719 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-2932640813 / 1000000000000) (-2932640812 / 1000000000000), orderedInterval (-34731202339 / 1000000000000) (-34731202338 / 1000000000000)))) (orderedInterval (-871265669 / 1000000000000) (-871264117 / 1000000000000))) = true
  rfl'

theorem compactCertificate488_chunkChecks0_1 :
    compactCertificate488.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3215465751644281 / 4000000000000) 0 (IntervalRat.scale (719 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (11061427069 / 1000000000000) (11061427070 / 1000000000000), orderedInterval (25869598258 / 1000000000000) (25869598259 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1856450017281649 / 4000000000000) 0 (IntervalRat.scale (719 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-2149847049 / 1000000000000) (-2149847047 / 1000000000000), orderedInterval (36976249204 / 1000000000000) (36976249206 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3294303133251941 / 4000000000000) 0 (IntervalRat.scale (719 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (26502495010 / 1000000000000) (26502495088 / 1000000000000), orderedInterval (8387029058 / 1000000000000) (8387029135 / 1000000000000)))) (orderedInterval (1642717737 / 1000000000000) (1642717891 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3077965312847129 / 4000000000000) 0 (IntervalRat.scale (719 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-15915745549 / 1000000000000) (-15915745548 / 1000000000000), orderedInterval (-23948259614 / 1000000000000) (-23948259613 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2196581283114857 / 4000000000000) 0 (IntervalRat.scale (719 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-5147939254 / 1000000000000) (-5147939253 / 1000000000000), orderedInterval (-33652275966 / 1000000000000) (-33652275965 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2490689061283503 / 4000000000000) 0 (IntervalRat.scale (719 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (31622216154 / 1000000000000) (31622216325 / 1000000000000), orderedInterval (4711121070 / 1000000000000) (4711121241 / 1000000000000)))) (orderedInterval (-359502217 / 1000000000000) (-359502173 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2076476871910207 / 4000000000000) 0 (IntervalRat.scale (719 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-35004277907 / 1000000000000) (-35004277495 / 1000000000000), orderedInterval (-989010166 / 1000000000000) (-989009754 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1834630289558347 / 4000000000000) 0 (IntervalRat.scale (719 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (25939742457 / 1000000000000) (25939742458 / 1000000000000), orderedInterval (26713757627 / 1000000000000) (26713757628 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (531747366064353 / 800000000000) 0 (IntervalRat.scale (719 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-16129254342 / 1000000000000) (-16129254037 / 1000000000000), orderedInterval (26424725962 / 1000000000000) (26424726267 / 1000000000000)))) (orderedInterval (-2301635752 / 1000000000000) (-2301635705 / 1000000000000))) = true
  rfl'

theorem compactCertificate488_chunkChecks0_2 :
    compactCertificate488.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1470841198864691 / 4000000000000) 0 (IntervalRat.scale (719 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-33330123125 / 1000000000000) (-33330123124 / 1000000000000), orderedInterval (-24862717947 / 1000000000000) (-24862717946 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1246848373397851 / 4000000000000) 0 (IntervalRat.scale (719 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-45003598380 / 1000000000000) (-45003598339 / 1000000000000), orderedInterval (-4051664816 / 1000000000000) (-4051664775 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (780219819046153 / 4000000000000) 0 (IntervalRat.scale (719 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (49864281925 / 1000000000000) (49864281926 / 1000000000000), orderedInterval (27753082754 / 1000000000000) (27753082755 / 1000000000000)))) (orderedInterval (9499781630 / 1000000000000) (9499781723 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (419604813576951 / 4000000000000) 0 (IntervalRat.scale (719 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-70413391428 / 1000000000000) (-70413383378 / 1000000000000), orderedInterval (33662273960 / 1000000000000) (33662282010 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1139308693623853 / 4000000000000) 0 (IntervalRat.scale (719 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (12737709900 / 1000000000000) (12737709999 / 1000000000000), orderedInterval (-45551061969 / 1000000000000) (-45551061870 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1555628618647181 / 4000000000000) 0 (IntervalRat.scale (719 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (5435082673 / 1000000000000) (5435082674 / 1000000000000), orderedInterval (40085487558 / 1000000000000) (40085487559 / 1000000000000)))) (orderedInterval (594674077 / 1000000000000) (594674272 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (657780180953847 / 4000000000000) 0 (IntervalRat.scale (719 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (59512672214 / 1000000000000) (59512674555 / 1000000000000), orderedInterval (-18334438489 / 1000000000000) (-18334436148 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2673839916713687 / 4000000000000) 0 (IntervalRat.scale (719 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-2649349082 / 1000000000000) (-2649349081 / 1000000000000), orderedInterval (-30744547081 / 1000000000000) (-30744547080 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1786001147757433 / 4000000000000) 0 (IntervalRat.scale (719 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (34902065892 / 1000000000000) (34902065894 / 1000000000000), orderedInterval (14370787928 / 1000000000000) (14370787929 / 1000000000000)))) (orderedInterval (-5974129827 / 1000000000000) (-5974129713 / 1000000000000))) = true
  rfl'

theorem compactCertificate488_chunkChecks0 :
    compactCertificate488.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate488.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate488_chunkChecks0_0
    compactCertificate488_chunkChecks0_1 compactCertificate488_chunkChecks0_2

theorem compactCertificate488_chunkChecks1_0 :
    compactCertificate488.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (719 / 2) 1 (IntervalRat.scale (719 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (35367093657 / 1000000000000) (35367181666 / 1000000000000), orderedInterval (-22853015412 / 1000000000000) (-22852927404 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1059224291540819 / 4000000000000) 1 (IntervalRat.scale (719 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (48640270225 / 1000000000000) (48640270803 / 1000000000000), orderedInterval (-6273913550 / 1000000000000) (-6273912972 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (342531372747827 / 800000000000) 1 (IntervalRat.scale (719 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (38273541270 / 1000000000000) (38273542743 / 1000000000000), orderedInterval (-4734460012 / 1000000000000) (-4734458540 / 1000000000000)))) (orderedInterval (-9432084779 / 1000000000000) (-9432049760 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (309079006528633 / 4000000000000) 1 (IntervalRat.scale (719 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (42419681267 / 1000000000000) (42419686018 / 1000000000000), orderedInterval (-80521560259 / 1000000000000) (-80521555509 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (830229687094501 / 4000000000000) 1 (IntervalRat.scale (719 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (46515628616 / 1000000000000) (46515628617 / 1000000000000), orderedInterval (29946071888 / 1000000000000) (29946071889 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2254235103136017 / 4000000000000) 1 (IntervalRat.scale (719 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30577472411 / 1000000000000) (-30577410562 / 1000000000000), orderedInterval (13979227067 / 1000000000000) (13979288916 / 1000000000000)))) (orderedInterval (-738837566 / 1000000000000) (-738830613 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1660459374189721 / 4000000000000) 1 (IntervalRat.scale (719 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (36635820588 / 1000000000000) (36635820590 / 1000000000000), orderedInterval (13791152555 / 1000000000000) (13791152557 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2845225439297533 / 4000000000000) 1 (IntervalRat.scale (719 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (25949551249 / 1000000000000) (25949600890 / 1000000000000), orderedInterval (-14905178063 / 1000000000000) (-14905128421 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2095780180953847 / 4000000000000) 1 (IntervalRat.scale (719 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-2932640813 / 1000000000000) (-2932640812 / 1000000000000), orderedInterval (-34731202339 / 1000000000000) (-34731202338 / 1000000000000)))) (orderedInterval (-313713086 / 1000000000000) (-313710021 / 1000000000000))) = true
  rfl'

theorem compactCertificate488_chunkChecks1_1 :
    compactCertificate488.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3215465751644281 / 4000000000000) 1 (IntervalRat.scale (719 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (11061427069 / 1000000000000) (11061427070 / 1000000000000), orderedInterval (25869598258 / 1000000000000) (25869598259 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1856450017281649 / 4000000000000) 1 (IntervalRat.scale (719 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-2149847049 / 1000000000000) (-2149847047 / 1000000000000), orderedInterval (36976249204 / 1000000000000) (36976249206 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3294303133251941 / 4000000000000) 1 (IntervalRat.scale (719 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (26502495010 / 1000000000000) (26502495088 / 1000000000000), orderedInterval (8387029058 / 1000000000000) (8387029135 / 1000000000000)))) (orderedInterval (-4010361270 / 1000000000000) (-4010360949 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3077965312847129 / 4000000000000) 1 (IntervalRat.scale (719 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-15915745549 / 1000000000000) (-15915745548 / 1000000000000), orderedInterval (-23948259614 / 1000000000000) (-23948259613 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2196581283114857 / 4000000000000) 1 (IntervalRat.scale (719 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-5147939254 / 1000000000000) (-5147939253 / 1000000000000), orderedInterval (-33652275966 / 1000000000000) (-33652275965 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2490689061283503 / 4000000000000) 1 (IntervalRat.scale (719 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (31622216154 / 1000000000000) (31622216325 / 1000000000000), orderedInterval (4711121070 / 1000000000000) (4711121241 / 1000000000000)))) (orderedInterval (-3976868059 / 1000000000000) (-3976867988 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2076476871910207 / 4000000000000) 1 (IntervalRat.scale (719 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-35004277907 / 1000000000000) (-35004277495 / 1000000000000), orderedInterval (-989010166 / 1000000000000) (-989009754 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1834630289558347 / 4000000000000) 1 (IntervalRat.scale (719 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (25939742457 / 1000000000000) (25939742458 / 1000000000000), orderedInterval (26713757627 / 1000000000000) (26713757628 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (531747366064353 / 800000000000) 1 (IntervalRat.scale (719 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-16129254342 / 1000000000000) (-16129254037 / 1000000000000), orderedInterval (26424725962 / 1000000000000) (26424726267 / 1000000000000)))) (orderedInterval (-715956726 / 1000000000000) (-715956654 / 1000000000000))) = true
  rfl'

theorem compactCertificate488_chunkChecks1_2 :
    compactCertificate488.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1470841198864691 / 4000000000000) 1 (IntervalRat.scale (719 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-33330123125 / 1000000000000) (-33330123124 / 1000000000000), orderedInterval (-24862717947 / 1000000000000) (-24862717946 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1246848373397851 / 4000000000000) 1 (IntervalRat.scale (719 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-45003598380 / 1000000000000) (-45003598339 / 1000000000000), orderedInterval (-4051664816 / 1000000000000) (-4051664775 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (780219819046153 / 4000000000000) 1 (IntervalRat.scale (719 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (49864281925 / 1000000000000) (49864281926 / 1000000000000), orderedInterval (27753082754 / 1000000000000) (27753082755 / 1000000000000)))) (orderedInterval (4755210198 / 1000000000000) (4755210284 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (419604813576951 / 4000000000000) 1 (IntervalRat.scale (719 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-70413391428 / 1000000000000) (-70413383378 / 1000000000000), orderedInterval (33662273960 / 1000000000000) (33662282010 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1139308693623853 / 4000000000000) 1 (IntervalRat.scale (719 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (12737709900 / 1000000000000) (12737709999 / 1000000000000), orderedInterval (-45551061969 / 1000000000000) (-45551061870 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1555628618647181 / 4000000000000) 1 (IntervalRat.scale (719 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (5435082673 / 1000000000000) (5435082674 / 1000000000000), orderedInterval (40085487558 / 1000000000000) (40085487559 / 1000000000000)))) (orderedInterval (-2686022351 / 1000000000000) (-2686022266 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (657780180953847 / 4000000000000) 1 (IntervalRat.scale (719 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (59512672214 / 1000000000000) (59512674555 / 1000000000000), orderedInterval (-18334438489 / 1000000000000) (-18334436148 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2673839916713687 / 4000000000000) 1 (IntervalRat.scale (719 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-2649349082 / 1000000000000) (-2649349081 / 1000000000000), orderedInterval (-30744547081 / 1000000000000) (-30744547080 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1786001147757433 / 4000000000000) 1 (IntervalRat.scale (719 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (34902065892 / 1000000000000) (34902065894 / 1000000000000), orderedInterval (14370787928 / 1000000000000) (14370787929 / 1000000000000)))) (orderedInterval (1254064089 / 1000000000000) (1254064236 / 1000000000000))) = true
  rfl'

theorem compactCertificate488_chunkChecks1 :
    compactCertificate488.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate488.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate488_chunkChecks1_0
    compactCertificate488_chunkChecks1_1 compactCertificate488_chunkChecks1_2

theorem compactCertificate488_chunkChecks2_0 :
    compactCertificate488.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (719 / 2) 2 (IntervalRat.scale (719 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (35367093657 / 1000000000000) (35367181666 / 1000000000000), orderedInterval (-22853015412 / 1000000000000) (-22852927404 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1059224291540819 / 4000000000000) 2 (IntervalRat.scale (719 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (48640270225 / 1000000000000) (48640270803 / 1000000000000), orderedInterval (-6273913550 / 1000000000000) (-6273912972 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (342531372747827 / 800000000000) 2 (IntervalRat.scale (719 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (38273541270 / 1000000000000) (38273542743 / 1000000000000), orderedInterval (-4734460012 / 1000000000000) (-4734458540 / 1000000000000)))) (orderedInterval (-17423800139 / 1000000000000) (-17423764999 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (309079006528633 / 4000000000000) 2 (IntervalRat.scale (719 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (42419681267 / 1000000000000) (42419686018 / 1000000000000), orderedInterval (-80521560259 / 1000000000000) (-80521555509 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (830229687094501 / 4000000000000) 2 (IntervalRat.scale (719 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (46515628616 / 1000000000000) (46515628617 / 1000000000000), orderedInterval (29946071888 / 1000000000000) (29946071889 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2254235103136017 / 4000000000000) 2 (IntervalRat.scale (719 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30577472411 / 1000000000000) (-30577410562 / 1000000000000), orderedInterval (13979227067 / 1000000000000) (13979288916 / 1000000000000)))) (orderedInterval (-5884617212 / 1000000000000) (-5884606318 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1660459374189721 / 4000000000000) 2 (IntervalRat.scale (719 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (36635820588 / 1000000000000) (36635820590 / 1000000000000), orderedInterval (13791152555 / 1000000000000) (13791152557 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2845225439297533 / 4000000000000) 2 (IntervalRat.scale (719 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (25949551249 / 1000000000000) (25949600890 / 1000000000000), orderedInterval (-14905178063 / 1000000000000) (-14905128421 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2095780180953847 / 4000000000000) 2 (IntervalRat.scale (719 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-2932640813 / 1000000000000) (-2932640812 / 1000000000000), orderedInterval (-34731202339 / 1000000000000) (-34731202338 / 1000000000000)))) (orderedInterval (3284822446 / 1000000000000) (3284828511 / 1000000000000))) = true
  rfl'

theorem compactCertificate488_chunkChecks2_1 :
    compactCertificate488.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3215465751644281 / 4000000000000) 2 (IntervalRat.scale (719 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (11061427069 / 1000000000000) (11061427070 / 1000000000000), orderedInterval (25869598258 / 1000000000000) (25869598259 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1856450017281649 / 4000000000000) 2 (IntervalRat.scale (719 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-2149847049 / 1000000000000) (-2149847047 / 1000000000000), orderedInterval (36976249204 / 1000000000000) (36976249206 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3294303133251941 / 4000000000000) 2 (IntervalRat.scale (719 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (26502495010 / 1000000000000) (26502495088 / 1000000000000), orderedInterval (8387029058 / 1000000000000) (8387029135 / 1000000000000)))) (orderedInterval (-9668430354 / 1000000000000) (-9668429662 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3077965312847129 / 4000000000000) 2 (IntervalRat.scale (719 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-15915745549 / 1000000000000) (-15915745548 / 1000000000000), orderedInterval (-23948259614 / 1000000000000) (-23948259613 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2196581283114857 / 4000000000000) 2 (IntervalRat.scale (719 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-5147939254 / 1000000000000) (-5147939253 / 1000000000000), orderedInterval (-33652275966 / 1000000000000) (-33652275965 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2490689061283503 / 4000000000000) 2 (IntervalRat.scale (719 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (31622216154 / 1000000000000) (31622216325 / 1000000000000), orderedInterval (4711121070 / 1000000000000) (4711121241 / 1000000000000)))) (orderedInterval (310617077 / 1000000000000) (310617195 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2076476871910207 / 4000000000000) 2 (IntervalRat.scale (719 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-35004277907 / 1000000000000) (-35004277495 / 1000000000000), orderedInterval (-989010166 / 1000000000000) (-989009754 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1834630289558347 / 4000000000000) 2 (IntervalRat.scale (719 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (25939742457 / 1000000000000) (25939742458 / 1000000000000), orderedInterval (26713757627 / 1000000000000) (26713757628 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (531747366064353 / 800000000000) 2 (IntervalRat.scale (719 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-16129254342 / 1000000000000) (-16129254037 / 1000000000000), orderedInterval (26424725962 / 1000000000000) (26424726267 / 1000000000000)))) (orderedInterval (4672842169 / 1000000000000) (4672842280 / 1000000000000))) = true
  rfl'

theorem compactCertificate488_chunkChecks2_2 :
    compactCertificate488.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1470841198864691 / 4000000000000) 2 (IntervalRat.scale (719 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-33330123125 / 1000000000000) (-33330123124 / 1000000000000), orderedInterval (-24862717947 / 1000000000000) (-24862717946 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1246848373397851 / 4000000000000) 2 (IntervalRat.scale (719 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-45003598380 / 1000000000000) (-45003598339 / 1000000000000), orderedInterval (-4051664816 / 1000000000000) (-4051664775 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (780219819046153 / 4000000000000) 2 (IntervalRat.scale (719 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (49864281925 / 1000000000000) (49864281926 / 1000000000000), orderedInterval (27753082754 / 1000000000000) (27753082755 / 1000000000000)))) (orderedInterval (-7981567983 / 1000000000000) (-7981567901 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (419604813576951 / 4000000000000) 2 (IntervalRat.scale (719 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-70413391428 / 1000000000000) (-70413383378 / 1000000000000), orderedInterval (33662273960 / 1000000000000) (33662282010 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1139308693623853 / 4000000000000) 2 (IntervalRat.scale (719 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (12737709900 / 1000000000000) (12737709999 / 1000000000000), orderedInterval (-45551061969 / 1000000000000) (-45551061870 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1555628618647181 / 4000000000000) 2 (IntervalRat.scale (719 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (5435082673 / 1000000000000) (5435082674 / 1000000000000), orderedInterval (40085487558 / 1000000000000) (40085487559 / 1000000000000)))) (orderedInterval (565634616 / 1000000000000) (565634669 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (657780180953847 / 4000000000000) 2 (IntervalRat.scale (719 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (59512672214 / 1000000000000) (59512674555 / 1000000000000), orderedInterval (-18334438489 / 1000000000000) (-18334436148 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2673839916713687 / 4000000000000) 2 (IntervalRat.scale (719 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-2649349082 / 1000000000000) (-2649349081 / 1000000000000), orderedInterval (-30744547081 / 1000000000000) (-30744547080 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1786001147757433 / 4000000000000) 2 (IntervalRat.scale (719 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (34902065892 / 1000000000000) (34902065894 / 1000000000000), orderedInterval (14370787928 / 1000000000000) (14370787929 / 1000000000000)))) (orderedInterval (9277430637 / 1000000000000) (9277430848 / 1000000000000))) = true
  rfl'

theorem compactCertificate488_chunkChecks2 :
    compactCertificate488.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate488.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate488_chunkChecks2_0
    compactCertificate488_chunkChecks2_1 compactCertificate488_chunkChecks2_2

theorem compactCertificate488_chunkChecks3_0 :
    compactCertificate488.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (719 / 2) 3 (IntervalRat.scale (719 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (35367093657 / 1000000000000) (35367181666 / 1000000000000), orderedInterval (-22853015412 / 1000000000000) (-22852927404 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1059224291540819 / 4000000000000) 3 (IntervalRat.scale (719 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (48640270225 / 1000000000000) (48640270803 / 1000000000000), orderedInterval (-6273913550 / 1000000000000) (-6273912972 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (342531372747827 / 800000000000) 3 (IntervalRat.scale (719 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (38273541270 / 1000000000000) (38273542743 / 1000000000000), orderedInterval (-4734460012 / 1000000000000) (-4734458540 / 1000000000000)))) (orderedInterval (9599215264 / 1000000000000) (9599250430 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (309079006528633 / 4000000000000) 3 (IntervalRat.scale (719 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (42419681267 / 1000000000000) (42419686018 / 1000000000000), orderedInterval (-80521560259 / 1000000000000) (-80521555509 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (830229687094501 / 4000000000000) 3 (IntervalRat.scale (719 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (46515628616 / 1000000000000) (46515628617 / 1000000000000), orderedInterval (29946071888 / 1000000000000) (29946071889 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2254235103136017 / 4000000000000) 3 (IntervalRat.scale (719 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30577472411 / 1000000000000) (-30577410562 / 1000000000000), orderedInterval (13979227067 / 1000000000000) (13979288916 / 1000000000000)))) (orderedInterval (3625606375 / 1000000000000) (3625623445 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1660459374189721 / 4000000000000) 3 (IntervalRat.scale (719 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (36635820588 / 1000000000000) (36635820590 / 1000000000000), orderedInterval (13791152555 / 1000000000000) (13791152557 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2845225439297533 / 4000000000000) 3 (IntervalRat.scale (719 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (25949551249 / 1000000000000) (25949600890 / 1000000000000), orderedInterval (-14905178063 / 1000000000000) (-14905128421 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2095780180953847 / 4000000000000) 3 (IntervalRat.scale (719 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-2932640813 / 1000000000000) (-2932640812 / 1000000000000), orderedInterval (-34731202339 / 1000000000000) (-34731202338 / 1000000000000)))) (orderedInterval (-971722950 / 1000000000000) (-971710959 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate488_chunkChecks3_1 :
    compactCertificate488.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3215465751644281 / 4000000000000) 3 (IntervalRat.scale (719 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (11061427069 / 1000000000000) (11061427070 / 1000000000000), orderedInterval (25869598258 / 1000000000000) (25869598259 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1856450017281649 / 4000000000000) 3 (IntervalRat.scale (719 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-2149847049 / 1000000000000) (-2149847047 / 1000000000000), orderedInterval (36976249204 / 1000000000000) (36976249206 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3294303133251941 / 4000000000000) 3 (IntervalRat.scale (719 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (26502495010 / 1000000000000) (26502495088 / 1000000000000), orderedInterval (8387029058 / 1000000000000) (8387029135 / 1000000000000)))) (orderedInterval (31190295592 / 1000000000000) (31190297113 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3077965312847129 / 4000000000000) 3 (IntervalRat.scale (719 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-15915745549 / 1000000000000) (-15915745548 / 1000000000000), orderedInterval (-23948259614 / 1000000000000) (-23948259613 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2196581283114857 / 4000000000000) 3 (IntervalRat.scale (719 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-5147939254 / 1000000000000) (-5147939253 / 1000000000000), orderedInterval (-33652275966 / 1000000000000) (-33652275965 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2490689061283503 / 4000000000000) 3 (IntervalRat.scale (719 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (31622216154 / 1000000000000) (31622216325 / 1000000000000), orderedInterval (4711121070 / 1000000000000) (4711121241 / 1000000000000)))) (orderedInterval (7225516681 / 1000000000000) (7225516882 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2076476871910207 / 4000000000000) 3 (IntervalRat.scale (719 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-35004277907 / 1000000000000) (-35004277495 / 1000000000000), orderedInterval (-989010166 / 1000000000000) (-989009754 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1834630289558347 / 4000000000000) 3 (IntervalRat.scale (719 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (25939742457 / 1000000000000) (25939742458 / 1000000000000), orderedInterval (26713757627 / 1000000000000) (26713757628 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (531747366064353 / 800000000000) 3 (IntervalRat.scale (719 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-16129254342 / 1000000000000) (-16129254037 / 1000000000000), orderedInterval (26424725962 / 1000000000000) (26424726267 / 1000000000000)))) (orderedInterval (-1080204729 / 1000000000000) (-1080204551 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate488_chunkChecks3_2 :
    compactCertificate488.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1470841198864691 / 4000000000000) 3 (IntervalRat.scale (719 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-33330123125 / 1000000000000) (-33330123124 / 1000000000000), orderedInterval (-24862717947 / 1000000000000) (-24862717946 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1246848373397851 / 4000000000000) 3 (IntervalRat.scale (719 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-45003598380 / 1000000000000) (-45003598339 / 1000000000000), orderedInterval (-4051664816 / 1000000000000) (-4051664775 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (780219819046153 / 4000000000000) 3 (IntervalRat.scale (719 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (49864281925 / 1000000000000) (49864281926 / 1000000000000), orderedInterval (27753082754 / 1000000000000) (27753082755 / 1000000000000)))) (orderedInterval (-4525563022 / 1000000000000) (-4525562942 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (419604813576951 / 4000000000000) 3 (IntervalRat.scale (719 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-70413391428 / 1000000000000) (-70413383378 / 1000000000000), orderedInterval (33662273960 / 1000000000000) (33662282010 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1139308693623853 / 4000000000000) 3 (IntervalRat.scale (719 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (12737709900 / 1000000000000) (12737709999 / 1000000000000), orderedInterval (-45551061969 / 1000000000000) (-45551061870 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1555628618647181 / 4000000000000) 3 (IntervalRat.scale (719 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (5435082673 / 1000000000000) (5435082674 / 1000000000000), orderedInterval (40085487558 / 1000000000000) (40085487559 / 1000000000000)))) (orderedInterval (3389252673 / 1000000000000) (3389252718 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (657780180953847 / 4000000000000) 3 (IntervalRat.scale (719 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (59512672214 / 1000000000000) (59512674555 / 1000000000000), orderedInterval (-18334438489 / 1000000000000) (-18334436148 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2673839916713687 / 4000000000000) 3 (IntervalRat.scale (719 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-2649349082 / 1000000000000) (-2649349081 / 1000000000000), orderedInterval (-30744547081 / 1000000000000) (-30744547080 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1786001147757433 / 4000000000000) 3 (IntervalRat.scale (719 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (34902065892 / 1000000000000) (34902065894 / 1000000000000), orderedInterval (14370787928 / 1000000000000) (14370787929 / 1000000000000)))) (orderedInterval (-10938441570 / 1000000000000) (-10938441249 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate488_chunkChecks3 :
    compactCertificate488.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate488.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate488_chunkChecks3_0
    compactCertificate488_chunkChecks3_1 compactCertificate488_chunkChecks3_2

theorem compactCertificate488_chunkChecks4_0 :
    compactCertificate488.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (719 / 2) 4 (IntervalRat.scale (719 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (35367093657 / 1000000000000) (35367181666 / 1000000000000), orderedInterval (-22853015412 / 1000000000000) (-22852927404 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1059224291540819 / 4000000000000) 4 (IntervalRat.scale (719 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (48640270225 / 1000000000000) (48640270803 / 1000000000000), orderedInterval (-6273913550 / 1000000000000) (-6273912972 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (342531372747827 / 800000000000) 4 (IntervalRat.scale (719 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (38273541270 / 1000000000000) (38273542743 / 1000000000000), orderedInterval (-4734460012 / 1000000000000) (-4734458540 / 1000000000000)))) (orderedInterval (18617172711 / 1000000000000) (18617208009 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (309079006528633 / 4000000000000) 4 (IntervalRat.scale (719 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (42419681267 / 1000000000000) (42419686018 / 1000000000000), orderedInterval (-80521560259 / 1000000000000) (-80521555509 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (830229687094501 / 4000000000000) 4 (IntervalRat.scale (719 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (46515628616 / 1000000000000) (46515628617 / 1000000000000), orderedInterval (29946071888 / 1000000000000) (29946071889 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2254235103136017 / 4000000000000) 4 (IntervalRat.scale (719 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30577472411 / 1000000000000) (-30577410562 / 1000000000000), orderedInterval (13979227067 / 1000000000000) (13979288916 / 1000000000000)))) (orderedInterval (13294594767 / 1000000000000) (13294621570 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1660459374189721 / 4000000000000) 4 (IntervalRat.scale (719 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (36635820588 / 1000000000000) (36635820590 / 1000000000000), orderedInterval (13791152555 / 1000000000000) (13791152557 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2845225439297533 / 4000000000000) 4 (IntervalRat.scale (719 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (25949551249 / 1000000000000) (25949600890 / 1000000000000), orderedInterval (-14905178063 / 1000000000000) (-14905128421 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2095780180953847 / 4000000000000) 4 (IntervalRat.scale (719 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-2932640813 / 1000000000000) (-2932640812 / 1000000000000), orderedInterval (-34731202339 / 1000000000000) (-34731202338 / 1000000000000)))) (orderedInterval (-12581182516 / 1000000000000) (-12581158773 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate488_chunkChecks4_1 :
    compactCertificate488.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3215465751644281 / 4000000000000) 4 (IntervalRat.scale (719 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (11061427069 / 1000000000000) (11061427070 / 1000000000000), orderedInterval (25869598258 / 1000000000000) (25869598259 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1856450017281649 / 4000000000000) 4 (IntervalRat.scale (719 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-2149847049 / 1000000000000) (-2149847047 / 1000000000000), orderedInterval (36976249204 / 1000000000000) (36976249206 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3294303133251941 / 4000000000000) 4 (IntervalRat.scale (719 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (26502495010 / 1000000000000) (26502495088 / 1000000000000), orderedInterval (8387029058 / 1000000000000) (8387029135 / 1000000000000)))) (orderedInterval (54016533615 / 1000000000000) (54016537006 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3077965312847129 / 4000000000000) 4 (IntervalRat.scale (719 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-15915745549 / 1000000000000) (-15915745548 / 1000000000000), orderedInterval (-23948259614 / 1000000000000) (-23948259613 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2196581283114857 / 4000000000000) 4 (IntervalRat.scale (719 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-5147939254 / 1000000000000) (-5147939253 / 1000000000000), orderedInterval (-33652275966 / 1000000000000) (-33652275965 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2490689061283503 / 4000000000000) 4 (IntervalRat.scale (719 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (31622216154 / 1000000000000) (31622216325 / 1000000000000), orderedInterval (4711121070 / 1000000000000) (4711121241 / 1000000000000)))) (orderedInterval (1900305689 / 1000000000000) (1900306036 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2076476871910207 / 4000000000000) 4 (IntervalRat.scale (719 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-35004277907 / 1000000000000) (-35004277495 / 1000000000000), orderedInterval (-989010166 / 1000000000000) (-989009754 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1834630289558347 / 4000000000000) 4 (IntervalRat.scale (719 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (25939742457 / 1000000000000) (25939742458 / 1000000000000), orderedInterval (26713757627 / 1000000000000) (26713757628 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (531747366064353 / 800000000000) 4 (IntervalRat.scale (719 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-16129254342 / 1000000000000) (-16129254037 / 1000000000000), orderedInterval (26424725962 / 1000000000000) (26424726267 / 1000000000000)))) (orderedInterval (-10510414318 / 1000000000000) (-10510414025 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate488_chunkChecks4_2 :
    compactCertificate488.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1470841198864691 / 4000000000000) 4 (IntervalRat.scale (719 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-33330123125 / 1000000000000) (-33330123124 / 1000000000000), orderedInterval (-24862717947 / 1000000000000) (-24862717946 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1246848373397851 / 4000000000000) 4 (IntervalRat.scale (719 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-45003598380 / 1000000000000) (-45003598339 / 1000000000000), orderedInterval (-4051664816 / 1000000000000) (-4051664775 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (780219819046153 / 4000000000000) 4 (IntervalRat.scale (719 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (49864281925 / 1000000000000) (49864281926 / 1000000000000), orderedInterval (27753082754 / 1000000000000) (27753082755 / 1000000000000)))) (orderedInterval (7438539360 / 1000000000000) (7438539438 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (419604813576951 / 4000000000000) 4 (IntervalRat.scale (719 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-70413391428 / 1000000000000) (-70413383378 / 1000000000000), orderedInterval (33662273960 / 1000000000000) (33662282010 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1139308693623853 / 4000000000000) 4 (IntervalRat.scale (719 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (12737709900 / 1000000000000) (12737709999 / 1000000000000), orderedInterval (-45551061969 / 1000000000000) (-45551061870 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1555628618647181 / 4000000000000) 4 (IntervalRat.scale (719 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (5435082673 / 1000000000000) (5435082674 / 1000000000000), orderedInterval (40085487558 / 1000000000000) (40085487559 / 1000000000000)))) (orderedInterval (-693775211 / 1000000000000) (-693775167 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (657780180953847 / 4000000000000) 4 (IntervalRat.scale (719 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (59512672214 / 1000000000000) (59512674555 / 1000000000000), orderedInterval (-18334438489 / 1000000000000) (-18334436148 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2673839916713687 / 4000000000000) 4 (IntervalRat.scale (719 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-2649349082 / 1000000000000) (-2649349081 / 1000000000000), orderedInterval (-30744547081 / 1000000000000) (-30744547080 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1786001147757433 / 4000000000000) 4 (IntervalRat.scale (719 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (34902065892 / 1000000000000) (34902065894 / 1000000000000), orderedInterval (14370787928 / 1000000000000) (14370787929 / 1000000000000)))) (orderedInterval (-12927876934 / 1000000000000) (-12927876420 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate488_chunkChecks4 :
    compactCertificate488.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate488.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate488_chunkChecks4_0
    compactCertificate488_chunkChecks4_1 compactCertificate488_chunkChecks4_2

theorem compactCertificate488_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate488.chunkCheck r b = true :=
  compactCertificate488.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate488_chunkChecks0
    · exact compactCertificate488_chunkChecks1
    · exact compactCertificate488_chunkChecks2
    · exact compactCertificate488_chunkChecks3
    · exact compactCertificate488_chunkChecks4)

theorem compactCertificate488_coefficient0 :
    compactCertificate488.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate488_coefficient1 :
    compactCertificate488.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate488_coefficient2 :
    compactCertificate488.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate488_coefficient3 :
    compactCertificate488.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate488_coefficient4 :
    compactCertificate488.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate488_coefficients : ∀ r : Fin 5,
    compactCertificate488.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate488_coefficient0
  · exact compactCertificate488_coefficient1
  · exact compactCertificate488_coefficient2
  · exact compactCertificate488_coefficient3
  · exact compactCertificate488_coefficient4

theorem compactCertificate488_lower : (1 : ℚ) ≤ compactCertificate488.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate488, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate488_proves {t : ℝ} (ht : t ∈ compactCertificate488.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate488.proves compactCertificate488_states compactCertificate488_chunks
    compactCertificate488_coefficients compactCertificate488_lower ht

end Erdos232
