/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate420 : CompactCertificate where
  left := 291
  right := 292
  center := 583 / 2
  grid := fun i =>
    match i.val with
    | 0 => 93
    | 1 => 68
    | 2 => 111
    | 3 => 20
    | 4 => 54
    | 5 => 146
    | 6 => 107
    | 7 => 184
    | 8 => 135
    | 9 => 208
    | 10 => 120
    | 11 => 213
    | 12 => 199
    | 13 => 142
    | 14 => 161
    | 15 => 134
    | 16 => 118
    | 17 => 172
    | 18 => 95
    | 19 => 80
    | 20 => 50
    | 21 => 27
    | 22 => 74
    | 23 => 100
    | 24 => 42
    | 25 => 173
    | _ => 115
  point := fun i =>
    match i.val with
    | 0 => 583 / 2
    | 1 => 858870322626283 / 4000000000000
    | 2 => 277741015732939 / 800000000000
    | 3 => 250616218089281 / 4000000000000
    | 4 => 673190413874957 / 4000000000000
    | 5 => 1827842927855769 / 4000000000000
    | 6 => 1346380827750497 / 4000000000000
    | 7 => 2307046496676581 / 4000000000000
    | 8 => 1699360007644079 / 4000000000000
    | 9 => 2607255261764417 / 4000000000000
    | 10 => 1505299527225593 / 4000000000000
    | 11 => 2671180426545037 / 4000000000000
    | 12 => 2495763250889953 / 4000000000000
    | 13 => 1781094420105649 / 4000000000000
    | 14 => 2019571241624871 / 4000000000000
    | 15 => 1683707950380599 / 4000000000000
    | 16 => 1487607035900579 / 4000000000000
    | 17 => 431166501273321 / 800000000000
    | 18 => 1192629233571787 / 4000000000000
    | 19 => 1011005009305907 / 4000000000000
    | 20 => 632639992355921 / 4000000000000
    | 21 => 340235891954607 / 4000000000000
    | 22 => 923806631964821 / 4000000000000
    | 23 => 1261378977289717 / 4000000000000
    | 24 => 533360007644079 / 4000000000000
    | 25 => 2168078819810959 / 4000000000000
    | _ => 1448176174050881 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-5448411709 / 1000000000000) (-5448411708 / 1000000000000), orderedInterval (-46404685468 / 1000000000000) (-46404685467 / 1000000000000))
    | 1 => (orderedInterval (51965619746 / 1000000000000) (51965623094 / 1000000000000), orderedInterval (-16383987382 / 1000000000000) (-16383984033 / 1000000000000))
    | 2 => (orderedInterval (29360143253 / 1000000000000) (29360161377 / 1000000000000), orderedInterval (-31214222253 / 1000000000000) (-31214204129 / 1000000000000))
    | 3 => (orderedInterval (57381088714 / 1000000000000) (57381088715 / 1000000000000), orderedInterval (82417893164 / 1000000000000) (82417893165 / 1000000000000))
    | 4 => (orderedInterval (-32864723663 / 1000000000000) (-32864717020 / 1000000000000), orderedInterval (52084362013 / 1000000000000) (52084368656 / 1000000000000))
    | 5 => (orderedInterval (-29846082855 / 1000000000000) (-29846030691 / 1000000000000), orderedInterval (22446318290 / 1000000000000) (22446370453 / 1000000000000))
    | 6 => (orderedInterval (-40985883007 / 1000000000000) (-40985883006 / 1000000000000), orderedInterval (-14482398869 / 1000000000000) (-14482398867 / 1000000000000))
    | 7 => (orderedInterval (-16109763297 / 1000000000000) (-16109762982 / 1000000000000), orderedInterval (29070099456 / 1000000000000) (29070099771 / 1000000000000))
    | 8 => (orderedInterval (-38639071000 / 1000000000000) (-38639070856 / 1000000000000), orderedInterval (-2302753443 / 1000000000000) (-2302753298 / 1000000000000))
    | 9 => (orderedInterval (-23525392905 / 1000000000000) (-23525382557 / 1000000000000), orderedInterval (20590976549 / 1000000000000) (20590986897 / 1000000000000))
    | 10 => (orderedInterval (4875954944 / 1000000000000) (4875954945 / 1000000000000), orderedInterval (40833483903 / 1000000000000) (40833483904 / 1000000000000))
    | 11 => (orderedInterval (16892719157 / 1000000000000) (16892719600 / 1000000000000), orderedInterval (-25857418756 / 1000000000000) (-25857418313 / 1000000000000))
    | 12 => (orderedInterval (13920538780 / 1000000000000) (13920538888 / 1000000000000), orderedInterval (-28760756679 / 1000000000000) (-28760756571 / 1000000000000))
    | 13 => (orderedInterval (-1792901734 / 1000000000000) (-1792901733 / 1000000000000), orderedInterval (37771227880 / 1000000000000) (37771227881 / 1000000000000))
    | 14 => (orderedInterval (4196450941 / 1000000000000) (4196450943 / 1000000000000), orderedInterval (-35264491112 / 1000000000000) (-35264491110 / 1000000000000))
    | 15 => (orderedInterval (26184844166 / 1000000000000) (26184844167 / 1000000000000), orderedInterval (28722631822 / 1000000000000) (28722631823 / 1000000000000))
    | 16 => (orderedInterval (37976196520 / 1000000000000) (37976218018 / 1000000000000), orderedInterval (-16470632796 / 1000000000000) (-16470611299 / 1000000000000))
    | 17 => (orderedInterval (-19706807127 / 1000000000000) (-19706805694 / 1000000000000), orderedInterval (28175811100 / 1000000000000) (28175812533 / 1000000000000))
    | 18 => (orderedInterval (-21786831695 / 1000000000000) (-21786831694 / 1000000000000), orderedInterval (-40712899547 / 1000000000000) (-40712899546 / 1000000000000))
    | 19 => (orderedInterval (40316328372 / 1000000000000) (40316425117 / 1000000000000), orderedInterval (-29968734251 / 1000000000000) (-29968637506 / 1000000000000))
    | 20 => (orderedInterval (60718528827 / 1000000000000) (60718531039 / 1000000000000), orderedInterval (-18587777236 / 1000000000000) (-18587775023 / 1000000000000))
    | 21 => (orderedInterval (-73713024509 / 1000000000000) (-73713024508 / 1000000000000), orderedInterval (-44852284022 / 1000000000000) (-44852284021 / 1000000000000))
    | 22 => (orderedInterval (-35453712688 / 1000000000000) (-35453685147 / 1000000000000), orderedInterval (38800666194 / 1000000000000) (38800693735 / 1000000000000))
    | 23 => (orderedInterval (41389789802 / 1000000000000) (41389804906 / 1000000000000), orderedInterval (-17549586106 / 1000000000000) (-17549571002 / 1000000000000))
    | 24 => (orderedInterval (56762447257 / 1000000000000) (56762491247 / 1000000000000), orderedInterval (-39613624575 / 1000000000000) (-39613580585 / 1000000000000))
    | 25 => (orderedInterval (21832397677 / 1000000000000) (21832401125 / 1000000000000), orderedInterval (-26437540213 / 1000000000000) (-26437536765 / 1000000000000))
    | _ => (orderedInterval (-41920358682 / 1000000000000) (-41920358529 / 1000000000000), orderedInterval (-984255407 / 1000000000000) (-984255254 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (47545760 / 1000000000000) (47546876 / 1000000000000)
      | 1 => orderedInterval (299251017 / 1000000000000) (299255004 / 1000000000000)
      | 2 => orderedInterval (-436940574 / 1000000000000) (-436940544 / 1000000000000)
      | 3 => orderedInterval (6942844074 / 1000000000000) (6942846092 / 1000000000000)
      | 4 => orderedInterval (-442087089 / 1000000000000) (-442087051 / 1000000000000)
      | 5 => orderedInterval (-2375450941 / 1000000000000) (-2375449646 / 1000000000000)
      | 6 => orderedInterval (3178349959 / 1000000000000) (3178355581 / 1000000000000)
      | 7 => orderedInterval (-1006615411 / 1000000000000) (-1006613593 / 1000000000000)
      | _ => orderedInterval (6430357643 / 1000000000000) (6430358299 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-20687183400 / 1000000000000) (-20687182086 / 1000000000000)
      | 1 => orderedInterval (-1595704839 / 1000000000000) (-1595698846 / 1000000000000)
      | 2 => orderedInterval (-1855197683 / 1000000000000) (-1855197630 / 1000000000000)
      | 3 => orderedInterval (-12696277207 / 1000000000000) (-12696272712 / 1000000000000)
      | 4 => orderedInterval (6876410824 / 1000000000000) (6876410885 / 1000000000000)
      | 5 => orderedInterval (3015309903 / 1000000000000) (3015311581 / 1000000000000)
      | 6 => orderedInterval (7800773165 / 1000000000000) (7800778021 / 1000000000000)
      | 7 => orderedInterval (999242971 / 1000000000000) (999244750 / 1000000000000)
      | _ => orderedInterval (4121707289 / 1000000000000) (4121708082 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-476076584 / 1000000000000) (-476075026 / 1000000000000)
      | 1 => orderedInterval (-4779822402 / 1000000000000) (-4779813132 / 1000000000000)
      | 2 => orderedInterval (44656837 / 1000000000000) (44656934 / 1000000000000)
      | 3 => orderedInterval (-34062445821 / 1000000000000) (-34062435769 / 1000000000000)
      | 4 => orderedInterval (1587093395 / 1000000000000) (1587093498 / 1000000000000)
      | 5 => orderedInterval (4621473287 / 1000000000000) (4621475481 / 1000000000000)
      | 6 => orderedInterval (-2537594173 / 1000000000000) (-2537589953 / 1000000000000)
      | 7 => orderedInterval (3088026232 / 1000000000000) (3088028016 / 1000000000000)
      | _ => orderedInterval (-6074120994 / 1000000000000) (-6074119754 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (21550059452 / 1000000000000) (21550061298 / 1000000000000)
      | 1 => orderedInterval (5806406743 / 1000000000000) (5806421189 / 1000000000000)
      | 2 => orderedInterval (7117404312 / 1000000000000) (7117404490 / 1000000000000)
      | 3 => orderedInterval (78707367501 / 1000000000000) (78707389974 / 1000000000000)
      | 4 => orderedInterval (-18754944935 / 1000000000000) (-18754944757 / 1000000000000)
      | 5 => orderedInterval (-7531547357 / 1000000000000) (-7531544470 / 1000000000000)
      | 6 => orderedInterval (-7966232483 / 1000000000000) (-7966228824 / 1000000000000)
      | 7 => orderedInterval (-1296147784 / 1000000000000) (-1296145969 / 1000000000000)
      | _ => orderedInterval (-14145237588 / 1000000000000) (-14145235441 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (1301717120 / 1000000000000) (1301719318 / 1000000000000)
      | 1 => orderedInterval (12638548556 / 1000000000000) (12638571202 / 1000000000000)
      | 2 => orderedInterval (3353307476 / 1000000000000) (3353307812 / 1000000000000)
      | 3 => orderedInterval (171110398340 / 1000000000000) (171110448686 / 1000000000000)
      | 4 => orderedInterval (-6260545748 / 1000000000000) (-6260545432 / 1000000000000)
      | 5 => orderedInterval (-10287993222 / 1000000000000) (-10287989368 / 1000000000000)
      | 6 => orderedInterval (2748998136 / 1000000000000) (2749001324 / 1000000000000)
      | 7 => orderedInterval (-4008679252 / 1000000000000) (-4008677374 / 1000000000000)
      | _ => orderedInterval (-2416395963 / 1000000000000) (-2416392100 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (12637254438 / 1000000000000) (12637271018 / 1000000000000)
    | 1 => orderedInterval (-14020918977 / 1000000000000) (-14020897955 / 1000000000000)
    | 2 => orderedInterval (-38588810223 / 1000000000000) (-38588779705 / 1000000000000)
    | 3 => orderedInterval (63487127861 / 1000000000000) (63487177490 / 1000000000000)
    | _ => orderedInterval (168179355443 / 1000000000000) (168179444068 / 1000000000000)

theorem compactCertificate420_stateChecks0 :
    compactCertificate420.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 93 12 (583 / 2)) (orderedInterval (-5448411709 / 1000000000000) (-5448411708 / 1000000000000), orderedInterval (-46404685468 / 1000000000000) (-46404685467 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (858870322626283 / 4000000000000)) (orderedInterval (51965619746 / 1000000000000) (51965623094 / 1000000000000), orderedInterval (-16383987382 / 1000000000000) (-16383984033 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 111 12 (277741015732939 / 800000000000)) (orderedInterval (29360143253 / 1000000000000) (29360161377 / 1000000000000), orderedInterval (-31214222253 / 1000000000000) (-31214204129 / 1000000000000))) = true
  rfl'

theorem compactCertificate420_stateChecks1 :
    compactCertificate420.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 20 12 (250616218089281 / 4000000000000)) (orderedInterval (57381088714 / 1000000000000) (57381088715 / 1000000000000), orderedInterval (82417893164 / 1000000000000) (82417893165 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (673190413874957 / 4000000000000)) (orderedInterval (-32864723663 / 1000000000000) (-32864717020 / 1000000000000), orderedInterval (52084362013 / 1000000000000) (52084368656 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 146 12 (1827842927855769 / 4000000000000)) (orderedInterval (-29846082855 / 1000000000000) (-29846030691 / 1000000000000), orderedInterval (22446318290 / 1000000000000) (22446370453 / 1000000000000))) = true
  rfl'

theorem compactCertificate420_stateChecks2 :
    compactCertificate420.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 107 12 (1346380827750497 / 4000000000000)) (orderedInterval (-40985883007 / 1000000000000) (-40985883006 / 1000000000000), orderedInterval (-14482398869 / 1000000000000) (-14482398867 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 184 12 (2307046496676581 / 4000000000000)) (orderedInterval (-16109763297 / 1000000000000) (-16109762982 / 1000000000000), orderedInterval (29070099456 / 1000000000000) (29070099771 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 135 12 (1699360007644079 / 4000000000000)) (orderedInterval (-38639071000 / 1000000000000) (-38639070856 / 1000000000000), orderedInterval (-2302753443 / 1000000000000) (-2302753298 / 1000000000000))) = true
  rfl'

theorem compactCertificate420_stateChecks3 :
    compactCertificate420.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 208 12 (2607255261764417 / 4000000000000)) (orderedInterval (-23525392905 / 1000000000000) (-23525382557 / 1000000000000), orderedInterval (20590976549 / 1000000000000) (20590986897 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 120 12 (1505299527225593 / 4000000000000)) (orderedInterval (4875954944 / 1000000000000) (4875954945 / 1000000000000), orderedInterval (40833483903 / 1000000000000) (40833483904 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 213 12 (2671180426545037 / 4000000000000)) (orderedInterval (16892719157 / 1000000000000) (16892719600 / 1000000000000), orderedInterval (-25857418756 / 1000000000000) (-25857418313 / 1000000000000))) = true
  rfl'

theorem compactCertificate420_stateChecks4 :
    compactCertificate420.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 199 12 (2495763250889953 / 4000000000000)) (orderedInterval (13920538780 / 1000000000000) (13920538888 / 1000000000000), orderedInterval (-28760756679 / 1000000000000) (-28760756571 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 142 12 (1781094420105649 / 4000000000000)) (orderedInterval (-1792901734 / 1000000000000) (-1792901733 / 1000000000000), orderedInterval (37771227880 / 1000000000000) (37771227881 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 161 12 (2019571241624871 / 4000000000000)) (orderedInterval (4196450941 / 1000000000000) (4196450943 / 1000000000000), orderedInterval (-35264491112 / 1000000000000) (-35264491110 / 1000000000000))) = true
  rfl'

theorem compactCertificate420_stateChecks5 :
    compactCertificate420.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 134 12 (1683707950380599 / 4000000000000)) (orderedInterval (26184844166 / 1000000000000) (26184844167 / 1000000000000), orderedInterval (28722631822 / 1000000000000) (28722631823 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 118 12 (1487607035900579 / 4000000000000)) (orderedInterval (37976196520 / 1000000000000) (37976218018 / 1000000000000), orderedInterval (-16470632796 / 1000000000000) (-16470611299 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 172 12 (431166501273321 / 800000000000)) (orderedInterval (-19706807127 / 1000000000000) (-19706805694 / 1000000000000), orderedInterval (28175811100 / 1000000000000) (28175812533 / 1000000000000))) = true
  rfl'

theorem compactCertificate420_stateChecks6 :
    compactCertificate420.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 95 12 (1192629233571787 / 4000000000000)) (orderedInterval (-21786831695 / 1000000000000) (-21786831694 / 1000000000000), orderedInterval (-40712899547 / 1000000000000) (-40712899546 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 80 12 (1011005009305907 / 4000000000000)) (orderedInterval (40316328372 / 1000000000000) (40316425117 / 1000000000000), orderedInterval (-29968734251 / 1000000000000) (-29968637506 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 50 12 (632639992355921 / 4000000000000)) (orderedInterval (60718528827 / 1000000000000) (60718531039 / 1000000000000), orderedInterval (-18587777236 / 1000000000000) (-18587775023 / 1000000000000))) = true
  rfl'

theorem compactCertificate420_stateChecks7 :
    compactCertificate420.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 27 12 (340235891954607 / 4000000000000)) (orderedInterval (-73713024509 / 1000000000000) (-73713024508 / 1000000000000), orderedInterval (-44852284022 / 1000000000000) (-44852284021 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 74 12 (923806631964821 / 4000000000000)) (orderedInterval (-35453712688 / 1000000000000) (-35453685147 / 1000000000000), orderedInterval (38800666194 / 1000000000000) (38800693735 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 100 12 (1261378977289717 / 4000000000000)) (orderedInterval (41389789802 / 1000000000000) (41389804906 / 1000000000000), orderedInterval (-17549586106 / 1000000000000) (-17549571002 / 1000000000000))) = true
  rfl'

theorem compactCertificate420_stateChecks8 :
    compactCertificate420.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 42 12 (533360007644079 / 4000000000000)) (orderedInterval (56762447257 / 1000000000000) (56762491247 / 1000000000000), orderedInterval (-39613624575 / 1000000000000) (-39613580585 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 173 12 (2168078819810959 / 4000000000000)) (orderedInterval (21832397677 / 1000000000000) (21832401125 / 1000000000000), orderedInterval (-26437540213 / 1000000000000) (-26437536765 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 115 12 (1448176174050881 / 4000000000000)) (orderedInterval (-41920358682 / 1000000000000) (-41920358529 / 1000000000000), orderedInterval (-984255407 / 1000000000000) (-984255254 / 1000000000000))) = true
  rfl'

theorem compactCertificate420_states : ∀ j,
    BesselStateValid (compactCertificate420.point j) (compactCertificate420.state j) :=
  compactCertificate420.statesValid_of_checks3 compactCertificate420_stateChecks0
    compactCertificate420_stateChecks1 compactCertificate420_stateChecks2
    compactCertificate420_stateChecks3 compactCertificate420_stateChecks4
    compactCertificate420_stateChecks5 compactCertificate420_stateChecks6
    compactCertificate420_stateChecks7 compactCertificate420_stateChecks8

theorem compactCertificate420_chunkChecks0_0 :
    compactCertificate420.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (583 / 2) 0 (IntervalRat.scale (583 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-5448411709 / 1000000000000) (-5448411708 / 1000000000000), orderedInterval (-46404685468 / 1000000000000) (-46404685467 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (858870322626283 / 4000000000000) 0 (IntervalRat.scale (583 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (51965619746 / 1000000000000) (51965623094 / 1000000000000), orderedInterval (-16383987382 / 1000000000000) (-16383984033 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (277741015732939 / 800000000000) 0 (IntervalRat.scale (583 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (29360143253 / 1000000000000) (29360161377 / 1000000000000), orderedInterval (-31214222253 / 1000000000000) (-31214204129 / 1000000000000)))) (orderedInterval (47545760 / 1000000000000) (47546876 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (250616218089281 / 4000000000000) 0 (IntervalRat.scale (583 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (57381088714 / 1000000000000) (57381088715 / 1000000000000), orderedInterval (82417893164 / 1000000000000) (82417893165 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (673190413874957 / 4000000000000) 0 (IntervalRat.scale (583 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-32864723663 / 1000000000000) (-32864717020 / 1000000000000), orderedInterval (52084362013 / 1000000000000) (52084368656 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1827842927855769 / 4000000000000) 0 (IntervalRat.scale (583 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29846082855 / 1000000000000) (-29846030691 / 1000000000000), orderedInterval (22446318290 / 1000000000000) (22446370453 / 1000000000000)))) (orderedInterval (299251017 / 1000000000000) (299255004 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1346380827750497 / 4000000000000) 0 (IntervalRat.scale (583 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-40985883007 / 1000000000000) (-40985883006 / 1000000000000), orderedInterval (-14482398869 / 1000000000000) (-14482398867 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2307046496676581 / 4000000000000) 0 (IntervalRat.scale (583 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-16109763297 / 1000000000000) (-16109762982 / 1000000000000), orderedInterval (29070099456 / 1000000000000) (29070099771 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1699360007644079 / 4000000000000) 0 (IntervalRat.scale (583 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-38639071000 / 1000000000000) (-38639070856 / 1000000000000), orderedInterval (-2302753443 / 1000000000000) (-2302753298 / 1000000000000)))) (orderedInterval (-436940574 / 1000000000000) (-436940544 / 1000000000000))) = true
  rfl'

theorem compactCertificate420_chunkChecks0_1 :
    compactCertificate420.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2607255261764417 / 4000000000000) 0 (IntervalRat.scale (583 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-23525392905 / 1000000000000) (-23525382557 / 1000000000000), orderedInterval (20590976549 / 1000000000000) (20590986897 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1505299527225593 / 4000000000000) 0 (IntervalRat.scale (583 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (4875954944 / 1000000000000) (4875954945 / 1000000000000), orderedInterval (40833483903 / 1000000000000) (40833483904 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2671180426545037 / 4000000000000) 0 (IntervalRat.scale (583 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (16892719157 / 1000000000000) (16892719600 / 1000000000000), orderedInterval (-25857418756 / 1000000000000) (-25857418313 / 1000000000000)))) (orderedInterval (6942844074 / 1000000000000) (6942846092 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2495763250889953 / 4000000000000) 0 (IntervalRat.scale (583 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (13920538780 / 1000000000000) (13920538888 / 1000000000000), orderedInterval (-28760756679 / 1000000000000) (-28760756571 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1781094420105649 / 4000000000000) 0 (IntervalRat.scale (583 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-1792901734 / 1000000000000) (-1792901733 / 1000000000000), orderedInterval (37771227880 / 1000000000000) (37771227881 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2019571241624871 / 4000000000000) 0 (IntervalRat.scale (583 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (4196450941 / 1000000000000) (4196450943 / 1000000000000), orderedInterval (-35264491112 / 1000000000000) (-35264491110 / 1000000000000)))) (orderedInterval (-442087089 / 1000000000000) (-442087051 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1683707950380599 / 4000000000000) 0 (IntervalRat.scale (583 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (26184844166 / 1000000000000) (26184844167 / 1000000000000), orderedInterval (28722631822 / 1000000000000) (28722631823 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1487607035900579 / 4000000000000) 0 (IntervalRat.scale (583 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (37976196520 / 1000000000000) (37976218018 / 1000000000000), orderedInterval (-16470632796 / 1000000000000) (-16470611299 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (431166501273321 / 800000000000) 0 (IntervalRat.scale (583 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-19706807127 / 1000000000000) (-19706805694 / 1000000000000), orderedInterval (28175811100 / 1000000000000) (28175812533 / 1000000000000)))) (orderedInterval (-2375450941 / 1000000000000) (-2375449646 / 1000000000000))) = true
  rfl'

theorem compactCertificate420_chunkChecks0_2 :
    compactCertificate420.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1192629233571787 / 4000000000000) 0 (IntervalRat.scale (583 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-21786831695 / 1000000000000) (-21786831694 / 1000000000000), orderedInterval (-40712899547 / 1000000000000) (-40712899546 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1011005009305907 / 4000000000000) 0 (IntervalRat.scale (583 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (40316328372 / 1000000000000) (40316425117 / 1000000000000), orderedInterval (-29968734251 / 1000000000000) (-29968637506 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (632639992355921 / 4000000000000) 0 (IntervalRat.scale (583 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (60718528827 / 1000000000000) (60718531039 / 1000000000000), orderedInterval (-18587777236 / 1000000000000) (-18587775023 / 1000000000000)))) (orderedInterval (3178349959 / 1000000000000) (3178355581 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (340235891954607 / 4000000000000) 0 (IntervalRat.scale (583 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-73713024509 / 1000000000000) (-73713024508 / 1000000000000), orderedInterval (-44852284022 / 1000000000000) (-44852284021 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (923806631964821 / 4000000000000) 0 (IntervalRat.scale (583 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-35453712688 / 1000000000000) (-35453685147 / 1000000000000), orderedInterval (38800666194 / 1000000000000) (38800693735 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1261378977289717 / 4000000000000) 0 (IntervalRat.scale (583 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (41389789802 / 1000000000000) (41389804906 / 1000000000000), orderedInterval (-17549586106 / 1000000000000) (-17549571002 / 1000000000000)))) (orderedInterval (-1006615411 / 1000000000000) (-1006613593 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (533360007644079 / 4000000000000) 0 (IntervalRat.scale (583 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (56762447257 / 1000000000000) (56762491247 / 1000000000000), orderedInterval (-39613624575 / 1000000000000) (-39613580585 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2168078819810959 / 4000000000000) 0 (IntervalRat.scale (583 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (21832397677 / 1000000000000) (21832401125 / 1000000000000), orderedInterval (-26437540213 / 1000000000000) (-26437536765 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1448176174050881 / 4000000000000) 0 (IntervalRat.scale (583 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-41920358682 / 1000000000000) (-41920358529 / 1000000000000), orderedInterval (-984255407 / 1000000000000) (-984255254 / 1000000000000)))) (orderedInterval (6430357643 / 1000000000000) (6430358299 / 1000000000000))) = true
  rfl'

theorem compactCertificate420_chunkChecks0 :
    compactCertificate420.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate420.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate420_chunkChecks0_0
    compactCertificate420_chunkChecks0_1 compactCertificate420_chunkChecks0_2

theorem compactCertificate420_chunkChecks1_0 :
    compactCertificate420.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (583 / 2) 1 (IntervalRat.scale (583 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-5448411709 / 1000000000000) (-5448411708 / 1000000000000), orderedInterval (-46404685468 / 1000000000000) (-46404685467 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (858870322626283 / 4000000000000) 1 (IntervalRat.scale (583 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (51965619746 / 1000000000000) (51965623094 / 1000000000000), orderedInterval (-16383987382 / 1000000000000) (-16383984033 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (277741015732939 / 800000000000) 1 (IntervalRat.scale (583 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (29360143253 / 1000000000000) (29360161377 / 1000000000000), orderedInterval (-31214222253 / 1000000000000) (-31214204129 / 1000000000000)))) (orderedInterval (-20687183400 / 1000000000000) (-20687182086 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (250616218089281 / 4000000000000) 1 (IntervalRat.scale (583 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (57381088714 / 1000000000000) (57381088715 / 1000000000000), orderedInterval (82417893164 / 1000000000000) (82417893165 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (673190413874957 / 4000000000000) 1 (IntervalRat.scale (583 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-32864723663 / 1000000000000) (-32864717020 / 1000000000000), orderedInterval (52084362013 / 1000000000000) (52084368656 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1827842927855769 / 4000000000000) 1 (IntervalRat.scale (583 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29846082855 / 1000000000000) (-29846030691 / 1000000000000), orderedInterval (22446318290 / 1000000000000) (22446370453 / 1000000000000)))) (orderedInterval (-1595704839 / 1000000000000) (-1595698846 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1346380827750497 / 4000000000000) 1 (IntervalRat.scale (583 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-40985883007 / 1000000000000) (-40985883006 / 1000000000000), orderedInterval (-14482398869 / 1000000000000) (-14482398867 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2307046496676581 / 4000000000000) 1 (IntervalRat.scale (583 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-16109763297 / 1000000000000) (-16109762982 / 1000000000000), orderedInterval (29070099456 / 1000000000000) (29070099771 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1699360007644079 / 4000000000000) 1 (IntervalRat.scale (583 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-38639071000 / 1000000000000) (-38639070856 / 1000000000000), orderedInterval (-2302753443 / 1000000000000) (-2302753298 / 1000000000000)))) (orderedInterval (-1855197683 / 1000000000000) (-1855197630 / 1000000000000))) = true
  rfl'

theorem compactCertificate420_chunkChecks1_1 :
    compactCertificate420.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2607255261764417 / 4000000000000) 1 (IntervalRat.scale (583 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-23525392905 / 1000000000000) (-23525382557 / 1000000000000), orderedInterval (20590976549 / 1000000000000) (20590986897 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1505299527225593 / 4000000000000) 1 (IntervalRat.scale (583 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (4875954944 / 1000000000000) (4875954945 / 1000000000000), orderedInterval (40833483903 / 1000000000000) (40833483904 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2671180426545037 / 4000000000000) 1 (IntervalRat.scale (583 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (16892719157 / 1000000000000) (16892719600 / 1000000000000), orderedInterval (-25857418756 / 1000000000000) (-25857418313 / 1000000000000)))) (orderedInterval (-12696277207 / 1000000000000) (-12696272712 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2495763250889953 / 4000000000000) 1 (IntervalRat.scale (583 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (13920538780 / 1000000000000) (13920538888 / 1000000000000), orderedInterval (-28760756679 / 1000000000000) (-28760756571 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1781094420105649 / 4000000000000) 1 (IntervalRat.scale (583 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-1792901734 / 1000000000000) (-1792901733 / 1000000000000), orderedInterval (37771227880 / 1000000000000) (37771227881 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2019571241624871 / 4000000000000) 1 (IntervalRat.scale (583 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (4196450941 / 1000000000000) (4196450943 / 1000000000000), orderedInterval (-35264491112 / 1000000000000) (-35264491110 / 1000000000000)))) (orderedInterval (6876410824 / 1000000000000) (6876410885 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1683707950380599 / 4000000000000) 1 (IntervalRat.scale (583 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (26184844166 / 1000000000000) (26184844167 / 1000000000000), orderedInterval (28722631822 / 1000000000000) (28722631823 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1487607035900579 / 4000000000000) 1 (IntervalRat.scale (583 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (37976196520 / 1000000000000) (37976218018 / 1000000000000), orderedInterval (-16470632796 / 1000000000000) (-16470611299 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (431166501273321 / 800000000000) 1 (IntervalRat.scale (583 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-19706807127 / 1000000000000) (-19706805694 / 1000000000000), orderedInterval (28175811100 / 1000000000000) (28175812533 / 1000000000000)))) (orderedInterval (3015309903 / 1000000000000) (3015311581 / 1000000000000))) = true
  rfl'

theorem compactCertificate420_chunkChecks1_2 :
    compactCertificate420.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1192629233571787 / 4000000000000) 1 (IntervalRat.scale (583 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-21786831695 / 1000000000000) (-21786831694 / 1000000000000), orderedInterval (-40712899547 / 1000000000000) (-40712899546 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1011005009305907 / 4000000000000) 1 (IntervalRat.scale (583 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (40316328372 / 1000000000000) (40316425117 / 1000000000000), orderedInterval (-29968734251 / 1000000000000) (-29968637506 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (632639992355921 / 4000000000000) 1 (IntervalRat.scale (583 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (60718528827 / 1000000000000) (60718531039 / 1000000000000), orderedInterval (-18587777236 / 1000000000000) (-18587775023 / 1000000000000)))) (orderedInterval (7800773165 / 1000000000000) (7800778021 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (340235891954607 / 4000000000000) 1 (IntervalRat.scale (583 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-73713024509 / 1000000000000) (-73713024508 / 1000000000000), orderedInterval (-44852284022 / 1000000000000) (-44852284021 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (923806631964821 / 4000000000000) 1 (IntervalRat.scale (583 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-35453712688 / 1000000000000) (-35453685147 / 1000000000000), orderedInterval (38800666194 / 1000000000000) (38800693735 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1261378977289717 / 4000000000000) 1 (IntervalRat.scale (583 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (41389789802 / 1000000000000) (41389804906 / 1000000000000), orderedInterval (-17549586106 / 1000000000000) (-17549571002 / 1000000000000)))) (orderedInterval (999242971 / 1000000000000) (999244750 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (533360007644079 / 4000000000000) 1 (IntervalRat.scale (583 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (56762447257 / 1000000000000) (56762491247 / 1000000000000), orderedInterval (-39613624575 / 1000000000000) (-39613580585 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2168078819810959 / 4000000000000) 1 (IntervalRat.scale (583 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (21832397677 / 1000000000000) (21832401125 / 1000000000000), orderedInterval (-26437540213 / 1000000000000) (-26437536765 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1448176174050881 / 4000000000000) 1 (IntervalRat.scale (583 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-41920358682 / 1000000000000) (-41920358529 / 1000000000000), orderedInterval (-984255407 / 1000000000000) (-984255254 / 1000000000000)))) (orderedInterval (4121707289 / 1000000000000) (4121708082 / 1000000000000))) = true
  rfl'

theorem compactCertificate420_chunkChecks1 :
    compactCertificate420.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate420.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate420_chunkChecks1_0
    compactCertificate420_chunkChecks1_1 compactCertificate420_chunkChecks1_2

theorem compactCertificate420_chunkChecks2_0 :
    compactCertificate420.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (583 / 2) 2 (IntervalRat.scale (583 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-5448411709 / 1000000000000) (-5448411708 / 1000000000000), orderedInterval (-46404685468 / 1000000000000) (-46404685467 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (858870322626283 / 4000000000000) 2 (IntervalRat.scale (583 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (51965619746 / 1000000000000) (51965623094 / 1000000000000), orderedInterval (-16383987382 / 1000000000000) (-16383984033 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (277741015732939 / 800000000000) 2 (IntervalRat.scale (583 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (29360143253 / 1000000000000) (29360161377 / 1000000000000), orderedInterval (-31214222253 / 1000000000000) (-31214204129 / 1000000000000)))) (orderedInterval (-476076584 / 1000000000000) (-476075026 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (250616218089281 / 4000000000000) 2 (IntervalRat.scale (583 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (57381088714 / 1000000000000) (57381088715 / 1000000000000), orderedInterval (82417893164 / 1000000000000) (82417893165 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (673190413874957 / 4000000000000) 2 (IntervalRat.scale (583 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-32864723663 / 1000000000000) (-32864717020 / 1000000000000), orderedInterval (52084362013 / 1000000000000) (52084368656 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1827842927855769 / 4000000000000) 2 (IntervalRat.scale (583 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29846082855 / 1000000000000) (-29846030691 / 1000000000000), orderedInterval (22446318290 / 1000000000000) (22446370453 / 1000000000000)))) (orderedInterval (-4779822402 / 1000000000000) (-4779813132 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1346380827750497 / 4000000000000) 2 (IntervalRat.scale (583 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-40985883007 / 1000000000000) (-40985883006 / 1000000000000), orderedInterval (-14482398869 / 1000000000000) (-14482398867 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2307046496676581 / 4000000000000) 2 (IntervalRat.scale (583 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-16109763297 / 1000000000000) (-16109762982 / 1000000000000), orderedInterval (29070099456 / 1000000000000) (29070099771 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1699360007644079 / 4000000000000) 2 (IntervalRat.scale (583 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-38639071000 / 1000000000000) (-38639070856 / 1000000000000), orderedInterval (-2302753443 / 1000000000000) (-2302753298 / 1000000000000)))) (orderedInterval (44656837 / 1000000000000) (44656934 / 1000000000000))) = true
  rfl'

theorem compactCertificate420_chunkChecks2_1 :
    compactCertificate420.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2607255261764417 / 4000000000000) 2 (IntervalRat.scale (583 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-23525392905 / 1000000000000) (-23525382557 / 1000000000000), orderedInterval (20590976549 / 1000000000000) (20590986897 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1505299527225593 / 4000000000000) 2 (IntervalRat.scale (583 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (4875954944 / 1000000000000) (4875954945 / 1000000000000), orderedInterval (40833483903 / 1000000000000) (40833483904 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2671180426545037 / 4000000000000) 2 (IntervalRat.scale (583 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (16892719157 / 1000000000000) (16892719600 / 1000000000000), orderedInterval (-25857418756 / 1000000000000) (-25857418313 / 1000000000000)))) (orderedInterval (-34062445821 / 1000000000000) (-34062435769 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2495763250889953 / 4000000000000) 2 (IntervalRat.scale (583 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (13920538780 / 1000000000000) (13920538888 / 1000000000000), orderedInterval (-28760756679 / 1000000000000) (-28760756571 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1781094420105649 / 4000000000000) 2 (IntervalRat.scale (583 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-1792901734 / 1000000000000) (-1792901733 / 1000000000000), orderedInterval (37771227880 / 1000000000000) (37771227881 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2019571241624871 / 4000000000000) 2 (IntervalRat.scale (583 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (4196450941 / 1000000000000) (4196450943 / 1000000000000), orderedInterval (-35264491112 / 1000000000000) (-35264491110 / 1000000000000)))) (orderedInterval (1587093395 / 1000000000000) (1587093498 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1683707950380599 / 4000000000000) 2 (IntervalRat.scale (583 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (26184844166 / 1000000000000) (26184844167 / 1000000000000), orderedInterval (28722631822 / 1000000000000) (28722631823 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1487607035900579 / 4000000000000) 2 (IntervalRat.scale (583 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (37976196520 / 1000000000000) (37976218018 / 1000000000000), orderedInterval (-16470632796 / 1000000000000) (-16470611299 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (431166501273321 / 800000000000) 2 (IntervalRat.scale (583 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-19706807127 / 1000000000000) (-19706805694 / 1000000000000), orderedInterval (28175811100 / 1000000000000) (28175812533 / 1000000000000)))) (orderedInterval (4621473287 / 1000000000000) (4621475481 / 1000000000000))) = true
  rfl'

theorem compactCertificate420_chunkChecks2_2 :
    compactCertificate420.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1192629233571787 / 4000000000000) 2 (IntervalRat.scale (583 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-21786831695 / 1000000000000) (-21786831694 / 1000000000000), orderedInterval (-40712899547 / 1000000000000) (-40712899546 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1011005009305907 / 4000000000000) 2 (IntervalRat.scale (583 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (40316328372 / 1000000000000) (40316425117 / 1000000000000), orderedInterval (-29968734251 / 1000000000000) (-29968637506 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (632639992355921 / 4000000000000) 2 (IntervalRat.scale (583 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (60718528827 / 1000000000000) (60718531039 / 1000000000000), orderedInterval (-18587777236 / 1000000000000) (-18587775023 / 1000000000000)))) (orderedInterval (-2537594173 / 1000000000000) (-2537589953 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (340235891954607 / 4000000000000) 2 (IntervalRat.scale (583 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-73713024509 / 1000000000000) (-73713024508 / 1000000000000), orderedInterval (-44852284022 / 1000000000000) (-44852284021 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (923806631964821 / 4000000000000) 2 (IntervalRat.scale (583 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-35453712688 / 1000000000000) (-35453685147 / 1000000000000), orderedInterval (38800666194 / 1000000000000) (38800693735 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1261378977289717 / 4000000000000) 2 (IntervalRat.scale (583 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (41389789802 / 1000000000000) (41389804906 / 1000000000000), orderedInterval (-17549586106 / 1000000000000) (-17549571002 / 1000000000000)))) (orderedInterval (3088026232 / 1000000000000) (3088028016 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (533360007644079 / 4000000000000) 2 (IntervalRat.scale (583 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (56762447257 / 1000000000000) (56762491247 / 1000000000000), orderedInterval (-39613624575 / 1000000000000) (-39613580585 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2168078819810959 / 4000000000000) 2 (IntervalRat.scale (583 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (21832397677 / 1000000000000) (21832401125 / 1000000000000), orderedInterval (-26437540213 / 1000000000000) (-26437536765 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1448176174050881 / 4000000000000) 2 (IntervalRat.scale (583 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-41920358682 / 1000000000000) (-41920358529 / 1000000000000), orderedInterval (-984255407 / 1000000000000) (-984255254 / 1000000000000)))) (orderedInterval (-6074120994 / 1000000000000) (-6074119754 / 1000000000000))) = true
  rfl'

theorem compactCertificate420_chunkChecks2 :
    compactCertificate420.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate420.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate420_chunkChecks2_0
    compactCertificate420_chunkChecks2_1 compactCertificate420_chunkChecks2_2

theorem compactCertificate420_chunkChecks3_0 :
    compactCertificate420.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (583 / 2) 3 (IntervalRat.scale (583 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-5448411709 / 1000000000000) (-5448411708 / 1000000000000), orderedInterval (-46404685468 / 1000000000000) (-46404685467 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (858870322626283 / 4000000000000) 3 (IntervalRat.scale (583 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (51965619746 / 1000000000000) (51965623094 / 1000000000000), orderedInterval (-16383987382 / 1000000000000) (-16383984033 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (277741015732939 / 800000000000) 3 (IntervalRat.scale (583 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (29360143253 / 1000000000000) (29360161377 / 1000000000000), orderedInterval (-31214222253 / 1000000000000) (-31214204129 / 1000000000000)))) (orderedInterval (21550059452 / 1000000000000) (21550061298 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (250616218089281 / 4000000000000) 3 (IntervalRat.scale (583 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (57381088714 / 1000000000000) (57381088715 / 1000000000000), orderedInterval (82417893164 / 1000000000000) (82417893165 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (673190413874957 / 4000000000000) 3 (IntervalRat.scale (583 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-32864723663 / 1000000000000) (-32864717020 / 1000000000000), orderedInterval (52084362013 / 1000000000000) (52084368656 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1827842927855769 / 4000000000000) 3 (IntervalRat.scale (583 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29846082855 / 1000000000000) (-29846030691 / 1000000000000), orderedInterval (22446318290 / 1000000000000) (22446370453 / 1000000000000)))) (orderedInterval (5806406743 / 1000000000000) (5806421189 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1346380827750497 / 4000000000000) 3 (IntervalRat.scale (583 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-40985883007 / 1000000000000) (-40985883006 / 1000000000000), orderedInterval (-14482398869 / 1000000000000) (-14482398867 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2307046496676581 / 4000000000000) 3 (IntervalRat.scale (583 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-16109763297 / 1000000000000) (-16109762982 / 1000000000000), orderedInterval (29070099456 / 1000000000000) (29070099771 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1699360007644079 / 4000000000000) 3 (IntervalRat.scale (583 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-38639071000 / 1000000000000) (-38639070856 / 1000000000000), orderedInterval (-2302753443 / 1000000000000) (-2302753298 / 1000000000000)))) (orderedInterval (7117404312 / 1000000000000) (7117404490 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate420_chunkChecks3_1 :
    compactCertificate420.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2607255261764417 / 4000000000000) 3 (IntervalRat.scale (583 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-23525392905 / 1000000000000) (-23525382557 / 1000000000000), orderedInterval (20590976549 / 1000000000000) (20590986897 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1505299527225593 / 4000000000000) 3 (IntervalRat.scale (583 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (4875954944 / 1000000000000) (4875954945 / 1000000000000), orderedInterval (40833483903 / 1000000000000) (40833483904 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2671180426545037 / 4000000000000) 3 (IntervalRat.scale (583 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (16892719157 / 1000000000000) (16892719600 / 1000000000000), orderedInterval (-25857418756 / 1000000000000) (-25857418313 / 1000000000000)))) (orderedInterval (78707367501 / 1000000000000) (78707389974 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2495763250889953 / 4000000000000) 3 (IntervalRat.scale (583 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (13920538780 / 1000000000000) (13920538888 / 1000000000000), orderedInterval (-28760756679 / 1000000000000) (-28760756571 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1781094420105649 / 4000000000000) 3 (IntervalRat.scale (583 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-1792901734 / 1000000000000) (-1792901733 / 1000000000000), orderedInterval (37771227880 / 1000000000000) (37771227881 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2019571241624871 / 4000000000000) 3 (IntervalRat.scale (583 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (4196450941 / 1000000000000) (4196450943 / 1000000000000), orderedInterval (-35264491112 / 1000000000000) (-35264491110 / 1000000000000)))) (orderedInterval (-18754944935 / 1000000000000) (-18754944757 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1683707950380599 / 4000000000000) 3 (IntervalRat.scale (583 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (26184844166 / 1000000000000) (26184844167 / 1000000000000), orderedInterval (28722631822 / 1000000000000) (28722631823 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1487607035900579 / 4000000000000) 3 (IntervalRat.scale (583 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (37976196520 / 1000000000000) (37976218018 / 1000000000000), orderedInterval (-16470632796 / 1000000000000) (-16470611299 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (431166501273321 / 800000000000) 3 (IntervalRat.scale (583 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-19706807127 / 1000000000000) (-19706805694 / 1000000000000), orderedInterval (28175811100 / 1000000000000) (28175812533 / 1000000000000)))) (orderedInterval (-7531547357 / 1000000000000) (-7531544470 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate420_chunkChecks3_2 :
    compactCertificate420.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1192629233571787 / 4000000000000) 3 (IntervalRat.scale (583 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-21786831695 / 1000000000000) (-21786831694 / 1000000000000), orderedInterval (-40712899547 / 1000000000000) (-40712899546 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1011005009305907 / 4000000000000) 3 (IntervalRat.scale (583 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (40316328372 / 1000000000000) (40316425117 / 1000000000000), orderedInterval (-29968734251 / 1000000000000) (-29968637506 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (632639992355921 / 4000000000000) 3 (IntervalRat.scale (583 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (60718528827 / 1000000000000) (60718531039 / 1000000000000), orderedInterval (-18587777236 / 1000000000000) (-18587775023 / 1000000000000)))) (orderedInterval (-7966232483 / 1000000000000) (-7966228824 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (340235891954607 / 4000000000000) 3 (IntervalRat.scale (583 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-73713024509 / 1000000000000) (-73713024508 / 1000000000000), orderedInterval (-44852284022 / 1000000000000) (-44852284021 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (923806631964821 / 4000000000000) 3 (IntervalRat.scale (583 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-35453712688 / 1000000000000) (-35453685147 / 1000000000000), orderedInterval (38800666194 / 1000000000000) (38800693735 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1261378977289717 / 4000000000000) 3 (IntervalRat.scale (583 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (41389789802 / 1000000000000) (41389804906 / 1000000000000), orderedInterval (-17549586106 / 1000000000000) (-17549571002 / 1000000000000)))) (orderedInterval (-1296147784 / 1000000000000) (-1296145969 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (533360007644079 / 4000000000000) 3 (IntervalRat.scale (583 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (56762447257 / 1000000000000) (56762491247 / 1000000000000), orderedInterval (-39613624575 / 1000000000000) (-39613580585 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2168078819810959 / 4000000000000) 3 (IntervalRat.scale (583 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (21832397677 / 1000000000000) (21832401125 / 1000000000000), orderedInterval (-26437540213 / 1000000000000) (-26437536765 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1448176174050881 / 4000000000000) 3 (IntervalRat.scale (583 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-41920358682 / 1000000000000) (-41920358529 / 1000000000000), orderedInterval (-984255407 / 1000000000000) (-984255254 / 1000000000000)))) (orderedInterval (-14145237588 / 1000000000000) (-14145235441 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate420_chunkChecks3 :
    compactCertificate420.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate420.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate420_chunkChecks3_0
    compactCertificate420_chunkChecks3_1 compactCertificate420_chunkChecks3_2

theorem compactCertificate420_chunkChecks4_0 :
    compactCertificate420.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (583 / 2) 4 (IntervalRat.scale (583 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-5448411709 / 1000000000000) (-5448411708 / 1000000000000), orderedInterval (-46404685468 / 1000000000000) (-46404685467 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (858870322626283 / 4000000000000) 4 (IntervalRat.scale (583 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (51965619746 / 1000000000000) (51965623094 / 1000000000000), orderedInterval (-16383987382 / 1000000000000) (-16383984033 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (277741015732939 / 800000000000) 4 (IntervalRat.scale (583 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (29360143253 / 1000000000000) (29360161377 / 1000000000000), orderedInterval (-31214222253 / 1000000000000) (-31214204129 / 1000000000000)))) (orderedInterval (1301717120 / 1000000000000) (1301719318 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (250616218089281 / 4000000000000) 4 (IntervalRat.scale (583 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (57381088714 / 1000000000000) (57381088715 / 1000000000000), orderedInterval (82417893164 / 1000000000000) (82417893165 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (673190413874957 / 4000000000000) 4 (IntervalRat.scale (583 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-32864723663 / 1000000000000) (-32864717020 / 1000000000000), orderedInterval (52084362013 / 1000000000000) (52084368656 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1827842927855769 / 4000000000000) 4 (IntervalRat.scale (583 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29846082855 / 1000000000000) (-29846030691 / 1000000000000), orderedInterval (22446318290 / 1000000000000) (22446370453 / 1000000000000)))) (orderedInterval (12638548556 / 1000000000000) (12638571202 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1346380827750497 / 4000000000000) 4 (IntervalRat.scale (583 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-40985883007 / 1000000000000) (-40985883006 / 1000000000000), orderedInterval (-14482398869 / 1000000000000) (-14482398867 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2307046496676581 / 4000000000000) 4 (IntervalRat.scale (583 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-16109763297 / 1000000000000) (-16109762982 / 1000000000000), orderedInterval (29070099456 / 1000000000000) (29070099771 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1699360007644079 / 4000000000000) 4 (IntervalRat.scale (583 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-38639071000 / 1000000000000) (-38639070856 / 1000000000000), orderedInterval (-2302753443 / 1000000000000) (-2302753298 / 1000000000000)))) (orderedInterval (3353307476 / 1000000000000) (3353307812 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate420_chunkChecks4_1 :
    compactCertificate420.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2607255261764417 / 4000000000000) 4 (IntervalRat.scale (583 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-23525392905 / 1000000000000) (-23525382557 / 1000000000000), orderedInterval (20590976549 / 1000000000000) (20590986897 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1505299527225593 / 4000000000000) 4 (IntervalRat.scale (583 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (4875954944 / 1000000000000) (4875954945 / 1000000000000), orderedInterval (40833483903 / 1000000000000) (40833483904 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2671180426545037 / 4000000000000) 4 (IntervalRat.scale (583 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (16892719157 / 1000000000000) (16892719600 / 1000000000000), orderedInterval (-25857418756 / 1000000000000) (-25857418313 / 1000000000000)))) (orderedInterval (171110398340 / 1000000000000) (171110448686 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2495763250889953 / 4000000000000) 4 (IntervalRat.scale (583 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (13920538780 / 1000000000000) (13920538888 / 1000000000000), orderedInterval (-28760756679 / 1000000000000) (-28760756571 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1781094420105649 / 4000000000000) 4 (IntervalRat.scale (583 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-1792901734 / 1000000000000) (-1792901733 / 1000000000000), orderedInterval (37771227880 / 1000000000000) (37771227881 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2019571241624871 / 4000000000000) 4 (IntervalRat.scale (583 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (4196450941 / 1000000000000) (4196450943 / 1000000000000), orderedInterval (-35264491112 / 1000000000000) (-35264491110 / 1000000000000)))) (orderedInterval (-6260545748 / 1000000000000) (-6260545432 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1683707950380599 / 4000000000000) 4 (IntervalRat.scale (583 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (26184844166 / 1000000000000) (26184844167 / 1000000000000), orderedInterval (28722631822 / 1000000000000) (28722631823 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1487607035900579 / 4000000000000) 4 (IntervalRat.scale (583 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (37976196520 / 1000000000000) (37976218018 / 1000000000000), orderedInterval (-16470632796 / 1000000000000) (-16470611299 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (431166501273321 / 800000000000) 4 (IntervalRat.scale (583 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-19706807127 / 1000000000000) (-19706805694 / 1000000000000), orderedInterval (28175811100 / 1000000000000) (28175812533 / 1000000000000)))) (orderedInterval (-10287993222 / 1000000000000) (-10287989368 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate420_chunkChecks4_2 :
    compactCertificate420.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1192629233571787 / 4000000000000) 4 (IntervalRat.scale (583 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-21786831695 / 1000000000000) (-21786831694 / 1000000000000), orderedInterval (-40712899547 / 1000000000000) (-40712899546 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1011005009305907 / 4000000000000) 4 (IntervalRat.scale (583 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (40316328372 / 1000000000000) (40316425117 / 1000000000000), orderedInterval (-29968734251 / 1000000000000) (-29968637506 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (632639992355921 / 4000000000000) 4 (IntervalRat.scale (583 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (60718528827 / 1000000000000) (60718531039 / 1000000000000), orderedInterval (-18587777236 / 1000000000000) (-18587775023 / 1000000000000)))) (orderedInterval (2748998136 / 1000000000000) (2749001324 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (340235891954607 / 4000000000000) 4 (IntervalRat.scale (583 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-73713024509 / 1000000000000) (-73713024508 / 1000000000000), orderedInterval (-44852284022 / 1000000000000) (-44852284021 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (923806631964821 / 4000000000000) 4 (IntervalRat.scale (583 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-35453712688 / 1000000000000) (-35453685147 / 1000000000000), orderedInterval (38800666194 / 1000000000000) (38800693735 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1261378977289717 / 4000000000000) 4 (IntervalRat.scale (583 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (41389789802 / 1000000000000) (41389804906 / 1000000000000), orderedInterval (-17549586106 / 1000000000000) (-17549571002 / 1000000000000)))) (orderedInterval (-4008679252 / 1000000000000) (-4008677374 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (533360007644079 / 4000000000000) 4 (IntervalRat.scale (583 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (56762447257 / 1000000000000) (56762491247 / 1000000000000), orderedInterval (-39613624575 / 1000000000000) (-39613580585 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2168078819810959 / 4000000000000) 4 (IntervalRat.scale (583 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (21832397677 / 1000000000000) (21832401125 / 1000000000000), orderedInterval (-26437540213 / 1000000000000) (-26437536765 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1448176174050881 / 4000000000000) 4 (IntervalRat.scale (583 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-41920358682 / 1000000000000) (-41920358529 / 1000000000000), orderedInterval (-984255407 / 1000000000000) (-984255254 / 1000000000000)))) (orderedInterval (-2416395963 / 1000000000000) (-2416392100 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate420_chunkChecks4 :
    compactCertificate420.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate420.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate420_chunkChecks4_0
    compactCertificate420_chunkChecks4_1 compactCertificate420_chunkChecks4_2

theorem compactCertificate420_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate420.chunkCheck r b = true :=
  compactCertificate420.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate420_chunkChecks0
    · exact compactCertificate420_chunkChecks1
    · exact compactCertificate420_chunkChecks2
    · exact compactCertificate420_chunkChecks3
    · exact compactCertificate420_chunkChecks4)

theorem compactCertificate420_coefficient0 :
    compactCertificate420.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate420_coefficient1 :
    compactCertificate420.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate420_coefficient2 :
    compactCertificate420.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate420_coefficient3 :
    compactCertificate420.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate420_coefficient4 :
    compactCertificate420.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate420_coefficients : ∀ r : Fin 5,
    compactCertificate420.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate420_coefficient0
  · exact compactCertificate420_coefficient1
  · exact compactCertificate420_coefficient2
  · exact compactCertificate420_coefficient3
  · exact compactCertificate420_coefficient4

theorem compactCertificate420_lower : (1 : ℚ) ≤ compactCertificate420.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate420, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate420_proves {t : ℝ} (ht : t ∈ compactCertificate420.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate420.proves compactCertificate420_states compactCertificate420_chunks
    compactCertificate420_coefficients compactCertificate420_lower ht

end Erdos232
