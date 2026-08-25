/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate286 : CompactCertificate where
  left := 160
  right := 161
  center := 321 / 2
  grid := fun i =>
    match i.val with
    | 0 => 51
    | 1 => 38
    | 2 => 61
    | 3 => 11
    | 4 => 30
    | 5 => 80
    | 6 => 59
    | 7 => 101
    | 8 => 74
    | 9 => 114
    | 10 => 66
    | 11 => 117
    | 12 => 109
    | 13 => 78
    | 14 => 89
    | 15 => 74
    | 16 => 65
    | 17 => 95
    | 18 => 52
    | 19 => 44
    | 20 => 28
    | 21 => 15
    | 22 => 40
    | 23 => 55
    | 24 => 23
    | 25 => 95
    | _ => 63
  point := fun i =>
    match i.val with
    | 0 => 321 / 2
    | 1 => 472894294276221 / 4000000000000
    | 2 => 152924298542493 / 800000000000
    | 3 => 137989375654647 / 4000000000000
    | 4 => 370658872819659 / 4000000000000
    | 5 => 1006410943124703 / 4000000000000
    | 6 => 741317745639639 / 4000000000000
    | 7 => 1270260592509747 / 4000000000000
    | 8 => 935668203179673 / 4000000000000
    | 9 => 1435555641554679 / 4000000000000
    | 10 => 828818436088191 / 4000000000000
    | 11 => 1470752859212619 / 4000000000000
    | 12 => 1374168102119511 / 4000000000000
    | 13 => 980671198720263 / 4000000000000
    | 14 => 1111976618458977 / 4000000000000
    | 15 => 927050175080913 / 4000000000000
    | 16 => 819076944295173 / 4000000000000
    | 17 => 237400423514127 / 800000000000
    | 18 => 656662065139869 / 4000000000000
    | 19 => 556659704952309 / 4000000000000
    | 20 => 348331796820327 / 4000000000000
    | 21 => 187333998829209 / 4000000000000
    | 22 => 508648248474627 / 4000000000000
    | 23 => 694515697615779 / 4000000000000
    | 24 => 293668203179673 / 4000000000000
    | 25 => 1193744941954233 / 4000000000000
    | _ => 797366298233847 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-55044983086 / 1000000000000) (-55044983085 / 1000000000000), orderedInterval (-30431103752 / 1000000000000) (-30431103751 / 1000000000000))
    | 1 => (orderedInterval (-26714079047 / 1000000000000) (-26714077983 / 1000000000000), orderedInterval (68459694176 / 1000000000000) (68459695240 / 1000000000000))
    | 2 => (orderedInterval (-17217696083 / 1000000000000) (-17217696082 / 1000000000000), orderedInterval (-55036167669 / 1000000000000) (-55036167668 / 1000000000000))
    | 3 => (orderedInterval (-89733536869 / 1000000000000) (-89733536868 / 1000000000000), orderedInterval (-100691384764 / 1000000000000) (-100691384763 / 1000000000000))
    | 4 => (orderedInterval (-59401536347 / 1000000000000) (-59401451780 / 1000000000000), orderedInterval (58127051283 / 1000000000000) (58127135850 / 1000000000000))
    | 5 => (orderedInterval (43886420176 / 1000000000000) (43886420177 / 1000000000000), orderedInterval (24494024697 / 1000000000000) (24494024698 / 1000000000000))
    | 6 => (orderedInterval (-40385474878 / 1000000000000) (-40385474877 / 1000000000000), orderedInterval (-42365567228 / 1000000000000) (-42365567227 / 1000000000000))
    | 7 => (orderedInterval (-38822058892 / 1000000000000) (-38822058891 / 1000000000000), orderedInterval (-22244408383 / 1000000000000) (-22244408382 / 1000000000000))
    | 8 => (orderedInterval (41427267185 / 1000000000000) (41427368737 / 1000000000000), orderedInterval (-31795659209 / 1000000000000) (-31795557657 / 1000000000000))
    | 9 => (orderedInterval (42086186848 / 1000000000000) (42086186972 / 1000000000000), orderedInterval (1558212155 / 1000000000000) (1558212279 / 1000000000000))
    | 10 => (orderedInterval (33292523314 / 1000000000000) (33292523315 / 1000000000000), orderedInterval (44237055759 / 1000000000000) (44237055760 / 1000000000000))
    | 11 => (orderedInterval (-32772932203 / 1000000000000) (-32772932202 / 1000000000000), orderedInterval (-25594203137 / 1000000000000) (-25594203136 / 1000000000000))
    | 12 => (orderedInterval (-40826177239 / 1000000000000) (-40826169121 / 1000000000000), orderedInterval (13709615067 / 1000000000000) (13709623185 / 1000000000000))
    | 13 => (orderedInterval (40182937286 / 1000000000000) (40182937287 / 1000000000000), orderedInterval (31254927080 / 1000000000000) (31254927081 / 1000000000000))
    | 14 => (orderedInterval (35074686834 / 1000000000000) (35074733169 / 1000000000000), orderedInterval (-32617857143 / 1000000000000) (-32617810808 / 1000000000000))
    | 15 => (orderedInterval (3642011940 / 1000000000000) (3642011941 / 1000000000000), orderedInterval (52276024534 / 1000000000000) (52276024535 / 1000000000000))
    | 16 => (orderedInterval (-54410481847 / 1000000000000) (-54410481844 / 1000000000000), orderedInterval (-12051274884 / 1000000000000) (-12051274881 / 1000000000000))
    | 17 => (orderedInterval (36731838216 / 1000000000000) (36731933526 / 1000000000000), orderedInterval (-28276658589 / 1000000000000) (-28276563279 / 1000000000000))
    | 18 => (orderedInterval (62264239343 / 1000000000000) (62264239411 / 1000000000000), orderedInterval (-1219506562 / 1000000000000) (-1219506495 / 1000000000000))
    | 19 => (orderedInterval (66890435032 / 1000000000000) (66890435375 / 1000000000000), orderedInterval (-10250918966 / 1000000000000) (-10250918622 / 1000000000000))
    | 20 => (orderedInterval (-8338629516 / 1000000000000) (-8338629483 / 1000000000000), orderedInterval (85142434936 / 1000000000000) (85142434968 / 1000000000000))
    | 21 => (orderedInterval (-55109294830 / 1000000000000) (-55109294829 / 1000000000000), orderedInterval (-102157274488 / 1000000000000) (-102157274487 / 1000000000000))
    | 22 => (orderedInterval (53566958030 / 1000000000000) (53567063915 / 1000000000000), orderedInterval (-46437666166 / 1000000000000) (-46437560282 / 1000000000000))
    | 23 => (orderedInterval (-60459685319 / 1000000000000) (-60459685195 / 1000000000000), orderedInterval (3515516295 / 1000000000000) (3515516419 / 1000000000000))
    | 24 => (orderedInterval (-86704798524 / 1000000000000) (-86704795195 / 1000000000000), orderedInterval (34552359152 / 1000000000000) (34552362482 / 1000000000000))
    | 25 => (orderedInterval (-32149076447 / 1000000000000) (-32149076446 / 1000000000000), orderedInterval (-33106689695 / 1000000000000) (-33106689694 / 1000000000000))
    | _ => (orderedInterval (-45489109560 / 1000000000000) (-45489034300 / 1000000000000), orderedInterval (33645444782 / 1000000000000) (33645520042 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-23077181767 / 1000000000000) (-23077181745 / 1000000000000)
      | 1 => orderedInterval (-4315178418 / 1000000000000) (-4315175311 / 1000000000000)
      | 2 => orderedInterval (2198642930 / 1000000000000) (2198645394 / 1000000000000)
      | 3 => orderedInterval (-9670370706 / 1000000000000) (-9670370619 / 1000000000000)
      | 4 => orderedInterval (4359353693 / 1000000000000) (4359354094 / 1000000000000)
      | 5 => orderedInterval (4096267963 / 1000000000000) (4096270420 / 1000000000000)
      | 6 => orderedInterval (-14013043352 / 1000000000000) (-14013043280 / 1000000000000)
      | 7 => orderedInterval (4435892934 / 1000000000000) (4435895366 / 1000000000000)
      | _ => orderedInterval (10629256487 / 1000000000000) (10629270673 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-15438374735 / 1000000000000) (-15438374714 / 1000000000000)
      | 1 => orderedInterval (-1269523492 / 1000000000000) (-1269521686 / 1000000000000)
      | 2 => orderedInterval (237586889 / 1000000000000) (237590482 / 1000000000000)
      | 3 => orderedInterval (-4722853237 / 1000000000000) (-4722853055 / 1000000000000)
      | 4 => orderedInterval (4270823145 / 1000000000000) (4270823897 / 1000000000000)
      | 5 => orderedInterval (412969411 / 1000000000000) (412973946 / 1000000000000)
      | 6 => orderedInterval (2206441651 / 1000000000000) (2206441718 / 1000000000000)
      | 7 => orderedInterval (1093659017 / 1000000000000) (1093660949 / 1000000000000)
      | _ => orderedInterval (-2734211265 / 1000000000000) (-2734193654 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (23482318756 / 1000000000000) (23482318778 / 1000000000000)
      | 1 => orderedInterval (8352737128 / 1000000000000) (8352738199 / 1000000000000)
      | 2 => orderedInterval (-6815915332 / 1000000000000) (-6815910067 / 1000000000000)
      | 3 => orderedInterval (57759891423 / 1000000000000) (57759891818 / 1000000000000)
      | 4 => orderedInterval (-11737104392 / 1000000000000) (-11737102961 / 1000000000000)
      | 5 => orderedInterval (-8373565832 / 1000000000000) (-8373557428 / 1000000000000)
      | 6 => orderedInterval (13328034262 / 1000000000000) (13328034325 / 1000000000000)
      | 7 => orderedInterval (-4753231629 / 1000000000000) (-4753230080 / 1000000000000)
      | _ => orderedInterval (-22087460671 / 1000000000000) (-22087438682 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (17116057227 / 1000000000000) (17116057249 / 1000000000000)
      | 1 => orderedInterval (6236533302 / 1000000000000) (6236533949 / 1000000000000)
      | 2 => orderedInterval (-2893199146 / 1000000000000) (-2893191464 / 1000000000000)
      | 3 => orderedInterval (39427429333 / 1000000000000) (39427430202 / 1000000000000)
      | 4 => orderedInterval (-8891556047 / 1000000000000) (-8891553295 / 1000000000000)
      | 5 => orderedInterval (1378352596 / 1000000000000) (1378368124 / 1000000000000)
      | 6 => orderedInterval (-1112563594 / 1000000000000) (-1112563534 / 1000000000000)
      | 7 => orderedInterval (-200064252 / 1000000000000) (-200063017 / 1000000000000)
      | _ => orderedInterval (-5113131543 / 1000000000000) (-5113104209 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-24136468825 / 1000000000000) (-24136468801 / 1000000000000)
      | 1 => orderedInterval (-19157027069 / 1000000000000) (-19157026648 / 1000000000000)
      | 2 => orderedInterval (22904920885 / 1000000000000) (22904932147 / 1000000000000)
      | 3 => orderedInterval (-308913628289 / 1000000000000) (-308913626355 / 1000000000000)
      | 4 => orderedInterval (34671411599 / 1000000000000) (34671416971 / 1000000000000)
      | 5 => orderedInterval (19405536253 / 1000000000000) (19405565043 / 1000000000000)
      | 6 => orderedInterval (-13045754023 / 1000000000000) (-13045753965 / 1000000000000)
      | 7 => orderedInterval (5876877126 / 1000000000000) (5876878119 / 1000000000000)
      | _ => orderedInterval (51632156275 / 1000000000000) (51632190441 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-25356360236 / 1000000000000) (-25356335008 / 1000000000000)
    | 1 => orderedInterval (-15943482616 / 1000000000000) (-15943452117 / 1000000000000)
    | 2 => orderedInterval (49155703713 / 1000000000000) (49155743902 / 1000000000000)
    | 3 => orderedInterval (45947857876 / 1000000000000) (45947914005 / 1000000000000)
    | _ => orderedInterval (-230761976068 / 1000000000000) (-230761893048 / 1000000000000)

theorem compactCertificate286_stateChecks0 :
    compactCertificate286.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (321 / 2)) (orderedInterval (-55044983086 / 1000000000000) (-55044983085 / 1000000000000), orderedInterval (-30431103752 / 1000000000000) (-30431103751 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (472894294276221 / 4000000000000)) (orderedInterval (-26714079047 / 1000000000000) (-26714077983 / 1000000000000), orderedInterval (68459694176 / 1000000000000) (68459695240 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 61 12 (152924298542493 / 800000000000)) (orderedInterval (-17217696083 / 1000000000000) (-17217696082 / 1000000000000), orderedInterval (-55036167669 / 1000000000000) (-55036167668 / 1000000000000))) = true
  rfl'

theorem compactCertificate286_stateChecks1 :
    compactCertificate286.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 11 12 (137989375654647 / 4000000000000)) (orderedInterval (-89733536869 / 1000000000000) (-89733536868 / 1000000000000), orderedInterval (-100691384764 / 1000000000000) (-100691384763 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (370658872819659 / 4000000000000)) (orderedInterval (-59401536347 / 1000000000000) (-59401451780 / 1000000000000), orderedInterval (58127051283 / 1000000000000) (58127135850 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 80 12 (1006410943124703 / 4000000000000)) (orderedInterval (43886420176 / 1000000000000) (43886420177 / 1000000000000), orderedInterval (24494024697 / 1000000000000) (24494024698 / 1000000000000))) = true
  rfl'

theorem compactCertificate286_stateChecks2 :
    compactCertificate286.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 59 12 (741317745639639 / 4000000000000)) (orderedInterval (-40385474878 / 1000000000000) (-40385474877 / 1000000000000), orderedInterval (-42365567228 / 1000000000000) (-42365567227 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 101 12 (1270260592509747 / 4000000000000)) (orderedInterval (-38822058892 / 1000000000000) (-38822058891 / 1000000000000), orderedInterval (-22244408383 / 1000000000000) (-22244408382 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 74 12 (935668203179673 / 4000000000000)) (orderedInterval (41427267185 / 1000000000000) (41427368737 / 1000000000000), orderedInterval (-31795659209 / 1000000000000) (-31795557657 / 1000000000000))) = true
  rfl'

theorem compactCertificate286_stateChecks3 :
    compactCertificate286.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 114 12 (1435555641554679 / 4000000000000)) (orderedInterval (42086186848 / 1000000000000) (42086186972 / 1000000000000), orderedInterval (1558212155 / 1000000000000) (1558212279 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (828818436088191 / 4000000000000)) (orderedInterval (33292523314 / 1000000000000) (33292523315 / 1000000000000), orderedInterval (44237055759 / 1000000000000) (44237055760 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 117 12 (1470752859212619 / 4000000000000)) (orderedInterval (-32772932203 / 1000000000000) (-32772932202 / 1000000000000), orderedInterval (-25594203137 / 1000000000000) (-25594203136 / 1000000000000))) = true
  rfl'

theorem compactCertificate286_stateChecks4 :
    compactCertificate286.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 109 12 (1374168102119511 / 4000000000000)) (orderedInterval (-40826177239 / 1000000000000) (-40826169121 / 1000000000000), orderedInterval (13709615067 / 1000000000000) (13709623185 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 78 12 (980671198720263 / 4000000000000)) (orderedInterval (40182937286 / 1000000000000) (40182937287 / 1000000000000), orderedInterval (31254927080 / 1000000000000) (31254927081 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 89 12 (1111976618458977 / 4000000000000)) (orderedInterval (35074686834 / 1000000000000) (35074733169 / 1000000000000), orderedInterval (-32617857143 / 1000000000000) (-32617810808 / 1000000000000))) = true
  rfl'

theorem compactCertificate286_stateChecks5 :
    compactCertificate286.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 74 12 (927050175080913 / 4000000000000)) (orderedInterval (3642011940 / 1000000000000) (3642011941 / 1000000000000), orderedInterval (52276024534 / 1000000000000) (52276024535 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 65 12 (819076944295173 / 4000000000000)) (orderedInterval (-54410481847 / 1000000000000) (-54410481844 / 1000000000000), orderedInterval (-12051274884 / 1000000000000) (-12051274881 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 95 12 (237400423514127 / 800000000000)) (orderedInterval (36731838216 / 1000000000000) (36731933526 / 1000000000000), orderedInterval (-28276658589 / 1000000000000) (-28276563279 / 1000000000000))) = true
  rfl'

theorem compactCertificate286_stateChecks6 :
    compactCertificate286.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 52 12 (656662065139869 / 4000000000000)) (orderedInterval (62264239343 / 1000000000000) (62264239411 / 1000000000000), orderedInterval (-1219506562 / 1000000000000) (-1219506495 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 44 12 (556659704952309 / 4000000000000)) (orderedInterval (66890435032 / 1000000000000) (66890435375 / 1000000000000), orderedInterval (-10250918966 / 1000000000000) (-10250918622 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 28 12 (348331796820327 / 4000000000000)) (orderedInterval (-8338629516 / 1000000000000) (-8338629483 / 1000000000000), orderedInterval (85142434936 / 1000000000000) (85142434968 / 1000000000000))) = true
  rfl'

theorem compactCertificate286_stateChecks7 :
    compactCertificate286.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 15 12 (187333998829209 / 4000000000000)) (orderedInterval (-55109294830 / 1000000000000) (-55109294829 / 1000000000000), orderedInterval (-102157274488 / 1000000000000) (-102157274487 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 40 12 (508648248474627 / 4000000000000)) (orderedInterval (53566958030 / 1000000000000) (53567063915 / 1000000000000), orderedInterval (-46437666166 / 1000000000000) (-46437560282 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (694515697615779 / 4000000000000)) (orderedInterval (-60459685319 / 1000000000000) (-60459685195 / 1000000000000), orderedInterval (3515516295 / 1000000000000) (3515516419 / 1000000000000))) = true
  rfl'

theorem compactCertificate286_stateChecks8 :
    compactCertificate286.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 23 12 (293668203179673 / 4000000000000)) (orderedInterval (-86704798524 / 1000000000000) (-86704795195 / 1000000000000), orderedInterval (34552359152 / 1000000000000) (34552362482 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 95 12 (1193744941954233 / 4000000000000)) (orderedInterval (-32149076447 / 1000000000000) (-32149076446 / 1000000000000), orderedInterval (-33106689695 / 1000000000000) (-33106689694 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (797366298233847 / 4000000000000)) (orderedInterval (-45489109560 / 1000000000000) (-45489034300 / 1000000000000), orderedInterval (33645444782 / 1000000000000) (33645520042 / 1000000000000))) = true
  rfl'

theorem compactCertificate286_states : ∀ j,
    BesselStateValid (compactCertificate286.point j) (compactCertificate286.state j) :=
  compactCertificate286.statesValid_of_checks3 compactCertificate286_stateChecks0
    compactCertificate286_stateChecks1 compactCertificate286_stateChecks2
    compactCertificate286_stateChecks3 compactCertificate286_stateChecks4
    compactCertificate286_stateChecks5 compactCertificate286_stateChecks6
    compactCertificate286_stateChecks7 compactCertificate286_stateChecks8

theorem compactCertificate286_chunkChecks0_0 :
    compactCertificate286.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (321 / 2) 0 (IntervalRat.scale (321 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-55044983086 / 1000000000000) (-55044983085 / 1000000000000), orderedInterval (-30431103752 / 1000000000000) (-30431103751 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (472894294276221 / 4000000000000) 0 (IntervalRat.scale (321 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-26714079047 / 1000000000000) (-26714077983 / 1000000000000), orderedInterval (68459694176 / 1000000000000) (68459695240 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (152924298542493 / 800000000000) 0 (IntervalRat.scale (321 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-17217696083 / 1000000000000) (-17217696082 / 1000000000000), orderedInterval (-55036167669 / 1000000000000) (-55036167668 / 1000000000000)))) (orderedInterval (-23077181767 / 1000000000000) (-23077181745 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (137989375654647 / 4000000000000) 0 (IntervalRat.scale (321 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-89733536869 / 1000000000000) (-89733536868 / 1000000000000), orderedInterval (-100691384764 / 1000000000000) (-100691384763 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (370658872819659 / 4000000000000) 0 (IntervalRat.scale (321 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-59401536347 / 1000000000000) (-59401451780 / 1000000000000), orderedInterval (58127051283 / 1000000000000) (58127135850 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1006410943124703 / 4000000000000) 0 (IntervalRat.scale (321 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (43886420176 / 1000000000000) (43886420177 / 1000000000000), orderedInterval (24494024697 / 1000000000000) (24494024698 / 1000000000000)))) (orderedInterval (-4315178418 / 1000000000000) (-4315175311 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (741317745639639 / 4000000000000) 0 (IntervalRat.scale (321 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-40385474878 / 1000000000000) (-40385474877 / 1000000000000), orderedInterval (-42365567228 / 1000000000000) (-42365567227 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1270260592509747 / 4000000000000) 0 (IntervalRat.scale (321 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-38822058892 / 1000000000000) (-38822058891 / 1000000000000), orderedInterval (-22244408383 / 1000000000000) (-22244408382 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (935668203179673 / 4000000000000) 0 (IntervalRat.scale (321 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (41427267185 / 1000000000000) (41427368737 / 1000000000000), orderedInterval (-31795659209 / 1000000000000) (-31795557657 / 1000000000000)))) (orderedInterval (2198642930 / 1000000000000) (2198645394 / 1000000000000))) = true
  rfl'

theorem compactCertificate286_chunkChecks0_1 :
    compactCertificate286.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1435555641554679 / 4000000000000) 0 (IntervalRat.scale (321 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (42086186848 / 1000000000000) (42086186972 / 1000000000000), orderedInterval (1558212155 / 1000000000000) (1558212279 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (828818436088191 / 4000000000000) 0 (IntervalRat.scale (321 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (33292523314 / 1000000000000) (33292523315 / 1000000000000), orderedInterval (44237055759 / 1000000000000) (44237055760 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1470752859212619 / 4000000000000) 0 (IntervalRat.scale (321 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-32772932203 / 1000000000000) (-32772932202 / 1000000000000), orderedInterval (-25594203137 / 1000000000000) (-25594203136 / 1000000000000)))) (orderedInterval (-9670370706 / 1000000000000) (-9670370619 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1374168102119511 / 4000000000000) 0 (IntervalRat.scale (321 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-40826177239 / 1000000000000) (-40826169121 / 1000000000000), orderedInterval (13709615067 / 1000000000000) (13709623185 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (980671198720263 / 4000000000000) 0 (IntervalRat.scale (321 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (40182937286 / 1000000000000) (40182937287 / 1000000000000), orderedInterval (31254927080 / 1000000000000) (31254927081 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1111976618458977 / 4000000000000) 0 (IntervalRat.scale (321 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (35074686834 / 1000000000000) (35074733169 / 1000000000000), orderedInterval (-32617857143 / 1000000000000) (-32617810808 / 1000000000000)))) (orderedInterval (4359353693 / 1000000000000) (4359354094 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (927050175080913 / 4000000000000) 0 (IntervalRat.scale (321 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (3642011940 / 1000000000000) (3642011941 / 1000000000000), orderedInterval (52276024534 / 1000000000000) (52276024535 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (819076944295173 / 4000000000000) 0 (IntervalRat.scale (321 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-54410481847 / 1000000000000) (-54410481844 / 1000000000000), orderedInterval (-12051274884 / 1000000000000) (-12051274881 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (237400423514127 / 800000000000) 0 (IntervalRat.scale (321 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (36731838216 / 1000000000000) (36731933526 / 1000000000000), orderedInterval (-28276658589 / 1000000000000) (-28276563279 / 1000000000000)))) (orderedInterval (4096267963 / 1000000000000) (4096270420 / 1000000000000))) = true
  rfl'

theorem compactCertificate286_chunkChecks0_2 :
    compactCertificate286.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (656662065139869 / 4000000000000) 0 (IntervalRat.scale (321 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (62264239343 / 1000000000000) (62264239411 / 1000000000000), orderedInterval (-1219506562 / 1000000000000) (-1219506495 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (556659704952309 / 4000000000000) 0 (IntervalRat.scale (321 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (66890435032 / 1000000000000) (66890435375 / 1000000000000), orderedInterval (-10250918966 / 1000000000000) (-10250918622 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (348331796820327 / 4000000000000) 0 (IntervalRat.scale (321 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-8338629516 / 1000000000000) (-8338629483 / 1000000000000), orderedInterval (85142434936 / 1000000000000) (85142434968 / 1000000000000)))) (orderedInterval (-14013043352 / 1000000000000) (-14013043280 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (187333998829209 / 4000000000000) 0 (IntervalRat.scale (321 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-55109294830 / 1000000000000) (-55109294829 / 1000000000000), orderedInterval (-102157274488 / 1000000000000) (-102157274487 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (508648248474627 / 4000000000000) 0 (IntervalRat.scale (321 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (53566958030 / 1000000000000) (53567063915 / 1000000000000), orderedInterval (-46437666166 / 1000000000000) (-46437560282 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (694515697615779 / 4000000000000) 0 (IntervalRat.scale (321 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-60459685319 / 1000000000000) (-60459685195 / 1000000000000), orderedInterval (3515516295 / 1000000000000) (3515516419 / 1000000000000)))) (orderedInterval (4435892934 / 1000000000000) (4435895366 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (293668203179673 / 4000000000000) 0 (IntervalRat.scale (321 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-86704798524 / 1000000000000) (-86704795195 / 1000000000000), orderedInterval (34552359152 / 1000000000000) (34552362482 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1193744941954233 / 4000000000000) 0 (IntervalRat.scale (321 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-32149076447 / 1000000000000) (-32149076446 / 1000000000000), orderedInterval (-33106689695 / 1000000000000) (-33106689694 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (797366298233847 / 4000000000000) 0 (IntervalRat.scale (321 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-45489109560 / 1000000000000) (-45489034300 / 1000000000000), orderedInterval (33645444782 / 1000000000000) (33645520042 / 1000000000000)))) (orderedInterval (10629256487 / 1000000000000) (10629270673 / 1000000000000))) = true
  rfl'

theorem compactCertificate286_chunkChecks0 :
    compactCertificate286.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate286.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate286_chunkChecks0_0
    compactCertificate286_chunkChecks0_1 compactCertificate286_chunkChecks0_2

theorem compactCertificate286_chunkChecks1_0 :
    compactCertificate286.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (321 / 2) 1 (IntervalRat.scale (321 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-55044983086 / 1000000000000) (-55044983085 / 1000000000000), orderedInterval (-30431103752 / 1000000000000) (-30431103751 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (472894294276221 / 4000000000000) 1 (IntervalRat.scale (321 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-26714079047 / 1000000000000) (-26714077983 / 1000000000000), orderedInterval (68459694176 / 1000000000000) (68459695240 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (152924298542493 / 800000000000) 1 (IntervalRat.scale (321 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-17217696083 / 1000000000000) (-17217696082 / 1000000000000), orderedInterval (-55036167669 / 1000000000000) (-55036167668 / 1000000000000)))) (orderedInterval (-15438374735 / 1000000000000) (-15438374714 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (137989375654647 / 4000000000000) 1 (IntervalRat.scale (321 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-89733536869 / 1000000000000) (-89733536868 / 1000000000000), orderedInterval (-100691384764 / 1000000000000) (-100691384763 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (370658872819659 / 4000000000000) 1 (IntervalRat.scale (321 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-59401536347 / 1000000000000) (-59401451780 / 1000000000000), orderedInterval (58127051283 / 1000000000000) (58127135850 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1006410943124703 / 4000000000000) 1 (IntervalRat.scale (321 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (43886420176 / 1000000000000) (43886420177 / 1000000000000), orderedInterval (24494024697 / 1000000000000) (24494024698 / 1000000000000)))) (orderedInterval (-1269523492 / 1000000000000) (-1269521686 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (741317745639639 / 4000000000000) 1 (IntervalRat.scale (321 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-40385474878 / 1000000000000) (-40385474877 / 1000000000000), orderedInterval (-42365567228 / 1000000000000) (-42365567227 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1270260592509747 / 4000000000000) 1 (IntervalRat.scale (321 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-38822058892 / 1000000000000) (-38822058891 / 1000000000000), orderedInterval (-22244408383 / 1000000000000) (-22244408382 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (935668203179673 / 4000000000000) 1 (IntervalRat.scale (321 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (41427267185 / 1000000000000) (41427368737 / 1000000000000), orderedInterval (-31795659209 / 1000000000000) (-31795557657 / 1000000000000)))) (orderedInterval (237586889 / 1000000000000) (237590482 / 1000000000000))) = true
  rfl'

theorem compactCertificate286_chunkChecks1_1 :
    compactCertificate286.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1435555641554679 / 4000000000000) 1 (IntervalRat.scale (321 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (42086186848 / 1000000000000) (42086186972 / 1000000000000), orderedInterval (1558212155 / 1000000000000) (1558212279 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (828818436088191 / 4000000000000) 1 (IntervalRat.scale (321 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (33292523314 / 1000000000000) (33292523315 / 1000000000000), orderedInterval (44237055759 / 1000000000000) (44237055760 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1470752859212619 / 4000000000000) 1 (IntervalRat.scale (321 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-32772932203 / 1000000000000) (-32772932202 / 1000000000000), orderedInterval (-25594203137 / 1000000000000) (-25594203136 / 1000000000000)))) (orderedInterval (-4722853237 / 1000000000000) (-4722853055 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1374168102119511 / 4000000000000) 1 (IntervalRat.scale (321 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-40826177239 / 1000000000000) (-40826169121 / 1000000000000), orderedInterval (13709615067 / 1000000000000) (13709623185 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (980671198720263 / 4000000000000) 1 (IntervalRat.scale (321 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (40182937286 / 1000000000000) (40182937287 / 1000000000000), orderedInterval (31254927080 / 1000000000000) (31254927081 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1111976618458977 / 4000000000000) 1 (IntervalRat.scale (321 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (35074686834 / 1000000000000) (35074733169 / 1000000000000), orderedInterval (-32617857143 / 1000000000000) (-32617810808 / 1000000000000)))) (orderedInterval (4270823145 / 1000000000000) (4270823897 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (927050175080913 / 4000000000000) 1 (IntervalRat.scale (321 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (3642011940 / 1000000000000) (3642011941 / 1000000000000), orderedInterval (52276024534 / 1000000000000) (52276024535 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (819076944295173 / 4000000000000) 1 (IntervalRat.scale (321 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-54410481847 / 1000000000000) (-54410481844 / 1000000000000), orderedInterval (-12051274884 / 1000000000000) (-12051274881 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (237400423514127 / 800000000000) 1 (IntervalRat.scale (321 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (36731838216 / 1000000000000) (36731933526 / 1000000000000), orderedInterval (-28276658589 / 1000000000000) (-28276563279 / 1000000000000)))) (orderedInterval (412969411 / 1000000000000) (412973946 / 1000000000000))) = true
  rfl'

theorem compactCertificate286_chunkChecks1_2 :
    compactCertificate286.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (656662065139869 / 4000000000000) 1 (IntervalRat.scale (321 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (62264239343 / 1000000000000) (62264239411 / 1000000000000), orderedInterval (-1219506562 / 1000000000000) (-1219506495 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (556659704952309 / 4000000000000) 1 (IntervalRat.scale (321 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (66890435032 / 1000000000000) (66890435375 / 1000000000000), orderedInterval (-10250918966 / 1000000000000) (-10250918622 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (348331796820327 / 4000000000000) 1 (IntervalRat.scale (321 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-8338629516 / 1000000000000) (-8338629483 / 1000000000000), orderedInterval (85142434936 / 1000000000000) (85142434968 / 1000000000000)))) (orderedInterval (2206441651 / 1000000000000) (2206441718 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (187333998829209 / 4000000000000) 1 (IntervalRat.scale (321 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-55109294830 / 1000000000000) (-55109294829 / 1000000000000), orderedInterval (-102157274488 / 1000000000000) (-102157274487 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (508648248474627 / 4000000000000) 1 (IntervalRat.scale (321 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (53566958030 / 1000000000000) (53567063915 / 1000000000000), orderedInterval (-46437666166 / 1000000000000) (-46437560282 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (694515697615779 / 4000000000000) 1 (IntervalRat.scale (321 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-60459685319 / 1000000000000) (-60459685195 / 1000000000000), orderedInterval (3515516295 / 1000000000000) (3515516419 / 1000000000000)))) (orderedInterval (1093659017 / 1000000000000) (1093660949 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (293668203179673 / 4000000000000) 1 (IntervalRat.scale (321 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-86704798524 / 1000000000000) (-86704795195 / 1000000000000), orderedInterval (34552359152 / 1000000000000) (34552362482 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1193744941954233 / 4000000000000) 1 (IntervalRat.scale (321 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-32149076447 / 1000000000000) (-32149076446 / 1000000000000), orderedInterval (-33106689695 / 1000000000000) (-33106689694 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (797366298233847 / 4000000000000) 1 (IntervalRat.scale (321 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-45489109560 / 1000000000000) (-45489034300 / 1000000000000), orderedInterval (33645444782 / 1000000000000) (33645520042 / 1000000000000)))) (orderedInterval (-2734211265 / 1000000000000) (-2734193654 / 1000000000000))) = true
  rfl'

theorem compactCertificate286_chunkChecks1 :
    compactCertificate286.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate286.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate286_chunkChecks1_0
    compactCertificate286_chunkChecks1_1 compactCertificate286_chunkChecks1_2

theorem compactCertificate286_chunkChecks2_0 :
    compactCertificate286.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (321 / 2) 2 (IntervalRat.scale (321 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-55044983086 / 1000000000000) (-55044983085 / 1000000000000), orderedInterval (-30431103752 / 1000000000000) (-30431103751 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (472894294276221 / 4000000000000) 2 (IntervalRat.scale (321 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-26714079047 / 1000000000000) (-26714077983 / 1000000000000), orderedInterval (68459694176 / 1000000000000) (68459695240 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (152924298542493 / 800000000000) 2 (IntervalRat.scale (321 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-17217696083 / 1000000000000) (-17217696082 / 1000000000000), orderedInterval (-55036167669 / 1000000000000) (-55036167668 / 1000000000000)))) (orderedInterval (23482318756 / 1000000000000) (23482318778 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (137989375654647 / 4000000000000) 2 (IntervalRat.scale (321 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-89733536869 / 1000000000000) (-89733536868 / 1000000000000), orderedInterval (-100691384764 / 1000000000000) (-100691384763 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (370658872819659 / 4000000000000) 2 (IntervalRat.scale (321 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-59401536347 / 1000000000000) (-59401451780 / 1000000000000), orderedInterval (58127051283 / 1000000000000) (58127135850 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1006410943124703 / 4000000000000) 2 (IntervalRat.scale (321 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (43886420176 / 1000000000000) (43886420177 / 1000000000000), orderedInterval (24494024697 / 1000000000000) (24494024698 / 1000000000000)))) (orderedInterval (8352737128 / 1000000000000) (8352738199 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (741317745639639 / 4000000000000) 2 (IntervalRat.scale (321 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-40385474878 / 1000000000000) (-40385474877 / 1000000000000), orderedInterval (-42365567228 / 1000000000000) (-42365567227 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1270260592509747 / 4000000000000) 2 (IntervalRat.scale (321 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-38822058892 / 1000000000000) (-38822058891 / 1000000000000), orderedInterval (-22244408383 / 1000000000000) (-22244408382 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (935668203179673 / 4000000000000) 2 (IntervalRat.scale (321 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (41427267185 / 1000000000000) (41427368737 / 1000000000000), orderedInterval (-31795659209 / 1000000000000) (-31795557657 / 1000000000000)))) (orderedInterval (-6815915332 / 1000000000000) (-6815910067 / 1000000000000))) = true
  rfl'

theorem compactCertificate286_chunkChecks2_1 :
    compactCertificate286.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1435555641554679 / 4000000000000) 2 (IntervalRat.scale (321 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (42086186848 / 1000000000000) (42086186972 / 1000000000000), orderedInterval (1558212155 / 1000000000000) (1558212279 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (828818436088191 / 4000000000000) 2 (IntervalRat.scale (321 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (33292523314 / 1000000000000) (33292523315 / 1000000000000), orderedInterval (44237055759 / 1000000000000) (44237055760 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1470752859212619 / 4000000000000) 2 (IntervalRat.scale (321 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-32772932203 / 1000000000000) (-32772932202 / 1000000000000), orderedInterval (-25594203137 / 1000000000000) (-25594203136 / 1000000000000)))) (orderedInterval (57759891423 / 1000000000000) (57759891818 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1374168102119511 / 4000000000000) 2 (IntervalRat.scale (321 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-40826177239 / 1000000000000) (-40826169121 / 1000000000000), orderedInterval (13709615067 / 1000000000000) (13709623185 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (980671198720263 / 4000000000000) 2 (IntervalRat.scale (321 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (40182937286 / 1000000000000) (40182937287 / 1000000000000), orderedInterval (31254927080 / 1000000000000) (31254927081 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1111976618458977 / 4000000000000) 2 (IntervalRat.scale (321 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (35074686834 / 1000000000000) (35074733169 / 1000000000000), orderedInterval (-32617857143 / 1000000000000) (-32617810808 / 1000000000000)))) (orderedInterval (-11737104392 / 1000000000000) (-11737102961 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (927050175080913 / 4000000000000) 2 (IntervalRat.scale (321 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (3642011940 / 1000000000000) (3642011941 / 1000000000000), orderedInterval (52276024534 / 1000000000000) (52276024535 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (819076944295173 / 4000000000000) 2 (IntervalRat.scale (321 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-54410481847 / 1000000000000) (-54410481844 / 1000000000000), orderedInterval (-12051274884 / 1000000000000) (-12051274881 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (237400423514127 / 800000000000) 2 (IntervalRat.scale (321 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (36731838216 / 1000000000000) (36731933526 / 1000000000000), orderedInterval (-28276658589 / 1000000000000) (-28276563279 / 1000000000000)))) (orderedInterval (-8373565832 / 1000000000000) (-8373557428 / 1000000000000))) = true
  rfl'

theorem compactCertificate286_chunkChecks2_2 :
    compactCertificate286.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (656662065139869 / 4000000000000) 2 (IntervalRat.scale (321 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (62264239343 / 1000000000000) (62264239411 / 1000000000000), orderedInterval (-1219506562 / 1000000000000) (-1219506495 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (556659704952309 / 4000000000000) 2 (IntervalRat.scale (321 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (66890435032 / 1000000000000) (66890435375 / 1000000000000), orderedInterval (-10250918966 / 1000000000000) (-10250918622 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (348331796820327 / 4000000000000) 2 (IntervalRat.scale (321 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-8338629516 / 1000000000000) (-8338629483 / 1000000000000), orderedInterval (85142434936 / 1000000000000) (85142434968 / 1000000000000)))) (orderedInterval (13328034262 / 1000000000000) (13328034325 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (187333998829209 / 4000000000000) 2 (IntervalRat.scale (321 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-55109294830 / 1000000000000) (-55109294829 / 1000000000000), orderedInterval (-102157274488 / 1000000000000) (-102157274487 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (508648248474627 / 4000000000000) 2 (IntervalRat.scale (321 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (53566958030 / 1000000000000) (53567063915 / 1000000000000), orderedInterval (-46437666166 / 1000000000000) (-46437560282 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (694515697615779 / 4000000000000) 2 (IntervalRat.scale (321 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-60459685319 / 1000000000000) (-60459685195 / 1000000000000), orderedInterval (3515516295 / 1000000000000) (3515516419 / 1000000000000)))) (orderedInterval (-4753231629 / 1000000000000) (-4753230080 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (293668203179673 / 4000000000000) 2 (IntervalRat.scale (321 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-86704798524 / 1000000000000) (-86704795195 / 1000000000000), orderedInterval (34552359152 / 1000000000000) (34552362482 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1193744941954233 / 4000000000000) 2 (IntervalRat.scale (321 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-32149076447 / 1000000000000) (-32149076446 / 1000000000000), orderedInterval (-33106689695 / 1000000000000) (-33106689694 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (797366298233847 / 4000000000000) 2 (IntervalRat.scale (321 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-45489109560 / 1000000000000) (-45489034300 / 1000000000000), orderedInterval (33645444782 / 1000000000000) (33645520042 / 1000000000000)))) (orderedInterval (-22087460671 / 1000000000000) (-22087438682 / 1000000000000))) = true
  rfl'

theorem compactCertificate286_chunkChecks2 :
    compactCertificate286.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate286.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate286_chunkChecks2_0
    compactCertificate286_chunkChecks2_1 compactCertificate286_chunkChecks2_2

theorem compactCertificate286_chunkChecks3_0 :
    compactCertificate286.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (321 / 2) 3 (IntervalRat.scale (321 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-55044983086 / 1000000000000) (-55044983085 / 1000000000000), orderedInterval (-30431103752 / 1000000000000) (-30431103751 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (472894294276221 / 4000000000000) 3 (IntervalRat.scale (321 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-26714079047 / 1000000000000) (-26714077983 / 1000000000000), orderedInterval (68459694176 / 1000000000000) (68459695240 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (152924298542493 / 800000000000) 3 (IntervalRat.scale (321 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-17217696083 / 1000000000000) (-17217696082 / 1000000000000), orderedInterval (-55036167669 / 1000000000000) (-55036167668 / 1000000000000)))) (orderedInterval (17116057227 / 1000000000000) (17116057249 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (137989375654647 / 4000000000000) 3 (IntervalRat.scale (321 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-89733536869 / 1000000000000) (-89733536868 / 1000000000000), orderedInterval (-100691384764 / 1000000000000) (-100691384763 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (370658872819659 / 4000000000000) 3 (IntervalRat.scale (321 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-59401536347 / 1000000000000) (-59401451780 / 1000000000000), orderedInterval (58127051283 / 1000000000000) (58127135850 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1006410943124703 / 4000000000000) 3 (IntervalRat.scale (321 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (43886420176 / 1000000000000) (43886420177 / 1000000000000), orderedInterval (24494024697 / 1000000000000) (24494024698 / 1000000000000)))) (orderedInterval (6236533302 / 1000000000000) (6236533949 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (741317745639639 / 4000000000000) 3 (IntervalRat.scale (321 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-40385474878 / 1000000000000) (-40385474877 / 1000000000000), orderedInterval (-42365567228 / 1000000000000) (-42365567227 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1270260592509747 / 4000000000000) 3 (IntervalRat.scale (321 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-38822058892 / 1000000000000) (-38822058891 / 1000000000000), orderedInterval (-22244408383 / 1000000000000) (-22244408382 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (935668203179673 / 4000000000000) 3 (IntervalRat.scale (321 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (41427267185 / 1000000000000) (41427368737 / 1000000000000), orderedInterval (-31795659209 / 1000000000000) (-31795557657 / 1000000000000)))) (orderedInterval (-2893199146 / 1000000000000) (-2893191464 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate286_chunkChecks3_1 :
    compactCertificate286.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1435555641554679 / 4000000000000) 3 (IntervalRat.scale (321 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (42086186848 / 1000000000000) (42086186972 / 1000000000000), orderedInterval (1558212155 / 1000000000000) (1558212279 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (828818436088191 / 4000000000000) 3 (IntervalRat.scale (321 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (33292523314 / 1000000000000) (33292523315 / 1000000000000), orderedInterval (44237055759 / 1000000000000) (44237055760 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1470752859212619 / 4000000000000) 3 (IntervalRat.scale (321 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-32772932203 / 1000000000000) (-32772932202 / 1000000000000), orderedInterval (-25594203137 / 1000000000000) (-25594203136 / 1000000000000)))) (orderedInterval (39427429333 / 1000000000000) (39427430202 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1374168102119511 / 4000000000000) 3 (IntervalRat.scale (321 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-40826177239 / 1000000000000) (-40826169121 / 1000000000000), orderedInterval (13709615067 / 1000000000000) (13709623185 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (980671198720263 / 4000000000000) 3 (IntervalRat.scale (321 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (40182937286 / 1000000000000) (40182937287 / 1000000000000), orderedInterval (31254927080 / 1000000000000) (31254927081 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1111976618458977 / 4000000000000) 3 (IntervalRat.scale (321 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (35074686834 / 1000000000000) (35074733169 / 1000000000000), orderedInterval (-32617857143 / 1000000000000) (-32617810808 / 1000000000000)))) (orderedInterval (-8891556047 / 1000000000000) (-8891553295 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (927050175080913 / 4000000000000) 3 (IntervalRat.scale (321 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (3642011940 / 1000000000000) (3642011941 / 1000000000000), orderedInterval (52276024534 / 1000000000000) (52276024535 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (819076944295173 / 4000000000000) 3 (IntervalRat.scale (321 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-54410481847 / 1000000000000) (-54410481844 / 1000000000000), orderedInterval (-12051274884 / 1000000000000) (-12051274881 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (237400423514127 / 800000000000) 3 (IntervalRat.scale (321 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (36731838216 / 1000000000000) (36731933526 / 1000000000000), orderedInterval (-28276658589 / 1000000000000) (-28276563279 / 1000000000000)))) (orderedInterval (1378352596 / 1000000000000) (1378368124 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate286_chunkChecks3_2 :
    compactCertificate286.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (656662065139869 / 4000000000000) 3 (IntervalRat.scale (321 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (62264239343 / 1000000000000) (62264239411 / 1000000000000), orderedInterval (-1219506562 / 1000000000000) (-1219506495 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (556659704952309 / 4000000000000) 3 (IntervalRat.scale (321 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (66890435032 / 1000000000000) (66890435375 / 1000000000000), orderedInterval (-10250918966 / 1000000000000) (-10250918622 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (348331796820327 / 4000000000000) 3 (IntervalRat.scale (321 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-8338629516 / 1000000000000) (-8338629483 / 1000000000000), orderedInterval (85142434936 / 1000000000000) (85142434968 / 1000000000000)))) (orderedInterval (-1112563594 / 1000000000000) (-1112563534 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (187333998829209 / 4000000000000) 3 (IntervalRat.scale (321 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-55109294830 / 1000000000000) (-55109294829 / 1000000000000), orderedInterval (-102157274488 / 1000000000000) (-102157274487 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (508648248474627 / 4000000000000) 3 (IntervalRat.scale (321 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (53566958030 / 1000000000000) (53567063915 / 1000000000000), orderedInterval (-46437666166 / 1000000000000) (-46437560282 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (694515697615779 / 4000000000000) 3 (IntervalRat.scale (321 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-60459685319 / 1000000000000) (-60459685195 / 1000000000000), orderedInterval (3515516295 / 1000000000000) (3515516419 / 1000000000000)))) (orderedInterval (-200064252 / 1000000000000) (-200063017 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (293668203179673 / 4000000000000) 3 (IntervalRat.scale (321 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-86704798524 / 1000000000000) (-86704795195 / 1000000000000), orderedInterval (34552359152 / 1000000000000) (34552362482 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1193744941954233 / 4000000000000) 3 (IntervalRat.scale (321 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-32149076447 / 1000000000000) (-32149076446 / 1000000000000), orderedInterval (-33106689695 / 1000000000000) (-33106689694 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (797366298233847 / 4000000000000) 3 (IntervalRat.scale (321 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-45489109560 / 1000000000000) (-45489034300 / 1000000000000), orderedInterval (33645444782 / 1000000000000) (33645520042 / 1000000000000)))) (orderedInterval (-5113131543 / 1000000000000) (-5113104209 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate286_chunkChecks3 :
    compactCertificate286.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate286.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate286_chunkChecks3_0
    compactCertificate286_chunkChecks3_1 compactCertificate286_chunkChecks3_2

theorem compactCertificate286_chunkChecks4_0 :
    compactCertificate286.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (321 / 2) 4 (IntervalRat.scale (321 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-55044983086 / 1000000000000) (-55044983085 / 1000000000000), orderedInterval (-30431103752 / 1000000000000) (-30431103751 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (472894294276221 / 4000000000000) 4 (IntervalRat.scale (321 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-26714079047 / 1000000000000) (-26714077983 / 1000000000000), orderedInterval (68459694176 / 1000000000000) (68459695240 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (152924298542493 / 800000000000) 4 (IntervalRat.scale (321 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-17217696083 / 1000000000000) (-17217696082 / 1000000000000), orderedInterval (-55036167669 / 1000000000000) (-55036167668 / 1000000000000)))) (orderedInterval (-24136468825 / 1000000000000) (-24136468801 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (137989375654647 / 4000000000000) 4 (IntervalRat.scale (321 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-89733536869 / 1000000000000) (-89733536868 / 1000000000000), orderedInterval (-100691384764 / 1000000000000) (-100691384763 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (370658872819659 / 4000000000000) 4 (IntervalRat.scale (321 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-59401536347 / 1000000000000) (-59401451780 / 1000000000000), orderedInterval (58127051283 / 1000000000000) (58127135850 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1006410943124703 / 4000000000000) 4 (IntervalRat.scale (321 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (43886420176 / 1000000000000) (43886420177 / 1000000000000), orderedInterval (24494024697 / 1000000000000) (24494024698 / 1000000000000)))) (orderedInterval (-19157027069 / 1000000000000) (-19157026648 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (741317745639639 / 4000000000000) 4 (IntervalRat.scale (321 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-40385474878 / 1000000000000) (-40385474877 / 1000000000000), orderedInterval (-42365567228 / 1000000000000) (-42365567227 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1270260592509747 / 4000000000000) 4 (IntervalRat.scale (321 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-38822058892 / 1000000000000) (-38822058891 / 1000000000000), orderedInterval (-22244408383 / 1000000000000) (-22244408382 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (935668203179673 / 4000000000000) 4 (IntervalRat.scale (321 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (41427267185 / 1000000000000) (41427368737 / 1000000000000), orderedInterval (-31795659209 / 1000000000000) (-31795557657 / 1000000000000)))) (orderedInterval (22904920885 / 1000000000000) (22904932147 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate286_chunkChecks4_1 :
    compactCertificate286.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1435555641554679 / 4000000000000) 4 (IntervalRat.scale (321 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (42086186848 / 1000000000000) (42086186972 / 1000000000000), orderedInterval (1558212155 / 1000000000000) (1558212279 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (828818436088191 / 4000000000000) 4 (IntervalRat.scale (321 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (33292523314 / 1000000000000) (33292523315 / 1000000000000), orderedInterval (44237055759 / 1000000000000) (44237055760 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1470752859212619 / 4000000000000) 4 (IntervalRat.scale (321 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-32772932203 / 1000000000000) (-32772932202 / 1000000000000), orderedInterval (-25594203137 / 1000000000000) (-25594203136 / 1000000000000)))) (orderedInterval (-308913628289 / 1000000000000) (-308913626355 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1374168102119511 / 4000000000000) 4 (IntervalRat.scale (321 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-40826177239 / 1000000000000) (-40826169121 / 1000000000000), orderedInterval (13709615067 / 1000000000000) (13709623185 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (980671198720263 / 4000000000000) 4 (IntervalRat.scale (321 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (40182937286 / 1000000000000) (40182937287 / 1000000000000), orderedInterval (31254927080 / 1000000000000) (31254927081 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1111976618458977 / 4000000000000) 4 (IntervalRat.scale (321 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (35074686834 / 1000000000000) (35074733169 / 1000000000000), orderedInterval (-32617857143 / 1000000000000) (-32617810808 / 1000000000000)))) (orderedInterval (34671411599 / 1000000000000) (34671416971 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (927050175080913 / 4000000000000) 4 (IntervalRat.scale (321 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (3642011940 / 1000000000000) (3642011941 / 1000000000000), orderedInterval (52276024534 / 1000000000000) (52276024535 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (819076944295173 / 4000000000000) 4 (IntervalRat.scale (321 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-54410481847 / 1000000000000) (-54410481844 / 1000000000000), orderedInterval (-12051274884 / 1000000000000) (-12051274881 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (237400423514127 / 800000000000) 4 (IntervalRat.scale (321 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (36731838216 / 1000000000000) (36731933526 / 1000000000000), orderedInterval (-28276658589 / 1000000000000) (-28276563279 / 1000000000000)))) (orderedInterval (19405536253 / 1000000000000) (19405565043 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate286_chunkChecks4_2 :
    compactCertificate286.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (656662065139869 / 4000000000000) 4 (IntervalRat.scale (321 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (62264239343 / 1000000000000) (62264239411 / 1000000000000), orderedInterval (-1219506562 / 1000000000000) (-1219506495 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (556659704952309 / 4000000000000) 4 (IntervalRat.scale (321 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (66890435032 / 1000000000000) (66890435375 / 1000000000000), orderedInterval (-10250918966 / 1000000000000) (-10250918622 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (348331796820327 / 4000000000000) 4 (IntervalRat.scale (321 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-8338629516 / 1000000000000) (-8338629483 / 1000000000000), orderedInterval (85142434936 / 1000000000000) (85142434968 / 1000000000000)))) (orderedInterval (-13045754023 / 1000000000000) (-13045753965 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (187333998829209 / 4000000000000) 4 (IntervalRat.scale (321 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-55109294830 / 1000000000000) (-55109294829 / 1000000000000), orderedInterval (-102157274488 / 1000000000000) (-102157274487 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (508648248474627 / 4000000000000) 4 (IntervalRat.scale (321 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (53566958030 / 1000000000000) (53567063915 / 1000000000000), orderedInterval (-46437666166 / 1000000000000) (-46437560282 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (694515697615779 / 4000000000000) 4 (IntervalRat.scale (321 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-60459685319 / 1000000000000) (-60459685195 / 1000000000000), orderedInterval (3515516295 / 1000000000000) (3515516419 / 1000000000000)))) (orderedInterval (5876877126 / 1000000000000) (5876878119 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (293668203179673 / 4000000000000) 4 (IntervalRat.scale (321 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-86704798524 / 1000000000000) (-86704795195 / 1000000000000), orderedInterval (34552359152 / 1000000000000) (34552362482 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1193744941954233 / 4000000000000) 4 (IntervalRat.scale (321 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-32149076447 / 1000000000000) (-32149076446 / 1000000000000), orderedInterval (-33106689695 / 1000000000000) (-33106689694 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (797366298233847 / 4000000000000) 4 (IntervalRat.scale (321 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-45489109560 / 1000000000000) (-45489034300 / 1000000000000), orderedInterval (33645444782 / 1000000000000) (33645520042 / 1000000000000)))) (orderedInterval (51632156275 / 1000000000000) (51632190441 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate286_chunkChecks4 :
    compactCertificate286.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate286.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate286_chunkChecks4_0
    compactCertificate286_chunkChecks4_1 compactCertificate286_chunkChecks4_2

theorem compactCertificate286_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate286.chunkCheck r b = true :=
  compactCertificate286.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate286_chunkChecks0
    · exact compactCertificate286_chunkChecks1
    · exact compactCertificate286_chunkChecks2
    · exact compactCertificate286_chunkChecks3
    · exact compactCertificate286_chunkChecks4)

theorem compactCertificate286_coefficient0 :
    compactCertificate286.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate286_coefficient1 :
    compactCertificate286.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate286_coefficient2 :
    compactCertificate286.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate286_coefficient3 :
    compactCertificate286.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate286_coefficient4 :
    compactCertificate286.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate286_coefficients : ∀ r : Fin 5,
    compactCertificate286.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate286_coefficient0
  · exact compactCertificate286_coefficient1
  · exact compactCertificate286_coefficient2
  · exact compactCertificate286_coefficient3
  · exact compactCertificate286_coefficient4

theorem compactCertificate286_lower : (1 : ℚ) ≤ compactCertificate286.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate286, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate286_proves {t : ℝ} (ht : t ∈ compactCertificate286.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate286.proves compactCertificate286_states compactCertificate286_chunks
    compactCertificate286_coefficients compactCertificate286_lower ht

end Erdos232
