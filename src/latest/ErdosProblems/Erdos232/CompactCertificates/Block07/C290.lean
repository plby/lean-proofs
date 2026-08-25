/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate290 : CompactCertificate where
  left := 164
  right := 165
  center := 329 / 2
  grid := fun i =>
    match i.val with
    | 0 => 52
    | 1 => 39
    | 2 => 62
    | 3 => 11
    | 4 => 30
    | 5 => 82
    | 6 => 60
    | 7 => 104
    | 8 => 76
    | 9 => 117
    | 10 => 68
    | 11 => 120
    | 12 => 112
    | 13 => 80
    | 14 => 91
    | 15 => 76
    | 16 => 67
    | 17 => 97
    | 18 => 54
    | 19 => 45
    | 20 => 28
    | 21 => 15
    | 22 => 42
    | 23 => 57
    | 24 => 24
    | 25 => 97
    | _ => 65
  point := fun i =>
    match i.val with
    | 0 => 329 / 2
    | 1 => 484679821859429 / 4000000000000
    | 2 => 156735496013957 / 800000000000
    | 3 => 141428363209903 / 4000000000000
    | 4 => 379896477126691 / 4000000000000
    | 5 => 1031492835788247 / 4000000000000
    | 6 => 759792954253711 / 4000000000000
    | 7 => 1301918177369803 / 4000000000000
    | 8 => 958987036903777 / 4000000000000
    | 9 => 1471332729194671 / 4000000000000
    | 10 => 849474347267959 / 4000000000000
    | 11 => 1507407136077731 / 4000000000000
    | 12 => 1408415282234639 / 4000000000000
    | 13 => 1005111602426687 / 4000000000000
    | 14 => 1139689431380073 / 4000000000000
    | 15 => 950154229288537 / 4000000000000
    | 16 => 839490076863277 / 4000000000000
    | 17 => 243316944972423 / 800000000000
    | 18 => 673027474862981 / 4000000000000
    | 19 => 570532844016541 / 4000000000000
    | 20 => 357012963096223 / 4000000000000
    | 21 => 192002758924641 / 4000000000000
    | 22 => 521324840336923 / 4000000000000
    | 23 => 711824500048571 / 4000000000000
    | 24 => 300987036903777 / 4000000000000
    | 25 => 1223495594713217 / 4000000000000
    | _ => 817238355510703 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (58415949596 / 1000000000000) (58415953857 / 1000000000000), orderedInterval (-21568955127 / 1000000000000) (-21568950866 / 1000000000000))
    | 1 => (orderedInterval (38979686372 / 1000000000000) (38979695176 / 1000000000000), orderedInterval (-61271758811 / 1000000000000) (-61271750007 / 1000000000000))
    | 2 => (orderedInterval (53457156204 / 1000000000000) (53457161433 / 1000000000000), orderedInterval (-19928368870 / 1000000000000) (-19928363640 / 1000000000000))
    | 3 => (orderedInterval (-134170035146 / 1000000000000) (-134170035122 / 1000000000000), orderedInterval (3324684930 / 1000000000000) (3324684954 / 1000000000000))
    | 4 => (orderedInterval (81722644788 / 1000000000000) (81722644801 / 1000000000000), orderedInterval (4509816481 / 1000000000000) (4509816493 / 1000000000000))
    | 5 => (orderedInterval (43037713728 / 1000000000000) (43037713729 / 1000000000000), orderedInterval (24745660815 / 1000000000000) (24745660816 / 1000000000000))
    | 6 => (orderedInterval (45498422084 / 1000000000000) (45498516414 / 1000000000000), orderedInterval (-35916874365 / 1000000000000) (-35916780036 / 1000000000000))
    | 7 => (orderedInterval (-19676751935 / 1000000000000) (-19676751056 / 1000000000000), orderedInterval (39637939137 / 1000000000000) (39637940017 / 1000000000000))
    | 8 => (orderedInterval (50505254451 / 1000000000000) (50505255653 / 1000000000000), orderedInterval (-10332654568 / 1000000000000) (-10332653366 / 1000000000000))
    | 9 => (orderedInterval (-36125825742 / 1000000000000) (-36125825741 / 1000000000000), orderedInterval (-20582265350 / 1000000000000) (-20582265349 / 1000000000000))
    | 10 => (orderedInterval (-25035197283 / 1000000000000) (-25035195274 / 1000000000000), orderedInterval (48751398355 / 1000000000000) (48751400364 / 1000000000000))
    | 11 => (orderedInterval (24734018916 / 1000000000000) (24734018917 / 1000000000000), orderedInterval (32793079821 / 1000000000000) (32793079822 / 1000000000000))
    | 12 => (orderedInterval (36463940375 / 1000000000000) (36463940376 / 1000000000000), orderedInterval (21821167207 / 1000000000000) (21821167208 / 1000000000000))
    | 13 => (orderedInterval (33767938254 / 1000000000000) (33767938255 / 1000000000000), orderedInterval (37259146337 / 1000000000000) (37259146338 / 1000000000000))
    | 14 => (orderedInterval (8351572605 / 1000000000000) (8351572629 / 1000000000000), orderedInterval (-46540097826 / 1000000000000) (-46540097801 / 1000000000000))
    | 15 => (orderedInterval (-21938706720 / 1000000000000) (-21938705591 / 1000000000000), orderedInterval (46937181659 / 1000000000000) (46937182788 / 1000000000000))
    | 16 => (orderedInterval (-9351198475 / 1000000000000) (-9351198474 / 1000000000000), orderedInterval (-54254119406 / 1000000000000) (-54254119405 / 1000000000000))
    | 17 => (orderedInterval (-8940408561 / 1000000000000) (-8940408560 / 1000000000000), orderedInterval (-44854102234 / 1000000000000) (-44854102233 / 1000000000000))
    | 18 => (orderedInterval (-34958774096 / 1000000000000) (-34958764059 / 1000000000000), orderedInterval (50715228411 / 1000000000000) (50715238449 / 1000000000000))
    | 19 => (orderedInterval (-59403702244 / 1000000000000) (-59403688740 / 1000000000000), orderedInterval (30778145870 / 1000000000000) (30778159374 / 1000000000000))
    | 20 => (orderedInterval (74041159917 / 1000000000000) (74041173425 / 1000000000000), orderedInterval (-41042119243 / 1000000000000) (-41042105735 / 1000000000000))
    | 21 => (orderedInterval (-114707037201 / 1000000000000) (-114707037118 / 1000000000000), orderedInterval (11407909743 / 1000000000000) (11407909826 / 1000000000000))
    | 22 => (orderedInterval (-51632528687 / 1000000000000) (-51632433920 / 1000000000000), orderedInterval (47301252056 / 1000000000000) (47301346823 / 1000000000000))
    | 23 => (orderedInterval (19379176129 / 1000000000000) (19379176566 / 1000000000000), orderedInterval (-56639394457 / 1000000000000) (-56639394019 / 1000000000000))
    | 24 => (orderedInterval (54358048956 / 1000000000000) (54358048957 / 1000000000000), orderedInterval (73839131309 / 1000000000000) (73839131310 / 1000000000000))
    | 25 => (orderedInterval (-42798833664 / 1000000000000) (-42798824512 / 1000000000000), orderedInterval (15867822814 / 1000000000000) (15867831966 / 1000000000000))
    | _ => (orderedInterval (-43406609598 / 1000000000000) (-43406609597 / 1000000000000), orderedInterval (-34991076362 / 1000000000000) (-34991076361 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (26654179370 / 1000000000000) (26654181460 / 1000000000000)
      | 1 => orderedInterval (1379950575 / 1000000000000) (1379950596 / 1000000000000)
      | 2 => orderedInterval (1827522077 / 1000000000000) (1827522144 / 1000000000000)
      | 3 => orderedInterval (8080307436 / 1000000000000) (8080307651 / 1000000000000)
      | 4 => orderedInterval (2492642591 / 1000000000000) (2492642611 / 1000000000000)
      | 5 => orderedInterval (52887287 / 1000000000000) (52887317 / 1000000000000)
      | 6 => orderedInterval (11362318329 / 1000000000000) (11362321180 / 1000000000000)
      | 7 => orderedInterval (1804258560 / 1000000000000) (1804260766 / 1000000000000)
      | _ => orderedInterval (11955819902 / 1000000000000) (11955820693 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-10362503685 / 1000000000000) (-10362501557 / 1000000000000)
      | 1 => orderedInterval (-2670377269 / 1000000000000) (-2670377246 / 1000000000000)
      | 2 => orderedInterval (-2782969206 / 1000000000000) (-2782969093 / 1000000000000)
      | 3 => orderedInterval (23520484748 / 1000000000000) (23520485077 / 1000000000000)
      | 4 => orderedInterval (4946702971 / 1000000000000) (4946703004 / 1000000000000)
      | 5 => orderedInterval (2620448605 / 1000000000000) (2620448647 / 1000000000000)
      | 6 => orderedInterval (-10529603900 / 1000000000000) (-10529601318 / 1000000000000)
      | 7 => orderedInterval (3784170541 / 1000000000000) (3784172299 / 1000000000000)
      | _ => orderedInterval (5955930952 / 1000000000000) (5955932402 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-27737781598 / 1000000000000) (-27737779401 / 1000000000000)
      | 1 => orderedInterval (6472959088 / 1000000000000) (6472959120 / 1000000000000)
      | 2 => orderedInterval (-4951740650 / 1000000000000) (-4951740452 / 1000000000000)
      | 3 => orderedInterval (-47600175319 / 1000000000000) (-47600174778 / 1000000000000)
      | 4 => orderedInterval (-4338109540 / 1000000000000) (-4338109486 / 1000000000000)
      | 5 => orderedInterval (423792121 / 1000000000000) (423792183 / 1000000000000)
      | 6 => orderedInterval (-9021237766 / 1000000000000) (-9021235331 / 1000000000000)
      | 7 => orderedInterval (799468166 / 1000000000000) (799469584 / 1000000000000)
      | _ => orderedInterval (-24713176396 / 1000000000000) (-24713173717 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (10921215787 / 1000000000000) (10921218058 / 1000000000000)
      | 1 => orderedInterval (6706047226 / 1000000000000) (6706047273 / 1000000000000)
      | 2 => orderedInterval (10273172689 / 1000000000000) (10273173043 / 1000000000000)
      | 3 => orderedInterval (-104418810301 / 1000000000000) (-104418809340 / 1000000000000)
      | 4 => orderedInterval (-9892019712 / 1000000000000) (-9892019621 / 1000000000000)
      | 5 => orderedInterval (-823401479 / 1000000000000) (-823401386 / 1000000000000)
      | 6 => orderedInterval (10080807764 / 1000000000000) (10080810101 / 1000000000000)
      | 7 => orderedInterval (-4961309885 / 1000000000000) (-4961308746 / 1000000000000)
      | _ => orderedInterval (-4166523302 / 1000000000000) (-4166518350 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (29438916401 / 1000000000000) (29438918779 / 1000000000000)
      | 1 => orderedInterval (-18223025110 / 1000000000000) (-18223025037 / 1000000000000)
      | 2 => orderedInterval (14683592514 / 1000000000000) (14683593161 / 1000000000000)
      | 3 => orderedInterval (253438567585 / 1000000000000) (253438569420 / 1000000000000)
      | 4 => orderedInterval (3307237886 / 1000000000000) (3307238043 / 1000000000000)
      | 5 => orderedInterval (-2348666521 / 1000000000000) (-2348666380 / 1000000000000)
      | 6 => orderedInterval (8104445806 / 1000000000000) (8104448095 / 1000000000000)
      | 7 => orderedInterval (-1496838138 / 1000000000000) (-1496837212 / 1000000000000)
      | _ => orderedInterval (61089396676 / 1000000000000) (61089405875 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (65609886127 / 1000000000000) (65609894418 / 1000000000000)
    | 1 => orderedInterval (14482283757 / 1000000000000) (14482292215 / 1000000000000)
    | 2 => orderedInterval (-110666001894 / 1000000000000) (-110665992278 / 1000000000000)
    | 3 => orderedInterval (-86280821213 / 1000000000000) (-86280808968 / 1000000000000)
    | _ => orderedInterval (347993627099 / 1000000000000) (347993644744 / 1000000000000)

theorem compactCertificate290_stateChecks0 :
    compactCertificate290.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 52 12 (329 / 2)) (orderedInterval (58415949596 / 1000000000000) (58415953857 / 1000000000000), orderedInterval (-21568955127 / 1000000000000) (-21568950866 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 39 12 (484679821859429 / 4000000000000)) (orderedInterval (38979686372 / 1000000000000) (38979695176 / 1000000000000), orderedInterval (-61271758811 / 1000000000000) (-61271750007 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (156735496013957 / 800000000000)) (orderedInterval (53457156204 / 1000000000000) (53457161433 / 1000000000000), orderedInterval (-19928368870 / 1000000000000) (-19928363640 / 1000000000000))) = true
  rfl'

theorem compactCertificate290_stateChecks1 :
    compactCertificate290.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 11 12 (141428363209903 / 4000000000000)) (orderedInterval (-134170035146 / 1000000000000) (-134170035122 / 1000000000000), orderedInterval (3324684930 / 1000000000000) (3324684954 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (379896477126691 / 4000000000000)) (orderedInterval (81722644788 / 1000000000000) (81722644801 / 1000000000000), orderedInterval (4509816481 / 1000000000000) (4509816493 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 82 12 (1031492835788247 / 4000000000000)) (orderedInterval (43037713728 / 1000000000000) (43037713729 / 1000000000000), orderedInterval (24745660815 / 1000000000000) (24745660816 / 1000000000000))) = true
  rfl'

theorem compactCertificate290_stateChecks2 :
    compactCertificate290.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 60 12 (759792954253711 / 4000000000000)) (orderedInterval (45498422084 / 1000000000000) (45498516414 / 1000000000000), orderedInterval (-35916874365 / 1000000000000) (-35916780036 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 104 12 (1301918177369803 / 4000000000000)) (orderedInterval (-19676751935 / 1000000000000) (-19676751056 / 1000000000000), orderedInterval (39637939137 / 1000000000000) (39637940017 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 76 12 (958987036903777 / 4000000000000)) (orderedInterval (50505254451 / 1000000000000) (50505255653 / 1000000000000), orderedInterval (-10332654568 / 1000000000000) (-10332653366 / 1000000000000))) = true
  rfl'

theorem compactCertificate290_stateChecks3 :
    compactCertificate290.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 117 12 (1471332729194671 / 4000000000000)) (orderedInterval (-36125825742 / 1000000000000) (-36125825741 / 1000000000000), orderedInterval (-20582265350 / 1000000000000) (-20582265349 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (849474347267959 / 4000000000000)) (orderedInterval (-25035197283 / 1000000000000) (-25035195274 / 1000000000000), orderedInterval (48751398355 / 1000000000000) (48751400364 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 120 12 (1507407136077731 / 4000000000000)) (orderedInterval (24734018916 / 1000000000000) (24734018917 / 1000000000000), orderedInterval (32793079821 / 1000000000000) (32793079822 / 1000000000000))) = true
  rfl'

theorem compactCertificate290_stateChecks4 :
    compactCertificate290.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 112 12 (1408415282234639 / 4000000000000)) (orderedInterval (36463940375 / 1000000000000) (36463940376 / 1000000000000), orderedInterval (21821167207 / 1000000000000) (21821167208 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 80 12 (1005111602426687 / 4000000000000)) (orderedInterval (33767938254 / 1000000000000) (33767938255 / 1000000000000), orderedInterval (37259146337 / 1000000000000) (37259146338 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 91 12 (1139689431380073 / 4000000000000)) (orderedInterval (8351572605 / 1000000000000) (8351572629 / 1000000000000), orderedInterval (-46540097826 / 1000000000000) (-46540097801 / 1000000000000))) = true
  rfl'

theorem compactCertificate290_stateChecks5 :
    compactCertificate290.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 76 12 (950154229288537 / 4000000000000)) (orderedInterval (-21938706720 / 1000000000000) (-21938705591 / 1000000000000), orderedInterval (46937181659 / 1000000000000) (46937182788 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (839490076863277 / 4000000000000)) (orderedInterval (-9351198475 / 1000000000000) (-9351198474 / 1000000000000), orderedInterval (-54254119406 / 1000000000000) (-54254119405 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 97 12 (243316944972423 / 800000000000)) (orderedInterval (-8940408561 / 1000000000000) (-8940408560 / 1000000000000), orderedInterval (-44854102234 / 1000000000000) (-44854102233 / 1000000000000))) = true
  rfl'

theorem compactCertificate290_stateChecks6 :
    compactCertificate290.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (673027474862981 / 4000000000000)) (orderedInterval (-34958774096 / 1000000000000) (-34958764059 / 1000000000000), orderedInterval (50715228411 / 1000000000000) (50715238449 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (570532844016541 / 4000000000000)) (orderedInterval (-59403702244 / 1000000000000) (-59403688740 / 1000000000000), orderedInterval (30778145870 / 1000000000000) (30778159374 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 28 12 (357012963096223 / 4000000000000)) (orderedInterval (74041159917 / 1000000000000) (74041173425 / 1000000000000), orderedInterval (-41042119243 / 1000000000000) (-41042105735 / 1000000000000))) = true
  rfl'

theorem compactCertificate290_stateChecks7 :
    compactCertificate290.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 15 12 (192002758924641 / 4000000000000)) (orderedInterval (-114707037201 / 1000000000000) (-114707037118 / 1000000000000), orderedInterval (11407909743 / 1000000000000) (11407909826 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 42 12 (521324840336923 / 4000000000000)) (orderedInterval (-51632528687 / 1000000000000) (-51632433920 / 1000000000000), orderedInterval (47301252056 / 1000000000000) (47301346823 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 57 12 (711824500048571 / 4000000000000)) (orderedInterval (19379176129 / 1000000000000) (19379176566 / 1000000000000), orderedInterval (-56639394457 / 1000000000000) (-56639394019 / 1000000000000))) = true
  rfl'

theorem compactCertificate290_stateChecks8 :
    compactCertificate290.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 24 12 (300987036903777 / 4000000000000)) (orderedInterval (54358048956 / 1000000000000) (54358048957 / 1000000000000), orderedInterval (73839131309 / 1000000000000) (73839131310 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 97 12 (1223495594713217 / 4000000000000)) (orderedInterval (-42798833664 / 1000000000000) (-42798824512 / 1000000000000), orderedInterval (15867822814 / 1000000000000) (15867831966 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 65 12 (817238355510703 / 4000000000000)) (orderedInterval (-43406609598 / 1000000000000) (-43406609597 / 1000000000000), orderedInterval (-34991076362 / 1000000000000) (-34991076361 / 1000000000000))) = true
  rfl'

theorem compactCertificate290_states : ∀ j,
    BesselStateValid (compactCertificate290.point j) (compactCertificate290.state j) :=
  compactCertificate290.statesValid_of_checks3 compactCertificate290_stateChecks0
    compactCertificate290_stateChecks1 compactCertificate290_stateChecks2
    compactCertificate290_stateChecks3 compactCertificate290_stateChecks4
    compactCertificate290_stateChecks5 compactCertificate290_stateChecks6
    compactCertificate290_stateChecks7 compactCertificate290_stateChecks8

theorem compactCertificate290_chunkChecks0_0 :
    compactCertificate290.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (329 / 2) 0 (IntervalRat.scale (329 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (58415949596 / 1000000000000) (58415953857 / 1000000000000), orderedInterval (-21568955127 / 1000000000000) (-21568950866 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (484679821859429 / 4000000000000) 0 (IntervalRat.scale (329 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (38979686372 / 1000000000000) (38979695176 / 1000000000000), orderedInterval (-61271758811 / 1000000000000) (-61271750007 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (156735496013957 / 800000000000) 0 (IntervalRat.scale (329 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (53457156204 / 1000000000000) (53457161433 / 1000000000000), orderedInterval (-19928368870 / 1000000000000) (-19928363640 / 1000000000000)))) (orderedInterval (26654179370 / 1000000000000) (26654181460 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (141428363209903 / 4000000000000) 0 (IntervalRat.scale (329 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-134170035146 / 1000000000000) (-134170035122 / 1000000000000), orderedInterval (3324684930 / 1000000000000) (3324684954 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (379896477126691 / 4000000000000) 0 (IntervalRat.scale (329 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (81722644788 / 1000000000000) (81722644801 / 1000000000000), orderedInterval (4509816481 / 1000000000000) (4509816493 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1031492835788247 / 4000000000000) 0 (IntervalRat.scale (329 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (43037713728 / 1000000000000) (43037713729 / 1000000000000), orderedInterval (24745660815 / 1000000000000) (24745660816 / 1000000000000)))) (orderedInterval (1379950575 / 1000000000000) (1379950596 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (759792954253711 / 4000000000000) 0 (IntervalRat.scale (329 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (45498422084 / 1000000000000) (45498516414 / 1000000000000), orderedInterval (-35916874365 / 1000000000000) (-35916780036 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1301918177369803 / 4000000000000) 0 (IntervalRat.scale (329 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-19676751935 / 1000000000000) (-19676751056 / 1000000000000), orderedInterval (39637939137 / 1000000000000) (39637940017 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (958987036903777 / 4000000000000) 0 (IntervalRat.scale (329 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (50505254451 / 1000000000000) (50505255653 / 1000000000000), orderedInterval (-10332654568 / 1000000000000) (-10332653366 / 1000000000000)))) (orderedInterval (1827522077 / 1000000000000) (1827522144 / 1000000000000))) = true
  rfl'

theorem compactCertificate290_chunkChecks0_1 :
    compactCertificate290.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1471332729194671 / 4000000000000) 0 (IntervalRat.scale (329 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-36125825742 / 1000000000000) (-36125825741 / 1000000000000), orderedInterval (-20582265350 / 1000000000000) (-20582265349 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (849474347267959 / 4000000000000) 0 (IntervalRat.scale (329 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-25035197283 / 1000000000000) (-25035195274 / 1000000000000), orderedInterval (48751398355 / 1000000000000) (48751400364 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1507407136077731 / 4000000000000) 0 (IntervalRat.scale (329 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (24734018916 / 1000000000000) (24734018917 / 1000000000000), orderedInterval (32793079821 / 1000000000000) (32793079822 / 1000000000000)))) (orderedInterval (8080307436 / 1000000000000) (8080307651 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1408415282234639 / 4000000000000) 0 (IntervalRat.scale (329 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (36463940375 / 1000000000000) (36463940376 / 1000000000000), orderedInterval (21821167207 / 1000000000000) (21821167208 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1005111602426687 / 4000000000000) 0 (IntervalRat.scale (329 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (33767938254 / 1000000000000) (33767938255 / 1000000000000), orderedInterval (37259146337 / 1000000000000) (37259146338 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1139689431380073 / 4000000000000) 0 (IntervalRat.scale (329 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (8351572605 / 1000000000000) (8351572629 / 1000000000000), orderedInterval (-46540097826 / 1000000000000) (-46540097801 / 1000000000000)))) (orderedInterval (2492642591 / 1000000000000) (2492642611 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (950154229288537 / 4000000000000) 0 (IntervalRat.scale (329 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-21938706720 / 1000000000000) (-21938705591 / 1000000000000), orderedInterval (46937181659 / 1000000000000) (46937182788 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (839490076863277 / 4000000000000) 0 (IntervalRat.scale (329 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-9351198475 / 1000000000000) (-9351198474 / 1000000000000), orderedInterval (-54254119406 / 1000000000000) (-54254119405 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (243316944972423 / 800000000000) 0 (IntervalRat.scale (329 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-8940408561 / 1000000000000) (-8940408560 / 1000000000000), orderedInterval (-44854102234 / 1000000000000) (-44854102233 / 1000000000000)))) (orderedInterval (52887287 / 1000000000000) (52887317 / 1000000000000))) = true
  rfl'

theorem compactCertificate290_chunkChecks0_2 :
    compactCertificate290.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (673027474862981 / 4000000000000) 0 (IntervalRat.scale (329 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-34958774096 / 1000000000000) (-34958764059 / 1000000000000), orderedInterval (50715228411 / 1000000000000) (50715238449 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (570532844016541 / 4000000000000) 0 (IntervalRat.scale (329 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-59403702244 / 1000000000000) (-59403688740 / 1000000000000), orderedInterval (30778145870 / 1000000000000) (30778159374 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (357012963096223 / 4000000000000) 0 (IntervalRat.scale (329 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (74041159917 / 1000000000000) (74041173425 / 1000000000000), orderedInterval (-41042119243 / 1000000000000) (-41042105735 / 1000000000000)))) (orderedInterval (11362318329 / 1000000000000) (11362321180 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (192002758924641 / 4000000000000) 0 (IntervalRat.scale (329 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-114707037201 / 1000000000000) (-114707037118 / 1000000000000), orderedInterval (11407909743 / 1000000000000) (11407909826 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (521324840336923 / 4000000000000) 0 (IntervalRat.scale (329 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-51632528687 / 1000000000000) (-51632433920 / 1000000000000), orderedInterval (47301252056 / 1000000000000) (47301346823 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (711824500048571 / 4000000000000) 0 (IntervalRat.scale (329 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (19379176129 / 1000000000000) (19379176566 / 1000000000000), orderedInterval (-56639394457 / 1000000000000) (-56639394019 / 1000000000000)))) (orderedInterval (1804258560 / 1000000000000) (1804260766 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (300987036903777 / 4000000000000) 0 (IntervalRat.scale (329 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (54358048956 / 1000000000000) (54358048957 / 1000000000000), orderedInterval (73839131309 / 1000000000000) (73839131310 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1223495594713217 / 4000000000000) 0 (IntervalRat.scale (329 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-42798833664 / 1000000000000) (-42798824512 / 1000000000000), orderedInterval (15867822814 / 1000000000000) (15867831966 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (817238355510703 / 4000000000000) 0 (IntervalRat.scale (329 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-43406609598 / 1000000000000) (-43406609597 / 1000000000000), orderedInterval (-34991076362 / 1000000000000) (-34991076361 / 1000000000000)))) (orderedInterval (11955819902 / 1000000000000) (11955820693 / 1000000000000))) = true
  rfl'

theorem compactCertificate290_chunkChecks0 :
    compactCertificate290.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate290.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate290_chunkChecks0_0
    compactCertificate290_chunkChecks0_1 compactCertificate290_chunkChecks0_2

theorem compactCertificate290_chunkChecks1_0 :
    compactCertificate290.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (329 / 2) 1 (IntervalRat.scale (329 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (58415949596 / 1000000000000) (58415953857 / 1000000000000), orderedInterval (-21568955127 / 1000000000000) (-21568950866 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (484679821859429 / 4000000000000) 1 (IntervalRat.scale (329 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (38979686372 / 1000000000000) (38979695176 / 1000000000000), orderedInterval (-61271758811 / 1000000000000) (-61271750007 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (156735496013957 / 800000000000) 1 (IntervalRat.scale (329 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (53457156204 / 1000000000000) (53457161433 / 1000000000000), orderedInterval (-19928368870 / 1000000000000) (-19928363640 / 1000000000000)))) (orderedInterval (-10362503685 / 1000000000000) (-10362501557 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (141428363209903 / 4000000000000) 1 (IntervalRat.scale (329 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-134170035146 / 1000000000000) (-134170035122 / 1000000000000), orderedInterval (3324684930 / 1000000000000) (3324684954 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (379896477126691 / 4000000000000) 1 (IntervalRat.scale (329 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (81722644788 / 1000000000000) (81722644801 / 1000000000000), orderedInterval (4509816481 / 1000000000000) (4509816493 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1031492835788247 / 4000000000000) 1 (IntervalRat.scale (329 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (43037713728 / 1000000000000) (43037713729 / 1000000000000), orderedInterval (24745660815 / 1000000000000) (24745660816 / 1000000000000)))) (orderedInterval (-2670377269 / 1000000000000) (-2670377246 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (759792954253711 / 4000000000000) 1 (IntervalRat.scale (329 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (45498422084 / 1000000000000) (45498516414 / 1000000000000), orderedInterval (-35916874365 / 1000000000000) (-35916780036 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1301918177369803 / 4000000000000) 1 (IntervalRat.scale (329 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-19676751935 / 1000000000000) (-19676751056 / 1000000000000), orderedInterval (39637939137 / 1000000000000) (39637940017 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (958987036903777 / 4000000000000) 1 (IntervalRat.scale (329 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (50505254451 / 1000000000000) (50505255653 / 1000000000000), orderedInterval (-10332654568 / 1000000000000) (-10332653366 / 1000000000000)))) (orderedInterval (-2782969206 / 1000000000000) (-2782969093 / 1000000000000))) = true
  rfl'

theorem compactCertificate290_chunkChecks1_1 :
    compactCertificate290.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1471332729194671 / 4000000000000) 1 (IntervalRat.scale (329 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-36125825742 / 1000000000000) (-36125825741 / 1000000000000), orderedInterval (-20582265350 / 1000000000000) (-20582265349 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (849474347267959 / 4000000000000) 1 (IntervalRat.scale (329 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-25035197283 / 1000000000000) (-25035195274 / 1000000000000), orderedInterval (48751398355 / 1000000000000) (48751400364 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1507407136077731 / 4000000000000) 1 (IntervalRat.scale (329 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (24734018916 / 1000000000000) (24734018917 / 1000000000000), orderedInterval (32793079821 / 1000000000000) (32793079822 / 1000000000000)))) (orderedInterval (23520484748 / 1000000000000) (23520485077 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1408415282234639 / 4000000000000) 1 (IntervalRat.scale (329 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (36463940375 / 1000000000000) (36463940376 / 1000000000000), orderedInterval (21821167207 / 1000000000000) (21821167208 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1005111602426687 / 4000000000000) 1 (IntervalRat.scale (329 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (33767938254 / 1000000000000) (33767938255 / 1000000000000), orderedInterval (37259146337 / 1000000000000) (37259146338 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1139689431380073 / 4000000000000) 1 (IntervalRat.scale (329 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (8351572605 / 1000000000000) (8351572629 / 1000000000000), orderedInterval (-46540097826 / 1000000000000) (-46540097801 / 1000000000000)))) (orderedInterval (4946702971 / 1000000000000) (4946703004 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (950154229288537 / 4000000000000) 1 (IntervalRat.scale (329 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-21938706720 / 1000000000000) (-21938705591 / 1000000000000), orderedInterval (46937181659 / 1000000000000) (46937182788 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (839490076863277 / 4000000000000) 1 (IntervalRat.scale (329 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-9351198475 / 1000000000000) (-9351198474 / 1000000000000), orderedInterval (-54254119406 / 1000000000000) (-54254119405 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (243316944972423 / 800000000000) 1 (IntervalRat.scale (329 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-8940408561 / 1000000000000) (-8940408560 / 1000000000000), orderedInterval (-44854102234 / 1000000000000) (-44854102233 / 1000000000000)))) (orderedInterval (2620448605 / 1000000000000) (2620448647 / 1000000000000))) = true
  rfl'

theorem compactCertificate290_chunkChecks1_2 :
    compactCertificate290.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (673027474862981 / 4000000000000) 1 (IntervalRat.scale (329 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-34958774096 / 1000000000000) (-34958764059 / 1000000000000), orderedInterval (50715228411 / 1000000000000) (50715238449 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (570532844016541 / 4000000000000) 1 (IntervalRat.scale (329 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-59403702244 / 1000000000000) (-59403688740 / 1000000000000), orderedInterval (30778145870 / 1000000000000) (30778159374 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (357012963096223 / 4000000000000) 1 (IntervalRat.scale (329 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (74041159917 / 1000000000000) (74041173425 / 1000000000000), orderedInterval (-41042119243 / 1000000000000) (-41042105735 / 1000000000000)))) (orderedInterval (-10529603900 / 1000000000000) (-10529601318 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (192002758924641 / 4000000000000) 1 (IntervalRat.scale (329 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-114707037201 / 1000000000000) (-114707037118 / 1000000000000), orderedInterval (11407909743 / 1000000000000) (11407909826 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (521324840336923 / 4000000000000) 1 (IntervalRat.scale (329 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-51632528687 / 1000000000000) (-51632433920 / 1000000000000), orderedInterval (47301252056 / 1000000000000) (47301346823 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (711824500048571 / 4000000000000) 1 (IntervalRat.scale (329 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (19379176129 / 1000000000000) (19379176566 / 1000000000000), orderedInterval (-56639394457 / 1000000000000) (-56639394019 / 1000000000000)))) (orderedInterval (3784170541 / 1000000000000) (3784172299 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (300987036903777 / 4000000000000) 1 (IntervalRat.scale (329 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (54358048956 / 1000000000000) (54358048957 / 1000000000000), orderedInterval (73839131309 / 1000000000000) (73839131310 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1223495594713217 / 4000000000000) 1 (IntervalRat.scale (329 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-42798833664 / 1000000000000) (-42798824512 / 1000000000000), orderedInterval (15867822814 / 1000000000000) (15867831966 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (817238355510703 / 4000000000000) 1 (IntervalRat.scale (329 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-43406609598 / 1000000000000) (-43406609597 / 1000000000000), orderedInterval (-34991076362 / 1000000000000) (-34991076361 / 1000000000000)))) (orderedInterval (5955930952 / 1000000000000) (5955932402 / 1000000000000))) = true
  rfl'

theorem compactCertificate290_chunkChecks1 :
    compactCertificate290.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate290.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate290_chunkChecks1_0
    compactCertificate290_chunkChecks1_1 compactCertificate290_chunkChecks1_2

theorem compactCertificate290_chunkChecks2_0 :
    compactCertificate290.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (329 / 2) 2 (IntervalRat.scale (329 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (58415949596 / 1000000000000) (58415953857 / 1000000000000), orderedInterval (-21568955127 / 1000000000000) (-21568950866 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (484679821859429 / 4000000000000) 2 (IntervalRat.scale (329 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (38979686372 / 1000000000000) (38979695176 / 1000000000000), orderedInterval (-61271758811 / 1000000000000) (-61271750007 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (156735496013957 / 800000000000) 2 (IntervalRat.scale (329 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (53457156204 / 1000000000000) (53457161433 / 1000000000000), orderedInterval (-19928368870 / 1000000000000) (-19928363640 / 1000000000000)))) (orderedInterval (-27737781598 / 1000000000000) (-27737779401 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (141428363209903 / 4000000000000) 2 (IntervalRat.scale (329 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-134170035146 / 1000000000000) (-134170035122 / 1000000000000), orderedInterval (3324684930 / 1000000000000) (3324684954 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (379896477126691 / 4000000000000) 2 (IntervalRat.scale (329 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (81722644788 / 1000000000000) (81722644801 / 1000000000000), orderedInterval (4509816481 / 1000000000000) (4509816493 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1031492835788247 / 4000000000000) 2 (IntervalRat.scale (329 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (43037713728 / 1000000000000) (43037713729 / 1000000000000), orderedInterval (24745660815 / 1000000000000) (24745660816 / 1000000000000)))) (orderedInterval (6472959088 / 1000000000000) (6472959120 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (759792954253711 / 4000000000000) 2 (IntervalRat.scale (329 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (45498422084 / 1000000000000) (45498516414 / 1000000000000), orderedInterval (-35916874365 / 1000000000000) (-35916780036 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1301918177369803 / 4000000000000) 2 (IntervalRat.scale (329 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-19676751935 / 1000000000000) (-19676751056 / 1000000000000), orderedInterval (39637939137 / 1000000000000) (39637940017 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (958987036903777 / 4000000000000) 2 (IntervalRat.scale (329 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (50505254451 / 1000000000000) (50505255653 / 1000000000000), orderedInterval (-10332654568 / 1000000000000) (-10332653366 / 1000000000000)))) (orderedInterval (-4951740650 / 1000000000000) (-4951740452 / 1000000000000))) = true
  rfl'

theorem compactCertificate290_chunkChecks2_1 :
    compactCertificate290.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1471332729194671 / 4000000000000) 2 (IntervalRat.scale (329 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-36125825742 / 1000000000000) (-36125825741 / 1000000000000), orderedInterval (-20582265350 / 1000000000000) (-20582265349 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (849474347267959 / 4000000000000) 2 (IntervalRat.scale (329 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-25035197283 / 1000000000000) (-25035195274 / 1000000000000), orderedInterval (48751398355 / 1000000000000) (48751400364 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1507407136077731 / 4000000000000) 2 (IntervalRat.scale (329 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (24734018916 / 1000000000000) (24734018917 / 1000000000000), orderedInterval (32793079821 / 1000000000000) (32793079822 / 1000000000000)))) (orderedInterval (-47600175319 / 1000000000000) (-47600174778 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1408415282234639 / 4000000000000) 2 (IntervalRat.scale (329 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (36463940375 / 1000000000000) (36463940376 / 1000000000000), orderedInterval (21821167207 / 1000000000000) (21821167208 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1005111602426687 / 4000000000000) 2 (IntervalRat.scale (329 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (33767938254 / 1000000000000) (33767938255 / 1000000000000), orderedInterval (37259146337 / 1000000000000) (37259146338 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1139689431380073 / 4000000000000) 2 (IntervalRat.scale (329 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (8351572605 / 1000000000000) (8351572629 / 1000000000000), orderedInterval (-46540097826 / 1000000000000) (-46540097801 / 1000000000000)))) (orderedInterval (-4338109540 / 1000000000000) (-4338109486 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (950154229288537 / 4000000000000) 2 (IntervalRat.scale (329 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-21938706720 / 1000000000000) (-21938705591 / 1000000000000), orderedInterval (46937181659 / 1000000000000) (46937182788 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (839490076863277 / 4000000000000) 2 (IntervalRat.scale (329 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-9351198475 / 1000000000000) (-9351198474 / 1000000000000), orderedInterval (-54254119406 / 1000000000000) (-54254119405 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (243316944972423 / 800000000000) 2 (IntervalRat.scale (329 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-8940408561 / 1000000000000) (-8940408560 / 1000000000000), orderedInterval (-44854102234 / 1000000000000) (-44854102233 / 1000000000000)))) (orderedInterval (423792121 / 1000000000000) (423792183 / 1000000000000))) = true
  rfl'

theorem compactCertificate290_chunkChecks2_2 :
    compactCertificate290.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (673027474862981 / 4000000000000) 2 (IntervalRat.scale (329 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-34958774096 / 1000000000000) (-34958764059 / 1000000000000), orderedInterval (50715228411 / 1000000000000) (50715238449 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (570532844016541 / 4000000000000) 2 (IntervalRat.scale (329 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-59403702244 / 1000000000000) (-59403688740 / 1000000000000), orderedInterval (30778145870 / 1000000000000) (30778159374 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (357012963096223 / 4000000000000) 2 (IntervalRat.scale (329 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (74041159917 / 1000000000000) (74041173425 / 1000000000000), orderedInterval (-41042119243 / 1000000000000) (-41042105735 / 1000000000000)))) (orderedInterval (-9021237766 / 1000000000000) (-9021235331 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (192002758924641 / 4000000000000) 2 (IntervalRat.scale (329 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-114707037201 / 1000000000000) (-114707037118 / 1000000000000), orderedInterval (11407909743 / 1000000000000) (11407909826 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (521324840336923 / 4000000000000) 2 (IntervalRat.scale (329 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-51632528687 / 1000000000000) (-51632433920 / 1000000000000), orderedInterval (47301252056 / 1000000000000) (47301346823 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (711824500048571 / 4000000000000) 2 (IntervalRat.scale (329 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (19379176129 / 1000000000000) (19379176566 / 1000000000000), orderedInterval (-56639394457 / 1000000000000) (-56639394019 / 1000000000000)))) (orderedInterval (799468166 / 1000000000000) (799469584 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (300987036903777 / 4000000000000) 2 (IntervalRat.scale (329 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (54358048956 / 1000000000000) (54358048957 / 1000000000000), orderedInterval (73839131309 / 1000000000000) (73839131310 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1223495594713217 / 4000000000000) 2 (IntervalRat.scale (329 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-42798833664 / 1000000000000) (-42798824512 / 1000000000000), orderedInterval (15867822814 / 1000000000000) (15867831966 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (817238355510703 / 4000000000000) 2 (IntervalRat.scale (329 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-43406609598 / 1000000000000) (-43406609597 / 1000000000000), orderedInterval (-34991076362 / 1000000000000) (-34991076361 / 1000000000000)))) (orderedInterval (-24713176396 / 1000000000000) (-24713173717 / 1000000000000))) = true
  rfl'

theorem compactCertificate290_chunkChecks2 :
    compactCertificate290.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate290.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate290_chunkChecks2_0
    compactCertificate290_chunkChecks2_1 compactCertificate290_chunkChecks2_2

theorem compactCertificate290_chunkChecks3_0 :
    compactCertificate290.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (329 / 2) 3 (IntervalRat.scale (329 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (58415949596 / 1000000000000) (58415953857 / 1000000000000), orderedInterval (-21568955127 / 1000000000000) (-21568950866 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (484679821859429 / 4000000000000) 3 (IntervalRat.scale (329 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (38979686372 / 1000000000000) (38979695176 / 1000000000000), orderedInterval (-61271758811 / 1000000000000) (-61271750007 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (156735496013957 / 800000000000) 3 (IntervalRat.scale (329 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (53457156204 / 1000000000000) (53457161433 / 1000000000000), orderedInterval (-19928368870 / 1000000000000) (-19928363640 / 1000000000000)))) (orderedInterval (10921215787 / 1000000000000) (10921218058 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (141428363209903 / 4000000000000) 3 (IntervalRat.scale (329 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-134170035146 / 1000000000000) (-134170035122 / 1000000000000), orderedInterval (3324684930 / 1000000000000) (3324684954 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (379896477126691 / 4000000000000) 3 (IntervalRat.scale (329 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (81722644788 / 1000000000000) (81722644801 / 1000000000000), orderedInterval (4509816481 / 1000000000000) (4509816493 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1031492835788247 / 4000000000000) 3 (IntervalRat.scale (329 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (43037713728 / 1000000000000) (43037713729 / 1000000000000), orderedInterval (24745660815 / 1000000000000) (24745660816 / 1000000000000)))) (orderedInterval (6706047226 / 1000000000000) (6706047273 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (759792954253711 / 4000000000000) 3 (IntervalRat.scale (329 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (45498422084 / 1000000000000) (45498516414 / 1000000000000), orderedInterval (-35916874365 / 1000000000000) (-35916780036 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1301918177369803 / 4000000000000) 3 (IntervalRat.scale (329 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-19676751935 / 1000000000000) (-19676751056 / 1000000000000), orderedInterval (39637939137 / 1000000000000) (39637940017 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (958987036903777 / 4000000000000) 3 (IntervalRat.scale (329 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (50505254451 / 1000000000000) (50505255653 / 1000000000000), orderedInterval (-10332654568 / 1000000000000) (-10332653366 / 1000000000000)))) (orderedInterval (10273172689 / 1000000000000) (10273173043 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate290_chunkChecks3_1 :
    compactCertificate290.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1471332729194671 / 4000000000000) 3 (IntervalRat.scale (329 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-36125825742 / 1000000000000) (-36125825741 / 1000000000000), orderedInterval (-20582265350 / 1000000000000) (-20582265349 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (849474347267959 / 4000000000000) 3 (IntervalRat.scale (329 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-25035197283 / 1000000000000) (-25035195274 / 1000000000000), orderedInterval (48751398355 / 1000000000000) (48751400364 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1507407136077731 / 4000000000000) 3 (IntervalRat.scale (329 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (24734018916 / 1000000000000) (24734018917 / 1000000000000), orderedInterval (32793079821 / 1000000000000) (32793079822 / 1000000000000)))) (orderedInterval (-104418810301 / 1000000000000) (-104418809340 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1408415282234639 / 4000000000000) 3 (IntervalRat.scale (329 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (36463940375 / 1000000000000) (36463940376 / 1000000000000), orderedInterval (21821167207 / 1000000000000) (21821167208 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1005111602426687 / 4000000000000) 3 (IntervalRat.scale (329 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (33767938254 / 1000000000000) (33767938255 / 1000000000000), orderedInterval (37259146337 / 1000000000000) (37259146338 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1139689431380073 / 4000000000000) 3 (IntervalRat.scale (329 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (8351572605 / 1000000000000) (8351572629 / 1000000000000), orderedInterval (-46540097826 / 1000000000000) (-46540097801 / 1000000000000)))) (orderedInterval (-9892019712 / 1000000000000) (-9892019621 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (950154229288537 / 4000000000000) 3 (IntervalRat.scale (329 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-21938706720 / 1000000000000) (-21938705591 / 1000000000000), orderedInterval (46937181659 / 1000000000000) (46937182788 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (839490076863277 / 4000000000000) 3 (IntervalRat.scale (329 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-9351198475 / 1000000000000) (-9351198474 / 1000000000000), orderedInterval (-54254119406 / 1000000000000) (-54254119405 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (243316944972423 / 800000000000) 3 (IntervalRat.scale (329 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-8940408561 / 1000000000000) (-8940408560 / 1000000000000), orderedInterval (-44854102234 / 1000000000000) (-44854102233 / 1000000000000)))) (orderedInterval (-823401479 / 1000000000000) (-823401386 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate290_chunkChecks3_2 :
    compactCertificate290.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (673027474862981 / 4000000000000) 3 (IntervalRat.scale (329 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-34958774096 / 1000000000000) (-34958764059 / 1000000000000), orderedInterval (50715228411 / 1000000000000) (50715238449 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (570532844016541 / 4000000000000) 3 (IntervalRat.scale (329 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-59403702244 / 1000000000000) (-59403688740 / 1000000000000), orderedInterval (30778145870 / 1000000000000) (30778159374 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (357012963096223 / 4000000000000) 3 (IntervalRat.scale (329 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (74041159917 / 1000000000000) (74041173425 / 1000000000000), orderedInterval (-41042119243 / 1000000000000) (-41042105735 / 1000000000000)))) (orderedInterval (10080807764 / 1000000000000) (10080810101 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (192002758924641 / 4000000000000) 3 (IntervalRat.scale (329 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-114707037201 / 1000000000000) (-114707037118 / 1000000000000), orderedInterval (11407909743 / 1000000000000) (11407909826 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (521324840336923 / 4000000000000) 3 (IntervalRat.scale (329 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-51632528687 / 1000000000000) (-51632433920 / 1000000000000), orderedInterval (47301252056 / 1000000000000) (47301346823 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (711824500048571 / 4000000000000) 3 (IntervalRat.scale (329 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (19379176129 / 1000000000000) (19379176566 / 1000000000000), orderedInterval (-56639394457 / 1000000000000) (-56639394019 / 1000000000000)))) (orderedInterval (-4961309885 / 1000000000000) (-4961308746 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (300987036903777 / 4000000000000) 3 (IntervalRat.scale (329 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (54358048956 / 1000000000000) (54358048957 / 1000000000000), orderedInterval (73839131309 / 1000000000000) (73839131310 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1223495594713217 / 4000000000000) 3 (IntervalRat.scale (329 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-42798833664 / 1000000000000) (-42798824512 / 1000000000000), orderedInterval (15867822814 / 1000000000000) (15867831966 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (817238355510703 / 4000000000000) 3 (IntervalRat.scale (329 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-43406609598 / 1000000000000) (-43406609597 / 1000000000000), orderedInterval (-34991076362 / 1000000000000) (-34991076361 / 1000000000000)))) (orderedInterval (-4166523302 / 1000000000000) (-4166518350 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate290_chunkChecks3 :
    compactCertificate290.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate290.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate290_chunkChecks3_0
    compactCertificate290_chunkChecks3_1 compactCertificate290_chunkChecks3_2

theorem compactCertificate290_chunkChecks4_0 :
    compactCertificate290.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (329 / 2) 4 (IntervalRat.scale (329 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (58415949596 / 1000000000000) (58415953857 / 1000000000000), orderedInterval (-21568955127 / 1000000000000) (-21568950866 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (484679821859429 / 4000000000000) 4 (IntervalRat.scale (329 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (38979686372 / 1000000000000) (38979695176 / 1000000000000), orderedInterval (-61271758811 / 1000000000000) (-61271750007 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (156735496013957 / 800000000000) 4 (IntervalRat.scale (329 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (53457156204 / 1000000000000) (53457161433 / 1000000000000), orderedInterval (-19928368870 / 1000000000000) (-19928363640 / 1000000000000)))) (orderedInterval (29438916401 / 1000000000000) (29438918779 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (141428363209903 / 4000000000000) 4 (IntervalRat.scale (329 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-134170035146 / 1000000000000) (-134170035122 / 1000000000000), orderedInterval (3324684930 / 1000000000000) (3324684954 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (379896477126691 / 4000000000000) 4 (IntervalRat.scale (329 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (81722644788 / 1000000000000) (81722644801 / 1000000000000), orderedInterval (4509816481 / 1000000000000) (4509816493 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1031492835788247 / 4000000000000) 4 (IntervalRat.scale (329 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (43037713728 / 1000000000000) (43037713729 / 1000000000000), orderedInterval (24745660815 / 1000000000000) (24745660816 / 1000000000000)))) (orderedInterval (-18223025110 / 1000000000000) (-18223025037 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (759792954253711 / 4000000000000) 4 (IntervalRat.scale (329 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (45498422084 / 1000000000000) (45498516414 / 1000000000000), orderedInterval (-35916874365 / 1000000000000) (-35916780036 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1301918177369803 / 4000000000000) 4 (IntervalRat.scale (329 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-19676751935 / 1000000000000) (-19676751056 / 1000000000000), orderedInterval (39637939137 / 1000000000000) (39637940017 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (958987036903777 / 4000000000000) 4 (IntervalRat.scale (329 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (50505254451 / 1000000000000) (50505255653 / 1000000000000), orderedInterval (-10332654568 / 1000000000000) (-10332653366 / 1000000000000)))) (orderedInterval (14683592514 / 1000000000000) (14683593161 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate290_chunkChecks4_1 :
    compactCertificate290.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1471332729194671 / 4000000000000) 4 (IntervalRat.scale (329 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-36125825742 / 1000000000000) (-36125825741 / 1000000000000), orderedInterval (-20582265350 / 1000000000000) (-20582265349 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (849474347267959 / 4000000000000) 4 (IntervalRat.scale (329 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-25035197283 / 1000000000000) (-25035195274 / 1000000000000), orderedInterval (48751398355 / 1000000000000) (48751400364 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1507407136077731 / 4000000000000) 4 (IntervalRat.scale (329 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (24734018916 / 1000000000000) (24734018917 / 1000000000000), orderedInterval (32793079821 / 1000000000000) (32793079822 / 1000000000000)))) (orderedInterval (253438567585 / 1000000000000) (253438569420 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1408415282234639 / 4000000000000) 4 (IntervalRat.scale (329 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (36463940375 / 1000000000000) (36463940376 / 1000000000000), orderedInterval (21821167207 / 1000000000000) (21821167208 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1005111602426687 / 4000000000000) 4 (IntervalRat.scale (329 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (33767938254 / 1000000000000) (33767938255 / 1000000000000), orderedInterval (37259146337 / 1000000000000) (37259146338 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1139689431380073 / 4000000000000) 4 (IntervalRat.scale (329 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (8351572605 / 1000000000000) (8351572629 / 1000000000000), orderedInterval (-46540097826 / 1000000000000) (-46540097801 / 1000000000000)))) (orderedInterval (3307237886 / 1000000000000) (3307238043 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (950154229288537 / 4000000000000) 4 (IntervalRat.scale (329 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-21938706720 / 1000000000000) (-21938705591 / 1000000000000), orderedInterval (46937181659 / 1000000000000) (46937182788 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (839490076863277 / 4000000000000) 4 (IntervalRat.scale (329 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-9351198475 / 1000000000000) (-9351198474 / 1000000000000), orderedInterval (-54254119406 / 1000000000000) (-54254119405 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (243316944972423 / 800000000000) 4 (IntervalRat.scale (329 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-8940408561 / 1000000000000) (-8940408560 / 1000000000000), orderedInterval (-44854102234 / 1000000000000) (-44854102233 / 1000000000000)))) (orderedInterval (-2348666521 / 1000000000000) (-2348666380 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate290_chunkChecks4_2 :
    compactCertificate290.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (673027474862981 / 4000000000000) 4 (IntervalRat.scale (329 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-34958774096 / 1000000000000) (-34958764059 / 1000000000000), orderedInterval (50715228411 / 1000000000000) (50715238449 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (570532844016541 / 4000000000000) 4 (IntervalRat.scale (329 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-59403702244 / 1000000000000) (-59403688740 / 1000000000000), orderedInterval (30778145870 / 1000000000000) (30778159374 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (357012963096223 / 4000000000000) 4 (IntervalRat.scale (329 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (74041159917 / 1000000000000) (74041173425 / 1000000000000), orderedInterval (-41042119243 / 1000000000000) (-41042105735 / 1000000000000)))) (orderedInterval (8104445806 / 1000000000000) (8104448095 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (192002758924641 / 4000000000000) 4 (IntervalRat.scale (329 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-114707037201 / 1000000000000) (-114707037118 / 1000000000000), orderedInterval (11407909743 / 1000000000000) (11407909826 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (521324840336923 / 4000000000000) 4 (IntervalRat.scale (329 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-51632528687 / 1000000000000) (-51632433920 / 1000000000000), orderedInterval (47301252056 / 1000000000000) (47301346823 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (711824500048571 / 4000000000000) 4 (IntervalRat.scale (329 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (19379176129 / 1000000000000) (19379176566 / 1000000000000), orderedInterval (-56639394457 / 1000000000000) (-56639394019 / 1000000000000)))) (orderedInterval (-1496838138 / 1000000000000) (-1496837212 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (300987036903777 / 4000000000000) 4 (IntervalRat.scale (329 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (54358048956 / 1000000000000) (54358048957 / 1000000000000), orderedInterval (73839131309 / 1000000000000) (73839131310 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1223495594713217 / 4000000000000) 4 (IntervalRat.scale (329 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-42798833664 / 1000000000000) (-42798824512 / 1000000000000), orderedInterval (15867822814 / 1000000000000) (15867831966 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (817238355510703 / 4000000000000) 4 (IntervalRat.scale (329 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-43406609598 / 1000000000000) (-43406609597 / 1000000000000), orderedInterval (-34991076362 / 1000000000000) (-34991076361 / 1000000000000)))) (orderedInterval (61089396676 / 1000000000000) (61089405875 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate290_chunkChecks4 :
    compactCertificate290.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate290.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate290_chunkChecks4_0
    compactCertificate290_chunkChecks4_1 compactCertificate290_chunkChecks4_2

theorem compactCertificate290_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate290.chunkCheck r b = true :=
  compactCertificate290.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate290_chunkChecks0
    · exact compactCertificate290_chunkChecks1
    · exact compactCertificate290_chunkChecks2
    · exact compactCertificate290_chunkChecks3
    · exact compactCertificate290_chunkChecks4)

theorem compactCertificate290_coefficient0 :
    compactCertificate290.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate290_coefficient1 :
    compactCertificate290.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate290_coefficient2 :
    compactCertificate290.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate290_coefficient3 :
    compactCertificate290.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate290_coefficient4 :
    compactCertificate290.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate290_coefficients : ∀ r : Fin 5,
    compactCertificate290.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate290_coefficient0
  · exact compactCertificate290_coefficient1
  · exact compactCertificate290_coefficient2
  · exact compactCertificate290_coefficient3
  · exact compactCertificate290_coefficient4

theorem compactCertificate290_lower : (1 : ℚ) ≤ compactCertificate290.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate290, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate290_proves {t : ℝ} (ht : t ∈ compactCertificate290.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate290.proves compactCertificate290_states compactCertificate290_chunks
    compactCertificate290_coefficients compactCertificate290_lower ht

end Erdos232
