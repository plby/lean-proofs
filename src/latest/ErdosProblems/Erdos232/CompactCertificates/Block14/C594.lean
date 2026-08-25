/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate594 : CompactCertificate where
  left := 465
  right := 466
  center := 931 / 2
  grid := fun i =>
    match i.val with
    | 0 => 148
    | 1 => 109
    | 2 => 177
    | 3 => 32
    | 4 => 86
    | 5 => 232
    | 6 => 171
    | 7 => 293
    | 8 => 216
    | 9 => 331
    | 10 => 191
    | 11 => 340
    | 12 => 317
    | 13 => 226
    | 14 => 257
    | 15 => 214
    | 16 => 189
    | 17 => 274
    | 18 => 152
    | 19 => 129
    | 20 => 80
    | 21 => 43
    | 22 => 117
    | 23 => 160
    | 24 => 68
    | 25 => 276
    | _ => 184
  point := fun i =>
    match i.val with
    | 0 => 931 / 2
    | 1 => 1371540772495831 / 4000000000000
    | 2 => 443528105741623 / 800000000000
    | 3 => 400212176742917 / 4000000000000
    | 4 => 1075026201230849 / 4000000000000
    | 5 => 2918905258719933 / 4000000000000
    | 6 => 2150052402462629 / 4000000000000
    | 7 => 3684151438089017 / 4000000000000
    | 8 => 2713729274642603 / 4000000000000
    | 9 => 4163558574104069 / 4000000000000
    | 10 => 2403831663545501 / 4000000000000
    | 11 => 4265641470177409 / 4000000000000
    | 12 => 3985515585898021 / 4000000000000
    | 13 => 2844251981335093 / 4000000000000
    | 14 => 3225078603692547 / 4000000000000
    | 15 => 2688734308412243 / 4000000000000
    | 16 => 2375578302613103 / 4000000000000
    | 17 => 688535184709197 / 800000000000
    | 18 => 1904524556527159 / 4000000000000
    | 19 => 1614486558599999 / 4000000000000
    | 20 => 1010270725357397 / 4000000000000
    | 21 => 543326956105899 / 4000000000000
    | 22 => 1475238377974697 / 4000000000000
    | 23 => 2014311883116169 / 4000000000000
    | 24 => 851729274642603 / 4000000000000
    | 25 => 3462232214826763 / 4000000000000
    | _ => 2312610665594117 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (35909008983 / 1000000000000) (35909008997 / 1000000000000), orderedInterval (8801486896 / 1000000000000) (8801486909 / 1000000000000))
    | 1 => (orderedInterval (-40705367308 / 1000000000000) (-40705367306 / 1000000000000), orderedInterval (-14073133692 / 1000000000000) (-14073133690 / 1000000000000))
    | 2 => (orderedInterval (25825728067 / 1000000000000) (25825747280 / 1000000000000), orderedInterval (-21962176173 / 1000000000000) (-21962156960 / 1000000000000))
    | 3 => (orderedInterval (24046854156 / 1000000000000) (24046854157 / 1000000000000), orderedInterval (75936629809 / 1000000000000) (75936629810 / 1000000000000))
    | 4 => (orderedInterval (-28888868432 / 1000000000000) (-28888860196 / 1000000000000), orderedInterval (39222539081 / 1000000000000) (39222547318 / 1000000000000))
    | 5 => (orderedInterval (29413680839 / 1000000000000) (29413686462 / 1000000000000), orderedInterval (-2711618082 / 1000000000000) (-2711612459 / 1000000000000))
    | 6 => (orderedInterval (-30447948358 / 1000000000000) (-30447948357 / 1000000000000), orderedInterval (-16012318011 / 1000000000000) (-16012318010 / 1000000000000))
    | 7 => (orderedInterval (-25572177711 / 1000000000000) (-25572177306 / 1000000000000), orderedInterval (-6090371658 / 1000000000000) (-6090371252 / 1000000000000))
    | 8 => (orderedInterval (18134156098 / 1000000000000) (18134156099 / 1000000000000), orderedInterval (24675121134 / 1000000000000) (24675121135 / 1000000000000))
    | 9 => (orderedInterval (-24039763297 / 1000000000000) (-24039667849 / 1000000000000), orderedInterval (5816942476 / 1000000000000) (5817037925 / 1000000000000))
    | 10 => (orderedInterval (-32280791359 / 1000000000000) (-32280787192 / 1000000000000), orderedInterval (4185217373 / 1000000000000) (4185221541 / 1000000000000))
    | 11 => (orderedInterval (-19815132475 / 1000000000000) (-19815129404 / 1000000000000), orderedInterval (14303869877 / 1000000000000) (14303872948 / 1000000000000))
    | 12 => (orderedInterval (-24210798631 / 1000000000000) (-24210798313 / 1000000000000), orderedInterval (-7252187382 / 1000000000000) (-7252187065 / 1000000000000))
    | 13 => (orderedInterval (28777109743 / 1000000000000) (28777141250 / 1000000000000), orderedInterval (-8216833656 / 1000000000000) (-8216802149 / 1000000000000))
    | 14 => (orderedInterval (9222827819 / 1000000000000) (9222827824 / 1000000000000), orderedInterval (-26548632632 / 1000000000000) (-26548632628 / 1000000000000))
    | 15 => (orderedInterval (19061541464 / 1000000000000) (19061541465 / 1000000000000), orderedInterval (24146736377 / 1000000000000) (24146736378 / 1000000000000))
    | 16 => (orderedInterval (-26023616819 / 1000000000000) (-26023616818 / 1000000000000), orderedInterval (-19845450297 / 1000000000000) (-19845450296 / 1000000000000))
    | 17 => (orderedInterval (16628672806 / 1000000000000) (16628672807 / 1000000000000), orderedInterval (21511664818 / 1000000000000) (21511664819 / 1000000000000))
    | 18 => (orderedInterval (-20821628202 / 1000000000000) (-20821626251 / 1000000000000), orderedInterval (30080610708 / 1000000000000) (30080612660 / 1000000000000))
    | 19 => (orderedInterval (30064485000 / 1000000000000) (30064521228 / 1000000000000), orderedInterval (-25987099710 / 1000000000000) (-25987063482 / 1000000000000))
    | 20 => (orderedInterval (45111336580 / 1000000000000) (45111355398 / 1000000000000), orderedInterval (-22124608385 / 1000000000000) (-22124589567 / 1000000000000))
    | 21 => (orderedInterval (-68396699322 / 1000000000000) (-68396699299 / 1000000000000), orderedInterval (-2695474817 / 1000000000000) (-2695474794 / 1000000000000))
    | 22 => (orderedInterval (-37273915569 / 1000000000000) (-37273882109 / 1000000000000), orderedInterval (18402708602 / 1000000000000) (18402742062 / 1000000000000))
    | 23 => (orderedInterval (35219902104 / 1000000000000) (35219904806 / 1000000000000), orderedInterval (-4908455466 / 1000000000000) (-4908452764 / 1000000000000))
    | 24 => (orderedInterval (4850693564 / 1000000000000) (4850693565 / 1000000000000), orderedInterval (54451938017 / 1000000000000) (54451938018 / 1000000000000))
    | 25 => (orderedInterval (-18211851994 / 1000000000000) (-18211851099 / 1000000000000), orderedInterval (20106056211 / 1000000000000) (20106057106 / 1000000000000))
    | _ => (orderedInterval (25676800946 / 1000000000000) (25676800947 / 1000000000000), orderedInterval (20997529217 / 1000000000000) (20997529218 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (15369262187 / 1000000000000) (15369263353 / 1000000000000)
      | 1 => orderedInterval (-3406682784 / 1000000000000) (-3406682027 / 1000000000000)
      | 2 => orderedInterval (1227015023 / 1000000000000) (1227015062 / 1000000000000)
      | 3 => orderedInterval (-937020204 / 1000000000000) (-937002314 / 1000000000000)
      | 4 => orderedInterval (3111652748 / 1000000000000) (3111655788 / 1000000000000)
      | 5 => orderedInterval (2135121189 / 1000000000000) (2135121234 / 1000000000000)
      | 6 => orderedInterval (3096181818 / 1000000000000) (3096184910 / 1000000000000)
      | 7 => orderedInterval (-590633259 / 1000000000000) (-590632237 / 1000000000000)
      | _ => orderedInterval (-3305930437 / 1000000000000) (-3305930235 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (1857089605 / 1000000000000) (1857090990 / 1000000000000)
      | 1 => orderedInterval (951922177 / 1000000000000) (951923041 / 1000000000000)
      | 2 => orderedInterval (1240817802 / 1000000000000) (1240817873 / 1000000000000)
      | 3 => orderedInterval (2747338891 / 1000000000000) (2747378596 / 1000000000000)
      | 4 => orderedInterval (-673958081 / 1000000000000) (-673953427 / 1000000000000)
      | 5 => orderedInterval (2869930539 / 1000000000000) (2869930604 / 1000000000000)
      | 6 => orderedInterval (-4034960563 / 1000000000000) (-4034958025 / 1000000000000)
      | 7 => orderedInterval (90692918 / 1000000000000) (90693794 / 1000000000000)
      | _ => orderedInterval (-7786208935 / 1000000000000) (-7786208618 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-16180951181 / 1000000000000) (-16180949532 / 1000000000000)
      | 1 => orderedInterval (5500101624 / 1000000000000) (5500102796 / 1000000000000)
      | 2 => orderedInterval (-4021419835 / 1000000000000) (-4021419705 / 1000000000000)
      | 3 => orderedInterval (-2594255379 / 1000000000000) (-2594166870 / 1000000000000)
      | 4 => orderedInterval (-8210604145 / 1000000000000) (-8210597007 / 1000000000000)
      | 5 => orderedInterval (-4344662831 / 1000000000000) (-4344662734 / 1000000000000)
      | 6 => orderedInterval (-2627373104 / 1000000000000) (-2627370947 / 1000000000000)
      | 7 => orderedInterval (2520320215 / 1000000000000) (2520320985 / 1000000000000)
      | _ => orderedInterval (2316626089 / 1000000000000) (2316626609 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-1224175413 / 1000000000000) (-1224173450 / 1000000000000)
      | 1 => orderedInterval (-1021836669 / 1000000000000) (-1021834938 / 1000000000000)
      | 2 => orderedInterval (-3292563498 / 1000000000000) (-3292563253 / 1000000000000)
      | 3 => orderedInterval (-13553011122 / 1000000000000) (-13552813605 / 1000000000000)
      | 4 => orderedInterval (805032411 / 1000000000000) (805043354 / 1000000000000)
      | 5 => orderedInterval (-6669895822 / 1000000000000) (-6669895674 / 1000000000000)
      | 6 => orderedInterval (4308625130 / 1000000000000) (4308627003 / 1000000000000)
      | 7 => orderedInterval (-275263993 / 1000000000000) (-275263300 / 1000000000000)
      | _ => orderedInterval (18033360411 / 1000000000000) (18033361293 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (17175877999 / 1000000000000) (17175880339 / 1000000000000)
      | 1 => orderedInterval (-12740830419 / 1000000000000) (-12740827762 / 1000000000000)
      | 2 => orderedInterval (14079910193 / 1000000000000) (14079910657 / 1000000000000)
      | 3 => orderedInterval (22617962614 / 1000000000000) (22618404322 / 1000000000000)
      | 4 => orderedInterval (23566567307 / 1000000000000) (23566584133 / 1000000000000)
      | 5 => orderedInterval (9906801132 / 1000000000000) (9906801367 / 1000000000000)
      | 6 => orderedInterval (2790870987 / 1000000000000) (2790872647 / 1000000000000)
      | 7 => orderedInterval (-3353241850 / 1000000000000) (-3353241210 / 1000000000000)
      | _ => orderedInterval (6181302743 / 1000000000000) (6181304279 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (16698966281 / 1000000000000) (16698993534 / 1000000000000)
    | 1 => orderedInterval (-2737335647 / 1000000000000) (-2737285172 / 1000000000000)
    | 2 => orderedInterval (-27642218547 / 1000000000000) (-27642116405 / 1000000000000)
    | 3 => orderedInterval (-2889728565 / 1000000000000) (-2889512570 / 1000000000000)
    | _ => orderedInterval (80225220706 / 1000000000000) (80225688772 / 1000000000000)

theorem compactCertificate594_stateChecks0 :
    compactCertificate594.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 148 12 (931 / 2)) (orderedInterval (35909008983 / 1000000000000) (35909008997 / 1000000000000), orderedInterval (8801486896 / 1000000000000) (8801486909 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 109 12 (1371540772495831 / 4000000000000)) (orderedInterval (-40705367308 / 1000000000000) (-40705367306 / 1000000000000), orderedInterval (-14073133692 / 1000000000000) (-14073133690 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 177 12 (443528105741623 / 800000000000)) (orderedInterval (25825728067 / 1000000000000) (25825747280 / 1000000000000), orderedInterval (-21962176173 / 1000000000000) (-21962156960 / 1000000000000))) = true
  rfl'

theorem compactCertificate594_stateChecks1 :
    compactCertificate594.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (400212176742917 / 4000000000000)) (orderedInterval (24046854156 / 1000000000000) (24046854157 / 1000000000000), orderedInterval (75936629809 / 1000000000000) (75936629810 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 86 12 (1075026201230849 / 4000000000000)) (orderedInterval (-28888868432 / 1000000000000) (-28888860196 / 1000000000000), orderedInterval (39222539081 / 1000000000000) (39222547318 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 232 12 (2918905258719933 / 4000000000000)) (orderedInterval (29413680839 / 1000000000000) (29413686462 / 1000000000000), orderedInterval (-2711618082 / 1000000000000) (-2711612459 / 1000000000000))) = true
  rfl'

theorem compactCertificate594_stateChecks2 :
    compactCertificate594.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 171 12 (2150052402462629 / 4000000000000)) (orderedInterval (-30447948358 / 1000000000000) (-30447948357 / 1000000000000), orderedInterval (-16012318011 / 1000000000000) (-16012318010 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 293 12 (3684151438089017 / 4000000000000)) (orderedInterval (-25572177711 / 1000000000000) (-25572177306 / 1000000000000), orderedInterval (-6090371658 / 1000000000000) (-6090371252 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 216 12 (2713729274642603 / 4000000000000)) (orderedInterval (18134156098 / 1000000000000) (18134156099 / 1000000000000), orderedInterval (24675121134 / 1000000000000) (24675121135 / 1000000000000))) = true
  rfl'

theorem compactCertificate594_stateChecks3 :
    compactCertificate594.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 331 12 (4163558574104069 / 4000000000000)) (orderedInterval (-24039763297 / 1000000000000) (-24039667849 / 1000000000000), orderedInterval (5816942476 / 1000000000000) (5817037925 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 191 12 (2403831663545501 / 4000000000000)) (orderedInterval (-32280791359 / 1000000000000) (-32280787192 / 1000000000000), orderedInterval (4185217373 / 1000000000000) (4185221541 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 340 12 (4265641470177409 / 4000000000000)) (orderedInterval (-19815132475 / 1000000000000) (-19815129404 / 1000000000000), orderedInterval (14303869877 / 1000000000000) (14303872948 / 1000000000000))) = true
  rfl'

theorem compactCertificate594_stateChecks4 :
    compactCertificate594.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 317 12 (3985515585898021 / 4000000000000)) (orderedInterval (-24210798631 / 1000000000000) (-24210798313 / 1000000000000), orderedInterval (-7252187382 / 1000000000000) (-7252187065 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 226 12 (2844251981335093 / 4000000000000)) (orderedInterval (28777109743 / 1000000000000) (28777141250 / 1000000000000), orderedInterval (-8216833656 / 1000000000000) (-8216802149 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 257 12 (3225078603692547 / 4000000000000)) (orderedInterval (9222827819 / 1000000000000) (9222827824 / 1000000000000), orderedInterval (-26548632632 / 1000000000000) (-26548632628 / 1000000000000))) = true
  rfl'

theorem compactCertificate594_stateChecks5 :
    compactCertificate594.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 214 12 (2688734308412243 / 4000000000000)) (orderedInterval (19061541464 / 1000000000000) (19061541465 / 1000000000000), orderedInterval (24146736377 / 1000000000000) (24146736378 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 189 12 (2375578302613103 / 4000000000000)) (orderedInterval (-26023616819 / 1000000000000) (-26023616818 / 1000000000000), orderedInterval (-19845450297 / 1000000000000) (-19845450296 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 274 12 (688535184709197 / 800000000000)) (orderedInterval (16628672806 / 1000000000000) (16628672807 / 1000000000000), orderedInterval (21511664818 / 1000000000000) (21511664819 / 1000000000000))) = true
  rfl'

theorem compactCertificate594_stateChecks6 :
    compactCertificate594.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 152 12 (1904524556527159 / 4000000000000)) (orderedInterval (-20821628202 / 1000000000000) (-20821626251 / 1000000000000), orderedInterval (30080610708 / 1000000000000) (30080612660 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 129 12 (1614486558599999 / 4000000000000)) (orderedInterval (30064485000 / 1000000000000) (30064521228 / 1000000000000), orderedInterval (-25987099710 / 1000000000000) (-25987063482 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 80 12 (1010270725357397 / 4000000000000)) (orderedInterval (45111336580 / 1000000000000) (45111355398 / 1000000000000), orderedInterval (-22124608385 / 1000000000000) (-22124589567 / 1000000000000))) = true
  rfl'

theorem compactCertificate594_stateChecks7 :
    compactCertificate594.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (543326956105899 / 4000000000000)) (orderedInterval (-68396699322 / 1000000000000) (-68396699299 / 1000000000000), orderedInterval (-2695474817 / 1000000000000) (-2695474794 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 117 12 (1475238377974697 / 4000000000000)) (orderedInterval (-37273915569 / 1000000000000) (-37273882109 / 1000000000000), orderedInterval (18402708602 / 1000000000000) (18402742062 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 160 12 (2014311883116169 / 4000000000000)) (orderedInterval (35219902104 / 1000000000000) (35219904806 / 1000000000000), orderedInterval (-4908455466 / 1000000000000) (-4908452764 / 1000000000000))) = true
  rfl'

theorem compactCertificate594_stateChecks8 :
    compactCertificate594.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (851729274642603 / 4000000000000)) (orderedInterval (4850693564 / 1000000000000) (4850693565 / 1000000000000), orderedInterval (54451938017 / 1000000000000) (54451938018 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 276 12 (3462232214826763 / 4000000000000)) (orderedInterval (-18211851994 / 1000000000000) (-18211851099 / 1000000000000), orderedInterval (20106056211 / 1000000000000) (20106057106 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 184 12 (2312610665594117 / 4000000000000)) (orderedInterval (25676800946 / 1000000000000) (25676800947 / 1000000000000), orderedInterval (20997529217 / 1000000000000) (20997529218 / 1000000000000))) = true
  rfl'

theorem compactCertificate594_states : ∀ j,
    BesselStateValid (compactCertificate594.point j) (compactCertificate594.state j) :=
  compactCertificate594.statesValid_of_checks3 compactCertificate594_stateChecks0
    compactCertificate594_stateChecks1 compactCertificate594_stateChecks2
    compactCertificate594_stateChecks3 compactCertificate594_stateChecks4
    compactCertificate594_stateChecks5 compactCertificate594_stateChecks6
    compactCertificate594_stateChecks7 compactCertificate594_stateChecks8

theorem compactCertificate594_chunkChecks0_0 :
    compactCertificate594.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (931 / 2) 0 (IntervalRat.scale (931 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (35909008983 / 1000000000000) (35909008997 / 1000000000000), orderedInterval (8801486896 / 1000000000000) (8801486909 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1371540772495831 / 4000000000000) 0 (IntervalRat.scale (931 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-40705367308 / 1000000000000) (-40705367306 / 1000000000000), orderedInterval (-14073133692 / 1000000000000) (-14073133690 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (443528105741623 / 800000000000) 0 (IntervalRat.scale (931 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (25825728067 / 1000000000000) (25825747280 / 1000000000000), orderedInterval (-21962176173 / 1000000000000) (-21962156960 / 1000000000000)))) (orderedInterval (15369262187 / 1000000000000) (15369263353 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (400212176742917 / 4000000000000) 0 (IntervalRat.scale (931 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (24046854156 / 1000000000000) (24046854157 / 1000000000000), orderedInterval (75936629809 / 1000000000000) (75936629810 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (1075026201230849 / 4000000000000) 0 (IntervalRat.scale (931 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-28888868432 / 1000000000000) (-28888860196 / 1000000000000), orderedInterval (39222539081 / 1000000000000) (39222547318 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2918905258719933 / 4000000000000) 0 (IntervalRat.scale (931 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29413680839 / 1000000000000) (29413686462 / 1000000000000), orderedInterval (-2711618082 / 1000000000000) (-2711612459 / 1000000000000)))) (orderedInterval (-3406682784 / 1000000000000) (-3406682027 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (2150052402462629 / 4000000000000) 0 (IntervalRat.scale (931 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-30447948358 / 1000000000000) (-30447948357 / 1000000000000), orderedInterval (-16012318011 / 1000000000000) (-16012318010 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3684151438089017 / 4000000000000) 0 (IntervalRat.scale (931 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-25572177711 / 1000000000000) (-25572177306 / 1000000000000), orderedInterval (-6090371658 / 1000000000000) (-6090371252 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2713729274642603 / 4000000000000) 0 (IntervalRat.scale (931 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (18134156098 / 1000000000000) (18134156099 / 1000000000000), orderedInterval (24675121134 / 1000000000000) (24675121135 / 1000000000000)))) (orderedInterval (1227015023 / 1000000000000) (1227015062 / 1000000000000))) = true
  rfl'

theorem compactCertificate594_chunkChecks0_1 :
    compactCertificate594.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (4163558574104069 / 4000000000000) 0 (IntervalRat.scale (931 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-24039763297 / 1000000000000) (-24039667849 / 1000000000000), orderedInterval (5816942476 / 1000000000000) (5817037925 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2403831663545501 / 4000000000000) 0 (IntervalRat.scale (931 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-32280791359 / 1000000000000) (-32280787192 / 1000000000000), orderedInterval (4185217373 / 1000000000000) (4185221541 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (4265641470177409 / 4000000000000) 0 (IntervalRat.scale (931 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-19815132475 / 1000000000000) (-19815129404 / 1000000000000), orderedInterval (14303869877 / 1000000000000) (14303872948 / 1000000000000)))) (orderedInterval (-937020204 / 1000000000000) (-937002314 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3985515585898021 / 4000000000000) 0 (IntervalRat.scale (931 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-24210798631 / 1000000000000) (-24210798313 / 1000000000000), orderedInterval (-7252187382 / 1000000000000) (-7252187065 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2844251981335093 / 4000000000000) 0 (IntervalRat.scale (931 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (28777109743 / 1000000000000) (28777141250 / 1000000000000), orderedInterval (-8216833656 / 1000000000000) (-8216802149 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (3225078603692547 / 4000000000000) 0 (IntervalRat.scale (931 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (9222827819 / 1000000000000) (9222827824 / 1000000000000), orderedInterval (-26548632632 / 1000000000000) (-26548632628 / 1000000000000)))) (orderedInterval (3111652748 / 1000000000000) (3111655788 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2688734308412243 / 4000000000000) 0 (IntervalRat.scale (931 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (19061541464 / 1000000000000) (19061541465 / 1000000000000), orderedInterval (24146736377 / 1000000000000) (24146736378 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2375578302613103 / 4000000000000) 0 (IntervalRat.scale (931 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-26023616819 / 1000000000000) (-26023616818 / 1000000000000), orderedInterval (-19845450297 / 1000000000000) (-19845450296 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (688535184709197 / 800000000000) 0 (IntervalRat.scale (931 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16628672806 / 1000000000000) (16628672807 / 1000000000000), orderedInterval (21511664818 / 1000000000000) (21511664819 / 1000000000000)))) (orderedInterval (2135121189 / 1000000000000) (2135121234 / 1000000000000))) = true
  rfl'

theorem compactCertificate594_chunkChecks0_2 :
    compactCertificate594.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1904524556527159 / 4000000000000) 0 (IntervalRat.scale (931 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-20821628202 / 1000000000000) (-20821626251 / 1000000000000), orderedInterval (30080610708 / 1000000000000) (30080612660 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1614486558599999 / 4000000000000) 0 (IntervalRat.scale (931 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (30064485000 / 1000000000000) (30064521228 / 1000000000000), orderedInterval (-25987099710 / 1000000000000) (-25987063482 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (1010270725357397 / 4000000000000) 0 (IntervalRat.scale (931 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (45111336580 / 1000000000000) (45111355398 / 1000000000000), orderedInterval (-22124608385 / 1000000000000) (-22124589567 / 1000000000000)))) (orderedInterval (3096181818 / 1000000000000) (3096184910 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (543326956105899 / 4000000000000) 0 (IntervalRat.scale (931 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-68396699322 / 1000000000000) (-68396699299 / 1000000000000), orderedInterval (-2695474817 / 1000000000000) (-2695474794 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1475238377974697 / 4000000000000) 0 (IntervalRat.scale (931 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-37273915569 / 1000000000000) (-37273882109 / 1000000000000), orderedInterval (18402708602 / 1000000000000) (18402742062 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (2014311883116169 / 4000000000000) 0 (IntervalRat.scale (931 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (35219902104 / 1000000000000) (35219904806 / 1000000000000), orderedInterval (-4908455466 / 1000000000000) (-4908452764 / 1000000000000)))) (orderedInterval (-590633259 / 1000000000000) (-590632237 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (851729274642603 / 4000000000000) 0 (IntervalRat.scale (931 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (4850693564 / 1000000000000) (4850693565 / 1000000000000), orderedInterval (54451938017 / 1000000000000) (54451938018 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3462232214826763 / 4000000000000) 0 (IntervalRat.scale (931 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-18211851994 / 1000000000000) (-18211851099 / 1000000000000), orderedInterval (20106056211 / 1000000000000) (20106057106 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2312610665594117 / 4000000000000) 0 (IntervalRat.scale (931 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (25676800946 / 1000000000000) (25676800947 / 1000000000000), orderedInterval (20997529217 / 1000000000000) (20997529218 / 1000000000000)))) (orderedInterval (-3305930437 / 1000000000000) (-3305930235 / 1000000000000))) = true
  rfl'

theorem compactCertificate594_chunkChecks0 :
    compactCertificate594.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate594.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate594_chunkChecks0_0
    compactCertificate594_chunkChecks0_1 compactCertificate594_chunkChecks0_2

theorem compactCertificate594_chunkChecks1_0 :
    compactCertificate594.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (931 / 2) 1 (IntervalRat.scale (931 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (35909008983 / 1000000000000) (35909008997 / 1000000000000), orderedInterval (8801486896 / 1000000000000) (8801486909 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1371540772495831 / 4000000000000) 1 (IntervalRat.scale (931 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-40705367308 / 1000000000000) (-40705367306 / 1000000000000), orderedInterval (-14073133692 / 1000000000000) (-14073133690 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (443528105741623 / 800000000000) 1 (IntervalRat.scale (931 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (25825728067 / 1000000000000) (25825747280 / 1000000000000), orderedInterval (-21962176173 / 1000000000000) (-21962156960 / 1000000000000)))) (orderedInterval (1857089605 / 1000000000000) (1857090990 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (400212176742917 / 4000000000000) 1 (IntervalRat.scale (931 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (24046854156 / 1000000000000) (24046854157 / 1000000000000), orderedInterval (75936629809 / 1000000000000) (75936629810 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (1075026201230849 / 4000000000000) 1 (IntervalRat.scale (931 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-28888868432 / 1000000000000) (-28888860196 / 1000000000000), orderedInterval (39222539081 / 1000000000000) (39222547318 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2918905258719933 / 4000000000000) 1 (IntervalRat.scale (931 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29413680839 / 1000000000000) (29413686462 / 1000000000000), orderedInterval (-2711618082 / 1000000000000) (-2711612459 / 1000000000000)))) (orderedInterval (951922177 / 1000000000000) (951923041 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (2150052402462629 / 4000000000000) 1 (IntervalRat.scale (931 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-30447948358 / 1000000000000) (-30447948357 / 1000000000000), orderedInterval (-16012318011 / 1000000000000) (-16012318010 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3684151438089017 / 4000000000000) 1 (IntervalRat.scale (931 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-25572177711 / 1000000000000) (-25572177306 / 1000000000000), orderedInterval (-6090371658 / 1000000000000) (-6090371252 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2713729274642603 / 4000000000000) 1 (IntervalRat.scale (931 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (18134156098 / 1000000000000) (18134156099 / 1000000000000), orderedInterval (24675121134 / 1000000000000) (24675121135 / 1000000000000)))) (orderedInterval (1240817802 / 1000000000000) (1240817873 / 1000000000000))) = true
  rfl'

theorem compactCertificate594_chunkChecks1_1 :
    compactCertificate594.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (4163558574104069 / 4000000000000) 1 (IntervalRat.scale (931 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-24039763297 / 1000000000000) (-24039667849 / 1000000000000), orderedInterval (5816942476 / 1000000000000) (5817037925 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2403831663545501 / 4000000000000) 1 (IntervalRat.scale (931 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-32280791359 / 1000000000000) (-32280787192 / 1000000000000), orderedInterval (4185217373 / 1000000000000) (4185221541 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (4265641470177409 / 4000000000000) 1 (IntervalRat.scale (931 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-19815132475 / 1000000000000) (-19815129404 / 1000000000000), orderedInterval (14303869877 / 1000000000000) (14303872948 / 1000000000000)))) (orderedInterval (2747338891 / 1000000000000) (2747378596 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3985515585898021 / 4000000000000) 1 (IntervalRat.scale (931 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-24210798631 / 1000000000000) (-24210798313 / 1000000000000), orderedInterval (-7252187382 / 1000000000000) (-7252187065 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2844251981335093 / 4000000000000) 1 (IntervalRat.scale (931 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (28777109743 / 1000000000000) (28777141250 / 1000000000000), orderedInterval (-8216833656 / 1000000000000) (-8216802149 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (3225078603692547 / 4000000000000) 1 (IntervalRat.scale (931 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (9222827819 / 1000000000000) (9222827824 / 1000000000000), orderedInterval (-26548632632 / 1000000000000) (-26548632628 / 1000000000000)))) (orderedInterval (-673958081 / 1000000000000) (-673953427 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2688734308412243 / 4000000000000) 1 (IntervalRat.scale (931 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (19061541464 / 1000000000000) (19061541465 / 1000000000000), orderedInterval (24146736377 / 1000000000000) (24146736378 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2375578302613103 / 4000000000000) 1 (IntervalRat.scale (931 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-26023616819 / 1000000000000) (-26023616818 / 1000000000000), orderedInterval (-19845450297 / 1000000000000) (-19845450296 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (688535184709197 / 800000000000) 1 (IntervalRat.scale (931 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16628672806 / 1000000000000) (16628672807 / 1000000000000), orderedInterval (21511664818 / 1000000000000) (21511664819 / 1000000000000)))) (orderedInterval (2869930539 / 1000000000000) (2869930604 / 1000000000000))) = true
  rfl'

theorem compactCertificate594_chunkChecks1_2 :
    compactCertificate594.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1904524556527159 / 4000000000000) 1 (IntervalRat.scale (931 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-20821628202 / 1000000000000) (-20821626251 / 1000000000000), orderedInterval (30080610708 / 1000000000000) (30080612660 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1614486558599999 / 4000000000000) 1 (IntervalRat.scale (931 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (30064485000 / 1000000000000) (30064521228 / 1000000000000), orderedInterval (-25987099710 / 1000000000000) (-25987063482 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (1010270725357397 / 4000000000000) 1 (IntervalRat.scale (931 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (45111336580 / 1000000000000) (45111355398 / 1000000000000), orderedInterval (-22124608385 / 1000000000000) (-22124589567 / 1000000000000)))) (orderedInterval (-4034960563 / 1000000000000) (-4034958025 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (543326956105899 / 4000000000000) 1 (IntervalRat.scale (931 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-68396699322 / 1000000000000) (-68396699299 / 1000000000000), orderedInterval (-2695474817 / 1000000000000) (-2695474794 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1475238377974697 / 4000000000000) 1 (IntervalRat.scale (931 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-37273915569 / 1000000000000) (-37273882109 / 1000000000000), orderedInterval (18402708602 / 1000000000000) (18402742062 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (2014311883116169 / 4000000000000) 1 (IntervalRat.scale (931 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (35219902104 / 1000000000000) (35219904806 / 1000000000000), orderedInterval (-4908455466 / 1000000000000) (-4908452764 / 1000000000000)))) (orderedInterval (90692918 / 1000000000000) (90693794 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (851729274642603 / 4000000000000) 1 (IntervalRat.scale (931 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (4850693564 / 1000000000000) (4850693565 / 1000000000000), orderedInterval (54451938017 / 1000000000000) (54451938018 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3462232214826763 / 4000000000000) 1 (IntervalRat.scale (931 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-18211851994 / 1000000000000) (-18211851099 / 1000000000000), orderedInterval (20106056211 / 1000000000000) (20106057106 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2312610665594117 / 4000000000000) 1 (IntervalRat.scale (931 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (25676800946 / 1000000000000) (25676800947 / 1000000000000), orderedInterval (20997529217 / 1000000000000) (20997529218 / 1000000000000)))) (orderedInterval (-7786208935 / 1000000000000) (-7786208618 / 1000000000000))) = true
  rfl'

theorem compactCertificate594_chunkChecks1 :
    compactCertificate594.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate594.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate594_chunkChecks1_0
    compactCertificate594_chunkChecks1_1 compactCertificate594_chunkChecks1_2

theorem compactCertificate594_chunkChecks2_0 :
    compactCertificate594.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (931 / 2) 2 (IntervalRat.scale (931 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (35909008983 / 1000000000000) (35909008997 / 1000000000000), orderedInterval (8801486896 / 1000000000000) (8801486909 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1371540772495831 / 4000000000000) 2 (IntervalRat.scale (931 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-40705367308 / 1000000000000) (-40705367306 / 1000000000000), orderedInterval (-14073133692 / 1000000000000) (-14073133690 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (443528105741623 / 800000000000) 2 (IntervalRat.scale (931 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (25825728067 / 1000000000000) (25825747280 / 1000000000000), orderedInterval (-21962176173 / 1000000000000) (-21962156960 / 1000000000000)))) (orderedInterval (-16180951181 / 1000000000000) (-16180949532 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (400212176742917 / 4000000000000) 2 (IntervalRat.scale (931 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (24046854156 / 1000000000000) (24046854157 / 1000000000000), orderedInterval (75936629809 / 1000000000000) (75936629810 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (1075026201230849 / 4000000000000) 2 (IntervalRat.scale (931 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-28888868432 / 1000000000000) (-28888860196 / 1000000000000), orderedInterval (39222539081 / 1000000000000) (39222547318 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2918905258719933 / 4000000000000) 2 (IntervalRat.scale (931 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29413680839 / 1000000000000) (29413686462 / 1000000000000), orderedInterval (-2711618082 / 1000000000000) (-2711612459 / 1000000000000)))) (orderedInterval (5500101624 / 1000000000000) (5500102796 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (2150052402462629 / 4000000000000) 2 (IntervalRat.scale (931 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-30447948358 / 1000000000000) (-30447948357 / 1000000000000), orderedInterval (-16012318011 / 1000000000000) (-16012318010 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3684151438089017 / 4000000000000) 2 (IntervalRat.scale (931 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-25572177711 / 1000000000000) (-25572177306 / 1000000000000), orderedInterval (-6090371658 / 1000000000000) (-6090371252 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2713729274642603 / 4000000000000) 2 (IntervalRat.scale (931 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (18134156098 / 1000000000000) (18134156099 / 1000000000000), orderedInterval (24675121134 / 1000000000000) (24675121135 / 1000000000000)))) (orderedInterval (-4021419835 / 1000000000000) (-4021419705 / 1000000000000))) = true
  rfl'

theorem compactCertificate594_chunkChecks2_1 :
    compactCertificate594.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (4163558574104069 / 4000000000000) 2 (IntervalRat.scale (931 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-24039763297 / 1000000000000) (-24039667849 / 1000000000000), orderedInterval (5816942476 / 1000000000000) (5817037925 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2403831663545501 / 4000000000000) 2 (IntervalRat.scale (931 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-32280791359 / 1000000000000) (-32280787192 / 1000000000000), orderedInterval (4185217373 / 1000000000000) (4185221541 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (4265641470177409 / 4000000000000) 2 (IntervalRat.scale (931 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-19815132475 / 1000000000000) (-19815129404 / 1000000000000), orderedInterval (14303869877 / 1000000000000) (14303872948 / 1000000000000)))) (orderedInterval (-2594255379 / 1000000000000) (-2594166870 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3985515585898021 / 4000000000000) 2 (IntervalRat.scale (931 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-24210798631 / 1000000000000) (-24210798313 / 1000000000000), orderedInterval (-7252187382 / 1000000000000) (-7252187065 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2844251981335093 / 4000000000000) 2 (IntervalRat.scale (931 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (28777109743 / 1000000000000) (28777141250 / 1000000000000), orderedInterval (-8216833656 / 1000000000000) (-8216802149 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (3225078603692547 / 4000000000000) 2 (IntervalRat.scale (931 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (9222827819 / 1000000000000) (9222827824 / 1000000000000), orderedInterval (-26548632632 / 1000000000000) (-26548632628 / 1000000000000)))) (orderedInterval (-8210604145 / 1000000000000) (-8210597007 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2688734308412243 / 4000000000000) 2 (IntervalRat.scale (931 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (19061541464 / 1000000000000) (19061541465 / 1000000000000), orderedInterval (24146736377 / 1000000000000) (24146736378 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2375578302613103 / 4000000000000) 2 (IntervalRat.scale (931 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-26023616819 / 1000000000000) (-26023616818 / 1000000000000), orderedInterval (-19845450297 / 1000000000000) (-19845450296 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (688535184709197 / 800000000000) 2 (IntervalRat.scale (931 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16628672806 / 1000000000000) (16628672807 / 1000000000000), orderedInterval (21511664818 / 1000000000000) (21511664819 / 1000000000000)))) (orderedInterval (-4344662831 / 1000000000000) (-4344662734 / 1000000000000))) = true
  rfl'

theorem compactCertificate594_chunkChecks2_2 :
    compactCertificate594.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1904524556527159 / 4000000000000) 2 (IntervalRat.scale (931 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-20821628202 / 1000000000000) (-20821626251 / 1000000000000), orderedInterval (30080610708 / 1000000000000) (30080612660 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1614486558599999 / 4000000000000) 2 (IntervalRat.scale (931 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (30064485000 / 1000000000000) (30064521228 / 1000000000000), orderedInterval (-25987099710 / 1000000000000) (-25987063482 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (1010270725357397 / 4000000000000) 2 (IntervalRat.scale (931 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (45111336580 / 1000000000000) (45111355398 / 1000000000000), orderedInterval (-22124608385 / 1000000000000) (-22124589567 / 1000000000000)))) (orderedInterval (-2627373104 / 1000000000000) (-2627370947 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (543326956105899 / 4000000000000) 2 (IntervalRat.scale (931 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-68396699322 / 1000000000000) (-68396699299 / 1000000000000), orderedInterval (-2695474817 / 1000000000000) (-2695474794 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1475238377974697 / 4000000000000) 2 (IntervalRat.scale (931 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-37273915569 / 1000000000000) (-37273882109 / 1000000000000), orderedInterval (18402708602 / 1000000000000) (18402742062 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (2014311883116169 / 4000000000000) 2 (IntervalRat.scale (931 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (35219902104 / 1000000000000) (35219904806 / 1000000000000), orderedInterval (-4908455466 / 1000000000000) (-4908452764 / 1000000000000)))) (orderedInterval (2520320215 / 1000000000000) (2520320985 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (851729274642603 / 4000000000000) 2 (IntervalRat.scale (931 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (4850693564 / 1000000000000) (4850693565 / 1000000000000), orderedInterval (54451938017 / 1000000000000) (54451938018 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3462232214826763 / 4000000000000) 2 (IntervalRat.scale (931 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-18211851994 / 1000000000000) (-18211851099 / 1000000000000), orderedInterval (20106056211 / 1000000000000) (20106057106 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2312610665594117 / 4000000000000) 2 (IntervalRat.scale (931 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (25676800946 / 1000000000000) (25676800947 / 1000000000000), orderedInterval (20997529217 / 1000000000000) (20997529218 / 1000000000000)))) (orderedInterval (2316626089 / 1000000000000) (2316626609 / 1000000000000))) = true
  rfl'

theorem compactCertificate594_chunkChecks2 :
    compactCertificate594.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate594.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate594_chunkChecks2_0
    compactCertificate594_chunkChecks2_1 compactCertificate594_chunkChecks2_2

theorem compactCertificate594_chunkChecks3_0 :
    compactCertificate594.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (931 / 2) 3 (IntervalRat.scale (931 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (35909008983 / 1000000000000) (35909008997 / 1000000000000), orderedInterval (8801486896 / 1000000000000) (8801486909 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1371540772495831 / 4000000000000) 3 (IntervalRat.scale (931 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-40705367308 / 1000000000000) (-40705367306 / 1000000000000), orderedInterval (-14073133692 / 1000000000000) (-14073133690 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (443528105741623 / 800000000000) 3 (IntervalRat.scale (931 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (25825728067 / 1000000000000) (25825747280 / 1000000000000), orderedInterval (-21962176173 / 1000000000000) (-21962156960 / 1000000000000)))) (orderedInterval (-1224175413 / 1000000000000) (-1224173450 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (400212176742917 / 4000000000000) 3 (IntervalRat.scale (931 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (24046854156 / 1000000000000) (24046854157 / 1000000000000), orderedInterval (75936629809 / 1000000000000) (75936629810 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (1075026201230849 / 4000000000000) 3 (IntervalRat.scale (931 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-28888868432 / 1000000000000) (-28888860196 / 1000000000000), orderedInterval (39222539081 / 1000000000000) (39222547318 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2918905258719933 / 4000000000000) 3 (IntervalRat.scale (931 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29413680839 / 1000000000000) (29413686462 / 1000000000000), orderedInterval (-2711618082 / 1000000000000) (-2711612459 / 1000000000000)))) (orderedInterval (-1021836669 / 1000000000000) (-1021834938 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (2150052402462629 / 4000000000000) 3 (IntervalRat.scale (931 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-30447948358 / 1000000000000) (-30447948357 / 1000000000000), orderedInterval (-16012318011 / 1000000000000) (-16012318010 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3684151438089017 / 4000000000000) 3 (IntervalRat.scale (931 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-25572177711 / 1000000000000) (-25572177306 / 1000000000000), orderedInterval (-6090371658 / 1000000000000) (-6090371252 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2713729274642603 / 4000000000000) 3 (IntervalRat.scale (931 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (18134156098 / 1000000000000) (18134156099 / 1000000000000), orderedInterval (24675121134 / 1000000000000) (24675121135 / 1000000000000)))) (orderedInterval (-3292563498 / 1000000000000) (-3292563253 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate594_chunkChecks3_1 :
    compactCertificate594.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (4163558574104069 / 4000000000000) 3 (IntervalRat.scale (931 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-24039763297 / 1000000000000) (-24039667849 / 1000000000000), orderedInterval (5816942476 / 1000000000000) (5817037925 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2403831663545501 / 4000000000000) 3 (IntervalRat.scale (931 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-32280791359 / 1000000000000) (-32280787192 / 1000000000000), orderedInterval (4185217373 / 1000000000000) (4185221541 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (4265641470177409 / 4000000000000) 3 (IntervalRat.scale (931 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-19815132475 / 1000000000000) (-19815129404 / 1000000000000), orderedInterval (14303869877 / 1000000000000) (14303872948 / 1000000000000)))) (orderedInterval (-13553011122 / 1000000000000) (-13552813605 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3985515585898021 / 4000000000000) 3 (IntervalRat.scale (931 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-24210798631 / 1000000000000) (-24210798313 / 1000000000000), orderedInterval (-7252187382 / 1000000000000) (-7252187065 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2844251981335093 / 4000000000000) 3 (IntervalRat.scale (931 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (28777109743 / 1000000000000) (28777141250 / 1000000000000), orderedInterval (-8216833656 / 1000000000000) (-8216802149 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (3225078603692547 / 4000000000000) 3 (IntervalRat.scale (931 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (9222827819 / 1000000000000) (9222827824 / 1000000000000), orderedInterval (-26548632632 / 1000000000000) (-26548632628 / 1000000000000)))) (orderedInterval (805032411 / 1000000000000) (805043354 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2688734308412243 / 4000000000000) 3 (IntervalRat.scale (931 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (19061541464 / 1000000000000) (19061541465 / 1000000000000), orderedInterval (24146736377 / 1000000000000) (24146736378 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2375578302613103 / 4000000000000) 3 (IntervalRat.scale (931 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-26023616819 / 1000000000000) (-26023616818 / 1000000000000), orderedInterval (-19845450297 / 1000000000000) (-19845450296 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (688535184709197 / 800000000000) 3 (IntervalRat.scale (931 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16628672806 / 1000000000000) (16628672807 / 1000000000000), orderedInterval (21511664818 / 1000000000000) (21511664819 / 1000000000000)))) (orderedInterval (-6669895822 / 1000000000000) (-6669895674 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate594_chunkChecks3_2 :
    compactCertificate594.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1904524556527159 / 4000000000000) 3 (IntervalRat.scale (931 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-20821628202 / 1000000000000) (-20821626251 / 1000000000000), orderedInterval (30080610708 / 1000000000000) (30080612660 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1614486558599999 / 4000000000000) 3 (IntervalRat.scale (931 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (30064485000 / 1000000000000) (30064521228 / 1000000000000), orderedInterval (-25987099710 / 1000000000000) (-25987063482 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (1010270725357397 / 4000000000000) 3 (IntervalRat.scale (931 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (45111336580 / 1000000000000) (45111355398 / 1000000000000), orderedInterval (-22124608385 / 1000000000000) (-22124589567 / 1000000000000)))) (orderedInterval (4308625130 / 1000000000000) (4308627003 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (543326956105899 / 4000000000000) 3 (IntervalRat.scale (931 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-68396699322 / 1000000000000) (-68396699299 / 1000000000000), orderedInterval (-2695474817 / 1000000000000) (-2695474794 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1475238377974697 / 4000000000000) 3 (IntervalRat.scale (931 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-37273915569 / 1000000000000) (-37273882109 / 1000000000000), orderedInterval (18402708602 / 1000000000000) (18402742062 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (2014311883116169 / 4000000000000) 3 (IntervalRat.scale (931 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (35219902104 / 1000000000000) (35219904806 / 1000000000000), orderedInterval (-4908455466 / 1000000000000) (-4908452764 / 1000000000000)))) (orderedInterval (-275263993 / 1000000000000) (-275263300 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (851729274642603 / 4000000000000) 3 (IntervalRat.scale (931 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (4850693564 / 1000000000000) (4850693565 / 1000000000000), orderedInterval (54451938017 / 1000000000000) (54451938018 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3462232214826763 / 4000000000000) 3 (IntervalRat.scale (931 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-18211851994 / 1000000000000) (-18211851099 / 1000000000000), orderedInterval (20106056211 / 1000000000000) (20106057106 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2312610665594117 / 4000000000000) 3 (IntervalRat.scale (931 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (25676800946 / 1000000000000) (25676800947 / 1000000000000), orderedInterval (20997529217 / 1000000000000) (20997529218 / 1000000000000)))) (orderedInterval (18033360411 / 1000000000000) (18033361293 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate594_chunkChecks3 :
    compactCertificate594.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate594.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate594_chunkChecks3_0
    compactCertificate594_chunkChecks3_1 compactCertificate594_chunkChecks3_2

theorem compactCertificate594_chunkChecks4_0 :
    compactCertificate594.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (931 / 2) 4 (IntervalRat.scale (931 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (35909008983 / 1000000000000) (35909008997 / 1000000000000), orderedInterval (8801486896 / 1000000000000) (8801486909 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1371540772495831 / 4000000000000) 4 (IntervalRat.scale (931 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-40705367308 / 1000000000000) (-40705367306 / 1000000000000), orderedInterval (-14073133692 / 1000000000000) (-14073133690 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (443528105741623 / 800000000000) 4 (IntervalRat.scale (931 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (25825728067 / 1000000000000) (25825747280 / 1000000000000), orderedInterval (-21962176173 / 1000000000000) (-21962156960 / 1000000000000)))) (orderedInterval (17175877999 / 1000000000000) (17175880339 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (400212176742917 / 4000000000000) 4 (IntervalRat.scale (931 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (24046854156 / 1000000000000) (24046854157 / 1000000000000), orderedInterval (75936629809 / 1000000000000) (75936629810 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (1075026201230849 / 4000000000000) 4 (IntervalRat.scale (931 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-28888868432 / 1000000000000) (-28888860196 / 1000000000000), orderedInterval (39222539081 / 1000000000000) (39222547318 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2918905258719933 / 4000000000000) 4 (IntervalRat.scale (931 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29413680839 / 1000000000000) (29413686462 / 1000000000000), orderedInterval (-2711618082 / 1000000000000) (-2711612459 / 1000000000000)))) (orderedInterval (-12740830419 / 1000000000000) (-12740827762 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (2150052402462629 / 4000000000000) 4 (IntervalRat.scale (931 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-30447948358 / 1000000000000) (-30447948357 / 1000000000000), orderedInterval (-16012318011 / 1000000000000) (-16012318010 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3684151438089017 / 4000000000000) 4 (IntervalRat.scale (931 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-25572177711 / 1000000000000) (-25572177306 / 1000000000000), orderedInterval (-6090371658 / 1000000000000) (-6090371252 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2713729274642603 / 4000000000000) 4 (IntervalRat.scale (931 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (18134156098 / 1000000000000) (18134156099 / 1000000000000), orderedInterval (24675121134 / 1000000000000) (24675121135 / 1000000000000)))) (orderedInterval (14079910193 / 1000000000000) (14079910657 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate594_chunkChecks4_1 :
    compactCertificate594.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (4163558574104069 / 4000000000000) 4 (IntervalRat.scale (931 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-24039763297 / 1000000000000) (-24039667849 / 1000000000000), orderedInterval (5816942476 / 1000000000000) (5817037925 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2403831663545501 / 4000000000000) 4 (IntervalRat.scale (931 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-32280791359 / 1000000000000) (-32280787192 / 1000000000000), orderedInterval (4185217373 / 1000000000000) (4185221541 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (4265641470177409 / 4000000000000) 4 (IntervalRat.scale (931 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-19815132475 / 1000000000000) (-19815129404 / 1000000000000), orderedInterval (14303869877 / 1000000000000) (14303872948 / 1000000000000)))) (orderedInterval (22617962614 / 1000000000000) (22618404322 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3985515585898021 / 4000000000000) 4 (IntervalRat.scale (931 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-24210798631 / 1000000000000) (-24210798313 / 1000000000000), orderedInterval (-7252187382 / 1000000000000) (-7252187065 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2844251981335093 / 4000000000000) 4 (IntervalRat.scale (931 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (28777109743 / 1000000000000) (28777141250 / 1000000000000), orderedInterval (-8216833656 / 1000000000000) (-8216802149 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (3225078603692547 / 4000000000000) 4 (IntervalRat.scale (931 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (9222827819 / 1000000000000) (9222827824 / 1000000000000), orderedInterval (-26548632632 / 1000000000000) (-26548632628 / 1000000000000)))) (orderedInterval (23566567307 / 1000000000000) (23566584133 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2688734308412243 / 4000000000000) 4 (IntervalRat.scale (931 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (19061541464 / 1000000000000) (19061541465 / 1000000000000), orderedInterval (24146736377 / 1000000000000) (24146736378 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2375578302613103 / 4000000000000) 4 (IntervalRat.scale (931 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-26023616819 / 1000000000000) (-26023616818 / 1000000000000), orderedInterval (-19845450297 / 1000000000000) (-19845450296 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (688535184709197 / 800000000000) 4 (IntervalRat.scale (931 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16628672806 / 1000000000000) (16628672807 / 1000000000000), orderedInterval (21511664818 / 1000000000000) (21511664819 / 1000000000000)))) (orderedInterval (9906801132 / 1000000000000) (9906801367 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate594_chunkChecks4_2 :
    compactCertificate594.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1904524556527159 / 4000000000000) 4 (IntervalRat.scale (931 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-20821628202 / 1000000000000) (-20821626251 / 1000000000000), orderedInterval (30080610708 / 1000000000000) (30080612660 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1614486558599999 / 4000000000000) 4 (IntervalRat.scale (931 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (30064485000 / 1000000000000) (30064521228 / 1000000000000), orderedInterval (-25987099710 / 1000000000000) (-25987063482 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (1010270725357397 / 4000000000000) 4 (IntervalRat.scale (931 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (45111336580 / 1000000000000) (45111355398 / 1000000000000), orderedInterval (-22124608385 / 1000000000000) (-22124589567 / 1000000000000)))) (orderedInterval (2790870987 / 1000000000000) (2790872647 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (543326956105899 / 4000000000000) 4 (IntervalRat.scale (931 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-68396699322 / 1000000000000) (-68396699299 / 1000000000000), orderedInterval (-2695474817 / 1000000000000) (-2695474794 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1475238377974697 / 4000000000000) 4 (IntervalRat.scale (931 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-37273915569 / 1000000000000) (-37273882109 / 1000000000000), orderedInterval (18402708602 / 1000000000000) (18402742062 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (2014311883116169 / 4000000000000) 4 (IntervalRat.scale (931 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (35219902104 / 1000000000000) (35219904806 / 1000000000000), orderedInterval (-4908455466 / 1000000000000) (-4908452764 / 1000000000000)))) (orderedInterval (-3353241850 / 1000000000000) (-3353241210 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (851729274642603 / 4000000000000) 4 (IntervalRat.scale (931 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (4850693564 / 1000000000000) (4850693565 / 1000000000000), orderedInterval (54451938017 / 1000000000000) (54451938018 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3462232214826763 / 4000000000000) 4 (IntervalRat.scale (931 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-18211851994 / 1000000000000) (-18211851099 / 1000000000000), orderedInterval (20106056211 / 1000000000000) (20106057106 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2312610665594117 / 4000000000000) 4 (IntervalRat.scale (931 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (25676800946 / 1000000000000) (25676800947 / 1000000000000), orderedInterval (20997529217 / 1000000000000) (20997529218 / 1000000000000)))) (orderedInterval (6181302743 / 1000000000000) (6181304279 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate594_chunkChecks4 :
    compactCertificate594.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate594.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate594_chunkChecks4_0
    compactCertificate594_chunkChecks4_1 compactCertificate594_chunkChecks4_2

theorem compactCertificate594_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate594.chunkCheck r b = true :=
  compactCertificate594.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate594_chunkChecks0
    · exact compactCertificate594_chunkChecks1
    · exact compactCertificate594_chunkChecks2
    · exact compactCertificate594_chunkChecks3
    · exact compactCertificate594_chunkChecks4)

theorem compactCertificate594_coefficient0 :
    compactCertificate594.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate594_coefficient1 :
    compactCertificate594.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate594_coefficient2 :
    compactCertificate594.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate594_coefficient3 :
    compactCertificate594.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate594_coefficient4 :
    compactCertificate594.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate594_coefficients : ∀ r : Fin 5,
    compactCertificate594.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate594_coefficient0
  · exact compactCertificate594_coefficient1
  · exact compactCertificate594_coefficient2
  · exact compactCertificate594_coefficient3
  · exact compactCertificate594_coefficient4

theorem compactCertificate594_lower : (1 : ℚ) ≤ compactCertificate594.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate594, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate594_proves {t : ℝ} (ht : t ∈ compactCertificate594.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate594.proves compactCertificate594_states compactCertificate594_chunks
    compactCertificate594_coefficients compactCertificate594_lower ht

end Erdos232
