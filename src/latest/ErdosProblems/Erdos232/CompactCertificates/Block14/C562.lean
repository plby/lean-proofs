/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate562 : CompactCertificate where
  left := 433
  right := 434
  center := 867 / 2
  grid := fun i =>
    match i.val with
    | 0 => 138
    | 1 => 102
    | 2 => 164
    | 3 => 30
    | 4 => 80
    | 5 => 216
    | 6 => 159
    | 7 => 273
    | 8 => 201
    | 9 => 309
    | 10 => 178
    | 11 => 316
    | 12 => 296
    | 13 => 211
    | 14 => 239
    | 15 => 199
    | 16 => 176
    | 17 => 255
    | 18 => 141
    | 19 => 120
    | 20 => 75
    | 21 => 40
    | 22 => 109
    | 23 => 149
    | 24 => 63
    | 25 => 257
    | _ => 171
  point := fun i =>
    match i.val with
    | 0 => 867 / 2
    | 1 => 1277256551830167 / 4000000000000
    | 2 => 413038525969911 / 800000000000
    | 3 => 372700276300869 / 4000000000000
    | 4 => 1001125366774593 / 4000000000000
    | 5 => 2718250117411581 / 4000000000000
    | 6 => 2002250733550053 / 4000000000000
    | 7 => 3430890759208569 / 4000000000000
    | 8 => 2527178604849771 / 4000000000000
    | 9 => 3877341872984133 / 4000000000000
    | 10 => 2238584374107357 / 4000000000000
    | 11 => 3972407255256513 / 4000000000000
    | 12 => 3711538144976997 / 4000000000000
    | 13 => 2648728751683701 / 4000000000000
    | 14 => 3003376100323779 / 4000000000000
    | 15 => 2503901874751251 / 4000000000000
    | 16 => 2212273242068271 / 4000000000000
    | 17 => 641203013042829 / 800000000000
    | 18 => 1773601278742263 / 4000000000000
    | 19 => 1503501446086143 / 4000000000000
    | 20 => 940821395150229 / 4000000000000
    | 21 => 505976875342443 / 4000000000000
    | 22 => 1373825643076329 / 4000000000000
    | 23 => 1875841463653833 / 4000000000000
    | 24 => 793178604849771 / 4000000000000
    | 25 => 3224226992754891 / 4000000000000
    | _ => 2153634207379269 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (25990183106 / 1000000000000) (25990183107 / 1000000000000), orderedInterval (28131489158 / 1000000000000) (28131489159 / 1000000000000))
    | 1 => (orderedInterval (-15029600585 / 1000000000000) (-15029600380 / 1000000000000), orderedInterval (42069020640 / 1000000000000) (42069020845 / 1000000000000))
    | 2 => (orderedInterval (33635190098 / 1000000000000) (33635204268 / 1000000000000), orderedInterval (-10118202686 / 1000000000000) (-10118188516 / 1000000000000))
    | 3 => (orderedInterval (-23529712088 / 1000000000000) (-23529711645 / 1000000000000), orderedInterval (79366069318 / 1000000000000) (79366069762 / 1000000000000))
    | 4 => (orderedInterval (-13022766341 / 1000000000000) (-13022766233 / 1000000000000), orderedInterval (48750019881 / 1000000000000) (48750019989 / 1000000000000))
    | 5 => (orderedInterval (30039421041 / 1000000000000) (30039433204 / 1000000000000), orderedInterval (-5890737039 / 1000000000000) (-5890724876 / 1000000000000))
    | 6 => (orderedInterval (-34428681902 / 1000000000000) (-34428671909 / 1000000000000), orderedInterval (9333521490 / 1000000000000) (9333531483 / 1000000000000))
    | 7 => (orderedInterval (-20524178103 / 1000000000000) (-20524178102 / 1000000000000), orderedInterval (-17903924493 / 1000000000000) (-17903924492 / 1000000000000))
    | 8 => (orderedInterval (-28568394249 / 1000000000000) (-28568394246 / 1000000000000), orderedInterval (-13815159023 / 1000000000000) (-13815159021 / 1000000000000))
    | 9 => (orderedInterval (15127014563 / 1000000000000) (15127014679 / 1000000000000), orderedInterval (-20694330671 / 1000000000000) (-20694330554 / 1000000000000))
    | 10 => (orderedInterval (31762574390 / 1000000000000) (31762574396 / 1000000000000), orderedInterval (11315274459 / 1000000000000) (11315274465 / 1000000000000))
    | 11 => (orderedInterval (23045601834 / 1000000000000) (23045601882 / 1000000000000), orderedInterval (10473719245 / 1000000000000) (10473719292 / 1000000000000))
    | 12 => (orderedInterval (-24787213676 / 1000000000000) (-24787113461 / 1000000000000), orderedInterval (8480562879 / 1000000000000) (8480663094 / 1000000000000))
    | 13 => (orderedInterval (-2828416262 / 1000000000000) (-2828416261 / 1000000000000), orderedInterval (-30874992333 / 1000000000000) (-30874992332 / 1000000000000))
    | 14 => (orderedInterval (-20655783204 / 1000000000000) (-20655783203 / 1000000000000), orderedInterval (-20509666097 / 1000000000000) (-20509666096 / 1000000000000))
    | 15 => (orderedInterval (-31887834233 / 1000000000000) (-31887832902 / 1000000000000), orderedInterval (437891027 / 1000000000000) (437892357 / 1000000000000))
    | 16 => (orderedInterval (27261154818 / 1000000000000) (27261154819 / 1000000000000), orderedInterval (20171846275 / 1000000000000) (20171846276 / 1000000000000))
    | 17 => (orderedInterval (-26089002246 / 1000000000000) (-26089002226 / 1000000000000), orderedInterval (-10644191665 / 1000000000000) (-10644191645 / 1000000000000))
    | 18 => (orderedInterval (-35595231632 / 1000000000000) (-35595231629 / 1000000000000), orderedInterval (-12950099594 / 1000000000000) (-12950099592 / 1000000000000))
    | 19 => (orderedInterval (-13362759527 / 1000000000000) (-13362759410 / 1000000000000), orderedInterval (38942535809 / 1000000000000) (38942535926 / 1000000000000))
    | 20 => (orderedInterval (-18850383849 / 1000000000000) (-18850383848 / 1000000000000), orderedInterval (-48450367309 / 1000000000000) (-48450367308 / 1000000000000))
    | 21 => (orderedInterval (70872878774 / 1000000000000) (70872878850 / 1000000000000), orderedInterval (-3409557356 / 1000000000000) (-3409557280 / 1000000000000))
    | 22 => (orderedInterval (-41849086731 / 1000000000000) (-41849083425 / 1000000000000), orderedInterval (10171322663 / 1000000000000) (10171325969 / 1000000000000))
    | 23 => (orderedInterval (-36734136661 / 1000000000000) (-36734135546 / 1000000000000), orderedInterval (2887925450 / 1000000000000) (2887926565 / 1000000000000))
    | 24 => (orderedInterval (-51926140224 / 1000000000000) (-51926140223 / 1000000000000), orderedInterval (-22543785687 / 1000000000000) (-22543785686 / 1000000000000))
    | 25 => (orderedInterval (14624986854 / 1000000000000) (14624986969 / 1000000000000), orderedInterval (-24007093872 / 1000000000000) (-24007093757 / 1000000000000))
    | _ => (orderedInterval (-31528384877 / 1000000000000) (-31528337418 / 1000000000000), orderedInterval (13754132798 / 1000000000000) (13754180257 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (12135303309 / 1000000000000) (12135304173 / 1000000000000)
      | 1 => orderedInterval (-2355695797 / 1000000000000) (-2355694871 / 1000000000000)
      | 2 => orderedInterval (-57393966 / 1000000000000) (-57393941 / 1000000000000)
      | 3 => orderedInterval (2941525523 / 1000000000000) (2941525722 / 1000000000000)
      | 4 => orderedInterval (284550878 / 1000000000000) (284552739 / 1000000000000)
      | 5 => orderedInterval (-2596277018 / 1000000000000) (-2596276960 / 1000000000000)
      | 6 => orderedInterval (5834060694 / 1000000000000) (5834060810 / 1000000000000)
      | 7 => orderedInterval (2456010993 / 1000000000000) (2456011207 / 1000000000000)
      | _ => orderedInterval (4412024659 / 1000000000000) (4412033693 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (10731931130 / 1000000000000) (10731932156 / 1000000000000)
      | 1 => orderedInterval (1499049765 / 1000000000000) (1499051183 / 1000000000000)
      | 2 => orderedInterval (606025844 / 1000000000000) (606025887 / 1000000000000)
      | 3 => orderedInterval (12715559434 / 1000000000000) (12715559853 / 1000000000000)
      | 4 => orderedInterval (-4607741595 / 1000000000000) (-4607737638 / 1000000000000)
      | 5 => orderedInterval (-1969355042 / 1000000000000) (-1969354958 / 1000000000000)
      | 6 => orderedInterval (-649047506 / 1000000000000) (-649047399 / 1000000000000)
      | 7 => orderedInterval (-403885675 / 1000000000000) (-403885475 / 1000000000000)
      | _ => orderedInterval (366367285 / 1000000000000) (366378531 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-13050095869 / 1000000000000) (-13050094646 / 1000000000000)
      | 1 => orderedInterval (5391058267 / 1000000000000) (5391060479 / 1000000000000)
      | 2 => orderedInterval (-1013124786 / 1000000000000) (-1013124710 / 1000000000000)
      | 3 => orderedInterval (-7705555563 / 1000000000000) (-7705554660 / 1000000000000)
      | 4 => orderedInterval (-1729045801 / 1000000000000) (-1729037364 / 1000000000000)
      | 5 => orderedInterval (5595184729 / 1000000000000) (5595184853 / 1000000000000)
      | 6 => orderedInterval (-6340803160 / 1000000000000) (-6340803058 / 1000000000000)
      | 7 => orderedInterval (-3778289787 / 1000000000000) (-3778289593 / 1000000000000)
      | _ => orderedInterval (-4944465389 / 1000000000000) (-4944451346 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-10273762133 / 1000000000000) (-10273760679 / 1000000000000)
      | 1 => orderedInterval (-1959661748 / 1000000000000) (-1959658289 / 1000000000000)
      | 2 => orderedInterval (-3241570432 / 1000000000000) (-3241570295 / 1000000000000)
      | 3 => orderedInterval (-60798737565 / 1000000000000) (-60798735579 / 1000000000000)
      | 4 => orderedInterval (11372243364 / 1000000000000) (11372261361 / 1000000000000)
      | 5 => orderedInterval (4091645377 / 1000000000000) (4091645565 / 1000000000000)
      | 6 => orderedInterval (-512366752 / 1000000000000) (-512366654 / 1000000000000)
      | 7 => orderedInterval (402116943 / 1000000000000) (402117137 / 1000000000000)
      | _ => orderedInterval (-7594664985 / 1000000000000) (-7594647449 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (14279052018 / 1000000000000) (14279053751 / 1000000000000)
      | 1 => orderedInterval (-12939345320 / 1000000000000) (-12939339894 / 1000000000000)
      | 2 => orderedInterval (6601975549 / 1000000000000) (6601975803 / 1000000000000)
      | 3 => orderedInterval (29854623926 / 1000000000000) (29854628345 / 1000000000000)
      | 4 => orderedInterval (8824942818 / 1000000000000) (8824981284 / 1000000000000)
      | 5 => orderedInterval (-13559225707 / 1000000000000) (-13559225415 / 1000000000000)
      | 6 => orderedInterval (6606058541 / 1000000000000) (6606058637 / 1000000000000)
      | 7 => orderedInterval (4218473444 / 1000000000000) (4218473642 / 1000000000000)
      | _ => orderedInterval (-133452077 / 1000000000000) (-133430081 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (23054109275 / 1000000000000) (23054122572 / 1000000000000)
    | 1 => orderedInterval (18288903640 / 1000000000000) (18288922140 / 1000000000000)
    | 2 => orderedInterval (-27575137359 / 1000000000000) (-27575110045 / 1000000000000)
    | 3 => orderedInterval (-68514757931 / 1000000000000) (-68514714882 / 1000000000000)
    | _ => orderedInterval (43753103192 / 1000000000000) (43753176072 / 1000000000000)

theorem compactCertificate562_stateChecks0 :
    compactCertificate562.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 138 12 (867 / 2)) (orderedInterval (25990183106 / 1000000000000) (25990183107 / 1000000000000), orderedInterval (28131489158 / 1000000000000) (28131489159 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 102 12 (1277256551830167 / 4000000000000)) (orderedInterval (-15029600585 / 1000000000000) (-15029600380 / 1000000000000), orderedInterval (42069020640 / 1000000000000) (42069020845 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 164 12 (413038525969911 / 800000000000)) (orderedInterval (33635190098 / 1000000000000) (33635204268 / 1000000000000), orderedInterval (-10118202686 / 1000000000000) (-10118188516 / 1000000000000))) = true
  rfl'

theorem compactCertificate562_stateChecks1 :
    compactCertificate562.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (372700276300869 / 4000000000000)) (orderedInterval (-23529712088 / 1000000000000) (-23529711645 / 1000000000000), orderedInterval (79366069318 / 1000000000000) (79366069762 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 80 12 (1001125366774593 / 4000000000000)) (orderedInterval (-13022766341 / 1000000000000) (-13022766233 / 1000000000000), orderedInterval (48750019881 / 1000000000000) (48750019989 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 216 12 (2718250117411581 / 4000000000000)) (orderedInterval (30039421041 / 1000000000000) (30039433204 / 1000000000000), orderedInterval (-5890737039 / 1000000000000) (-5890724876 / 1000000000000))) = true
  rfl'

theorem compactCertificate562_stateChecks2 :
    compactCertificate562.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 159 12 (2002250733550053 / 4000000000000)) (orderedInterval (-34428681902 / 1000000000000) (-34428671909 / 1000000000000), orderedInterval (9333521490 / 1000000000000) (9333531483 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 273 12 (3430890759208569 / 4000000000000)) (orderedInterval (-20524178103 / 1000000000000) (-20524178102 / 1000000000000), orderedInterval (-17903924493 / 1000000000000) (-17903924492 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 201 12 (2527178604849771 / 4000000000000)) (orderedInterval (-28568394249 / 1000000000000) (-28568394246 / 1000000000000), orderedInterval (-13815159023 / 1000000000000) (-13815159021 / 1000000000000))) = true
  rfl'

theorem compactCertificate562_stateChecks3 :
    compactCertificate562.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 309 12 (3877341872984133 / 4000000000000)) (orderedInterval (15127014563 / 1000000000000) (15127014679 / 1000000000000), orderedInterval (-20694330671 / 1000000000000) (-20694330554 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 178 12 (2238584374107357 / 4000000000000)) (orderedInterval (31762574390 / 1000000000000) (31762574396 / 1000000000000), orderedInterval (11315274459 / 1000000000000) (11315274465 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 316 12 (3972407255256513 / 4000000000000)) (orderedInterval (23045601834 / 1000000000000) (23045601882 / 1000000000000), orderedInterval (10473719245 / 1000000000000) (10473719292 / 1000000000000))) = true
  rfl'

theorem compactCertificate562_stateChecks4 :
    compactCertificate562.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 296 12 (3711538144976997 / 4000000000000)) (orderedInterval (-24787213676 / 1000000000000) (-24787113461 / 1000000000000), orderedInterval (8480562879 / 1000000000000) (8480663094 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 211 12 (2648728751683701 / 4000000000000)) (orderedInterval (-2828416262 / 1000000000000) (-2828416261 / 1000000000000), orderedInterval (-30874992333 / 1000000000000) (-30874992332 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 239 12 (3003376100323779 / 4000000000000)) (orderedInterval (-20655783204 / 1000000000000) (-20655783203 / 1000000000000), orderedInterval (-20509666097 / 1000000000000) (-20509666096 / 1000000000000))) = true
  rfl'

theorem compactCertificate562_stateChecks5 :
    compactCertificate562.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 199 12 (2503901874751251 / 4000000000000)) (orderedInterval (-31887834233 / 1000000000000) (-31887832902 / 1000000000000), orderedInterval (437891027 / 1000000000000) (437892357 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 176 12 (2212273242068271 / 4000000000000)) (orderedInterval (27261154818 / 1000000000000) (27261154819 / 1000000000000), orderedInterval (20171846275 / 1000000000000) (20171846276 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 255 12 (641203013042829 / 800000000000)) (orderedInterval (-26089002246 / 1000000000000) (-26089002226 / 1000000000000), orderedInterval (-10644191665 / 1000000000000) (-10644191645 / 1000000000000))) = true
  rfl'

theorem compactCertificate562_stateChecks6 :
    compactCertificate562.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 141 12 (1773601278742263 / 4000000000000)) (orderedInterval (-35595231632 / 1000000000000) (-35595231629 / 1000000000000), orderedInterval (-12950099594 / 1000000000000) (-12950099592 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 120 12 (1503501446086143 / 4000000000000)) (orderedInterval (-13362759527 / 1000000000000) (-13362759410 / 1000000000000), orderedInterval (38942535809 / 1000000000000) (38942535926 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 75 12 (940821395150229 / 4000000000000)) (orderedInterval (-18850383849 / 1000000000000) (-18850383848 / 1000000000000), orderedInterval (-48450367309 / 1000000000000) (-48450367308 / 1000000000000))) = true
  rfl'

theorem compactCertificate562_stateChecks7 :
    compactCertificate562.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 40 12 (505976875342443 / 4000000000000)) (orderedInterval (70872878774 / 1000000000000) (70872878850 / 1000000000000), orderedInterval (-3409557356 / 1000000000000) (-3409557280 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 109 12 (1373825643076329 / 4000000000000)) (orderedInterval (-41849086731 / 1000000000000) (-41849083425 / 1000000000000), orderedInterval (10171322663 / 1000000000000) (10171325969 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 149 12 (1875841463653833 / 4000000000000)) (orderedInterval (-36734136661 / 1000000000000) (-36734135546 / 1000000000000), orderedInterval (2887925450 / 1000000000000) (2887926565 / 1000000000000))) = true
  rfl'

theorem compactCertificate562_stateChecks8 :
    compactCertificate562.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (793178604849771 / 4000000000000)) (orderedInterval (-51926140224 / 1000000000000) (-51926140223 / 1000000000000), orderedInterval (-22543785687 / 1000000000000) (-22543785686 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 257 12 (3224226992754891 / 4000000000000)) (orderedInterval (14624986854 / 1000000000000) (14624986969 / 1000000000000), orderedInterval (-24007093872 / 1000000000000) (-24007093757 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 171 12 (2153634207379269 / 4000000000000)) (orderedInterval (-31528384877 / 1000000000000) (-31528337418 / 1000000000000), orderedInterval (13754132798 / 1000000000000) (13754180257 / 1000000000000))) = true
  rfl'

theorem compactCertificate562_states : ∀ j,
    BesselStateValid (compactCertificate562.point j) (compactCertificate562.state j) :=
  compactCertificate562.statesValid_of_checks3 compactCertificate562_stateChecks0
    compactCertificate562_stateChecks1 compactCertificate562_stateChecks2
    compactCertificate562_stateChecks3 compactCertificate562_stateChecks4
    compactCertificate562_stateChecks5 compactCertificate562_stateChecks6
    compactCertificate562_stateChecks7 compactCertificate562_stateChecks8

theorem compactCertificate562_chunkChecks0_0 :
    compactCertificate562.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (867 / 2) 0 (IntervalRat.scale (867 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (25990183106 / 1000000000000) (25990183107 / 1000000000000), orderedInterval (28131489158 / 1000000000000) (28131489159 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1277256551830167 / 4000000000000) 0 (IntervalRat.scale (867 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-15029600585 / 1000000000000) (-15029600380 / 1000000000000), orderedInterval (42069020640 / 1000000000000) (42069020845 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (413038525969911 / 800000000000) 0 (IntervalRat.scale (867 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (33635190098 / 1000000000000) (33635204268 / 1000000000000), orderedInterval (-10118202686 / 1000000000000) (-10118188516 / 1000000000000)))) (orderedInterval (12135303309 / 1000000000000) (12135304173 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (372700276300869 / 4000000000000) 0 (IntervalRat.scale (867 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-23529712088 / 1000000000000) (-23529711645 / 1000000000000), orderedInterval (79366069318 / 1000000000000) (79366069762 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (1001125366774593 / 4000000000000) 0 (IntervalRat.scale (867 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-13022766341 / 1000000000000) (-13022766233 / 1000000000000), orderedInterval (48750019881 / 1000000000000) (48750019989 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2718250117411581 / 4000000000000) 0 (IntervalRat.scale (867 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30039421041 / 1000000000000) (30039433204 / 1000000000000), orderedInterval (-5890737039 / 1000000000000) (-5890724876 / 1000000000000)))) (orderedInterval (-2355695797 / 1000000000000) (-2355694871 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (2002250733550053 / 4000000000000) 0 (IntervalRat.scale (867 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-34428681902 / 1000000000000) (-34428671909 / 1000000000000), orderedInterval (9333521490 / 1000000000000) (9333531483 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3430890759208569 / 4000000000000) 0 (IntervalRat.scale (867 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-20524178103 / 1000000000000) (-20524178102 / 1000000000000), orderedInterval (-17903924493 / 1000000000000) (-17903924492 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2527178604849771 / 4000000000000) 0 (IntervalRat.scale (867 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-28568394249 / 1000000000000) (-28568394246 / 1000000000000), orderedInterval (-13815159023 / 1000000000000) (-13815159021 / 1000000000000)))) (orderedInterval (-57393966 / 1000000000000) (-57393941 / 1000000000000))) = true
  rfl'

theorem compactCertificate562_chunkChecks0_1 :
    compactCertificate562.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3877341872984133 / 4000000000000) 0 (IntervalRat.scale (867 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (15127014563 / 1000000000000) (15127014679 / 1000000000000), orderedInterval (-20694330671 / 1000000000000) (-20694330554 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2238584374107357 / 4000000000000) 0 (IntervalRat.scale (867 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (31762574390 / 1000000000000) (31762574396 / 1000000000000), orderedInterval (11315274459 / 1000000000000) (11315274465 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3972407255256513 / 4000000000000) 0 (IntervalRat.scale (867 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (23045601834 / 1000000000000) (23045601882 / 1000000000000), orderedInterval (10473719245 / 1000000000000) (10473719292 / 1000000000000)))) (orderedInterval (2941525523 / 1000000000000) (2941525722 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3711538144976997 / 4000000000000) 0 (IntervalRat.scale (867 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-24787213676 / 1000000000000) (-24787113461 / 1000000000000), orderedInterval (8480562879 / 1000000000000) (8480663094 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2648728751683701 / 4000000000000) 0 (IntervalRat.scale (867 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-2828416262 / 1000000000000) (-2828416261 / 1000000000000), orderedInterval (-30874992333 / 1000000000000) (-30874992332 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (3003376100323779 / 4000000000000) 0 (IntervalRat.scale (867 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-20655783204 / 1000000000000) (-20655783203 / 1000000000000), orderedInterval (-20509666097 / 1000000000000) (-20509666096 / 1000000000000)))) (orderedInterval (284550878 / 1000000000000) (284552739 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2503901874751251 / 4000000000000) 0 (IntervalRat.scale (867 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-31887834233 / 1000000000000) (-31887832902 / 1000000000000), orderedInterval (437891027 / 1000000000000) (437892357 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2212273242068271 / 4000000000000) 0 (IntervalRat.scale (867 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (27261154818 / 1000000000000) (27261154819 / 1000000000000), orderedInterval (20171846275 / 1000000000000) (20171846276 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (641203013042829 / 800000000000) 0 (IntervalRat.scale (867 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-26089002246 / 1000000000000) (-26089002226 / 1000000000000), orderedInterval (-10644191665 / 1000000000000) (-10644191645 / 1000000000000)))) (orderedInterval (-2596277018 / 1000000000000) (-2596276960 / 1000000000000))) = true
  rfl'

theorem compactCertificate562_chunkChecks0_2 :
    compactCertificate562.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1773601278742263 / 4000000000000) 0 (IntervalRat.scale (867 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-35595231632 / 1000000000000) (-35595231629 / 1000000000000), orderedInterval (-12950099594 / 1000000000000) (-12950099592 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1503501446086143 / 4000000000000) 0 (IntervalRat.scale (867 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-13362759527 / 1000000000000) (-13362759410 / 1000000000000), orderedInterval (38942535809 / 1000000000000) (38942535926 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (940821395150229 / 4000000000000) 0 (IntervalRat.scale (867 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-18850383849 / 1000000000000) (-18850383848 / 1000000000000), orderedInterval (-48450367309 / 1000000000000) (-48450367308 / 1000000000000)))) (orderedInterval (5834060694 / 1000000000000) (5834060810 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (505976875342443 / 4000000000000) 0 (IntervalRat.scale (867 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (70872878774 / 1000000000000) (70872878850 / 1000000000000), orderedInterval (-3409557356 / 1000000000000) (-3409557280 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1373825643076329 / 4000000000000) 0 (IntervalRat.scale (867 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-41849086731 / 1000000000000) (-41849083425 / 1000000000000), orderedInterval (10171322663 / 1000000000000) (10171325969 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1875841463653833 / 4000000000000) 0 (IntervalRat.scale (867 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-36734136661 / 1000000000000) (-36734135546 / 1000000000000), orderedInterval (2887925450 / 1000000000000) (2887926565 / 1000000000000)))) (orderedInterval (2456010993 / 1000000000000) (2456011207 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (793178604849771 / 4000000000000) 0 (IntervalRat.scale (867 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-51926140224 / 1000000000000) (-51926140223 / 1000000000000), orderedInterval (-22543785687 / 1000000000000) (-22543785686 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3224226992754891 / 4000000000000) 0 (IntervalRat.scale (867 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (14624986854 / 1000000000000) (14624986969 / 1000000000000), orderedInterval (-24007093872 / 1000000000000) (-24007093757 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2153634207379269 / 4000000000000) 0 (IntervalRat.scale (867 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-31528384877 / 1000000000000) (-31528337418 / 1000000000000), orderedInterval (13754132798 / 1000000000000) (13754180257 / 1000000000000)))) (orderedInterval (4412024659 / 1000000000000) (4412033693 / 1000000000000))) = true
  rfl'

theorem compactCertificate562_chunkChecks0 :
    compactCertificate562.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate562.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate562_chunkChecks0_0
    compactCertificate562_chunkChecks0_1 compactCertificate562_chunkChecks0_2

theorem compactCertificate562_chunkChecks1_0 :
    compactCertificate562.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (867 / 2) 1 (IntervalRat.scale (867 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (25990183106 / 1000000000000) (25990183107 / 1000000000000), orderedInterval (28131489158 / 1000000000000) (28131489159 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1277256551830167 / 4000000000000) 1 (IntervalRat.scale (867 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-15029600585 / 1000000000000) (-15029600380 / 1000000000000), orderedInterval (42069020640 / 1000000000000) (42069020845 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (413038525969911 / 800000000000) 1 (IntervalRat.scale (867 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (33635190098 / 1000000000000) (33635204268 / 1000000000000), orderedInterval (-10118202686 / 1000000000000) (-10118188516 / 1000000000000)))) (orderedInterval (10731931130 / 1000000000000) (10731932156 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (372700276300869 / 4000000000000) 1 (IntervalRat.scale (867 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-23529712088 / 1000000000000) (-23529711645 / 1000000000000), orderedInterval (79366069318 / 1000000000000) (79366069762 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (1001125366774593 / 4000000000000) 1 (IntervalRat.scale (867 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-13022766341 / 1000000000000) (-13022766233 / 1000000000000), orderedInterval (48750019881 / 1000000000000) (48750019989 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2718250117411581 / 4000000000000) 1 (IntervalRat.scale (867 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30039421041 / 1000000000000) (30039433204 / 1000000000000), orderedInterval (-5890737039 / 1000000000000) (-5890724876 / 1000000000000)))) (orderedInterval (1499049765 / 1000000000000) (1499051183 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (2002250733550053 / 4000000000000) 1 (IntervalRat.scale (867 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-34428681902 / 1000000000000) (-34428671909 / 1000000000000), orderedInterval (9333521490 / 1000000000000) (9333531483 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3430890759208569 / 4000000000000) 1 (IntervalRat.scale (867 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-20524178103 / 1000000000000) (-20524178102 / 1000000000000), orderedInterval (-17903924493 / 1000000000000) (-17903924492 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2527178604849771 / 4000000000000) 1 (IntervalRat.scale (867 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-28568394249 / 1000000000000) (-28568394246 / 1000000000000), orderedInterval (-13815159023 / 1000000000000) (-13815159021 / 1000000000000)))) (orderedInterval (606025844 / 1000000000000) (606025887 / 1000000000000))) = true
  rfl'

theorem compactCertificate562_chunkChecks1_1 :
    compactCertificate562.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3877341872984133 / 4000000000000) 1 (IntervalRat.scale (867 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (15127014563 / 1000000000000) (15127014679 / 1000000000000), orderedInterval (-20694330671 / 1000000000000) (-20694330554 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2238584374107357 / 4000000000000) 1 (IntervalRat.scale (867 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (31762574390 / 1000000000000) (31762574396 / 1000000000000), orderedInterval (11315274459 / 1000000000000) (11315274465 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3972407255256513 / 4000000000000) 1 (IntervalRat.scale (867 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (23045601834 / 1000000000000) (23045601882 / 1000000000000), orderedInterval (10473719245 / 1000000000000) (10473719292 / 1000000000000)))) (orderedInterval (12715559434 / 1000000000000) (12715559853 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3711538144976997 / 4000000000000) 1 (IntervalRat.scale (867 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-24787213676 / 1000000000000) (-24787113461 / 1000000000000), orderedInterval (8480562879 / 1000000000000) (8480663094 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2648728751683701 / 4000000000000) 1 (IntervalRat.scale (867 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-2828416262 / 1000000000000) (-2828416261 / 1000000000000), orderedInterval (-30874992333 / 1000000000000) (-30874992332 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (3003376100323779 / 4000000000000) 1 (IntervalRat.scale (867 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-20655783204 / 1000000000000) (-20655783203 / 1000000000000), orderedInterval (-20509666097 / 1000000000000) (-20509666096 / 1000000000000)))) (orderedInterval (-4607741595 / 1000000000000) (-4607737638 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2503901874751251 / 4000000000000) 1 (IntervalRat.scale (867 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-31887834233 / 1000000000000) (-31887832902 / 1000000000000), orderedInterval (437891027 / 1000000000000) (437892357 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2212273242068271 / 4000000000000) 1 (IntervalRat.scale (867 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (27261154818 / 1000000000000) (27261154819 / 1000000000000), orderedInterval (20171846275 / 1000000000000) (20171846276 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (641203013042829 / 800000000000) 1 (IntervalRat.scale (867 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-26089002246 / 1000000000000) (-26089002226 / 1000000000000), orderedInterval (-10644191665 / 1000000000000) (-10644191645 / 1000000000000)))) (orderedInterval (-1969355042 / 1000000000000) (-1969354958 / 1000000000000))) = true
  rfl'

theorem compactCertificate562_chunkChecks1_2 :
    compactCertificate562.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1773601278742263 / 4000000000000) 1 (IntervalRat.scale (867 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-35595231632 / 1000000000000) (-35595231629 / 1000000000000), orderedInterval (-12950099594 / 1000000000000) (-12950099592 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1503501446086143 / 4000000000000) 1 (IntervalRat.scale (867 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-13362759527 / 1000000000000) (-13362759410 / 1000000000000), orderedInterval (38942535809 / 1000000000000) (38942535926 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (940821395150229 / 4000000000000) 1 (IntervalRat.scale (867 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-18850383849 / 1000000000000) (-18850383848 / 1000000000000), orderedInterval (-48450367309 / 1000000000000) (-48450367308 / 1000000000000)))) (orderedInterval (-649047506 / 1000000000000) (-649047399 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (505976875342443 / 4000000000000) 1 (IntervalRat.scale (867 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (70872878774 / 1000000000000) (70872878850 / 1000000000000), orderedInterval (-3409557356 / 1000000000000) (-3409557280 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1373825643076329 / 4000000000000) 1 (IntervalRat.scale (867 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-41849086731 / 1000000000000) (-41849083425 / 1000000000000), orderedInterval (10171322663 / 1000000000000) (10171325969 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1875841463653833 / 4000000000000) 1 (IntervalRat.scale (867 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-36734136661 / 1000000000000) (-36734135546 / 1000000000000), orderedInterval (2887925450 / 1000000000000) (2887926565 / 1000000000000)))) (orderedInterval (-403885675 / 1000000000000) (-403885475 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (793178604849771 / 4000000000000) 1 (IntervalRat.scale (867 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-51926140224 / 1000000000000) (-51926140223 / 1000000000000), orderedInterval (-22543785687 / 1000000000000) (-22543785686 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3224226992754891 / 4000000000000) 1 (IntervalRat.scale (867 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (14624986854 / 1000000000000) (14624986969 / 1000000000000), orderedInterval (-24007093872 / 1000000000000) (-24007093757 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2153634207379269 / 4000000000000) 1 (IntervalRat.scale (867 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-31528384877 / 1000000000000) (-31528337418 / 1000000000000), orderedInterval (13754132798 / 1000000000000) (13754180257 / 1000000000000)))) (orderedInterval (366367285 / 1000000000000) (366378531 / 1000000000000))) = true
  rfl'

theorem compactCertificate562_chunkChecks1 :
    compactCertificate562.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate562.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate562_chunkChecks1_0
    compactCertificate562_chunkChecks1_1 compactCertificate562_chunkChecks1_2

theorem compactCertificate562_chunkChecks2_0 :
    compactCertificate562.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (867 / 2) 2 (IntervalRat.scale (867 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (25990183106 / 1000000000000) (25990183107 / 1000000000000), orderedInterval (28131489158 / 1000000000000) (28131489159 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1277256551830167 / 4000000000000) 2 (IntervalRat.scale (867 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-15029600585 / 1000000000000) (-15029600380 / 1000000000000), orderedInterval (42069020640 / 1000000000000) (42069020845 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (413038525969911 / 800000000000) 2 (IntervalRat.scale (867 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (33635190098 / 1000000000000) (33635204268 / 1000000000000), orderedInterval (-10118202686 / 1000000000000) (-10118188516 / 1000000000000)))) (orderedInterval (-13050095869 / 1000000000000) (-13050094646 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (372700276300869 / 4000000000000) 2 (IntervalRat.scale (867 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-23529712088 / 1000000000000) (-23529711645 / 1000000000000), orderedInterval (79366069318 / 1000000000000) (79366069762 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (1001125366774593 / 4000000000000) 2 (IntervalRat.scale (867 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-13022766341 / 1000000000000) (-13022766233 / 1000000000000), orderedInterval (48750019881 / 1000000000000) (48750019989 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2718250117411581 / 4000000000000) 2 (IntervalRat.scale (867 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30039421041 / 1000000000000) (30039433204 / 1000000000000), orderedInterval (-5890737039 / 1000000000000) (-5890724876 / 1000000000000)))) (orderedInterval (5391058267 / 1000000000000) (5391060479 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (2002250733550053 / 4000000000000) 2 (IntervalRat.scale (867 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-34428681902 / 1000000000000) (-34428671909 / 1000000000000), orderedInterval (9333521490 / 1000000000000) (9333531483 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3430890759208569 / 4000000000000) 2 (IntervalRat.scale (867 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-20524178103 / 1000000000000) (-20524178102 / 1000000000000), orderedInterval (-17903924493 / 1000000000000) (-17903924492 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2527178604849771 / 4000000000000) 2 (IntervalRat.scale (867 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-28568394249 / 1000000000000) (-28568394246 / 1000000000000), orderedInterval (-13815159023 / 1000000000000) (-13815159021 / 1000000000000)))) (orderedInterval (-1013124786 / 1000000000000) (-1013124710 / 1000000000000))) = true
  rfl'

theorem compactCertificate562_chunkChecks2_1 :
    compactCertificate562.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3877341872984133 / 4000000000000) 2 (IntervalRat.scale (867 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (15127014563 / 1000000000000) (15127014679 / 1000000000000), orderedInterval (-20694330671 / 1000000000000) (-20694330554 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2238584374107357 / 4000000000000) 2 (IntervalRat.scale (867 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (31762574390 / 1000000000000) (31762574396 / 1000000000000), orderedInterval (11315274459 / 1000000000000) (11315274465 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3972407255256513 / 4000000000000) 2 (IntervalRat.scale (867 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (23045601834 / 1000000000000) (23045601882 / 1000000000000), orderedInterval (10473719245 / 1000000000000) (10473719292 / 1000000000000)))) (orderedInterval (-7705555563 / 1000000000000) (-7705554660 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3711538144976997 / 4000000000000) 2 (IntervalRat.scale (867 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-24787213676 / 1000000000000) (-24787113461 / 1000000000000), orderedInterval (8480562879 / 1000000000000) (8480663094 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2648728751683701 / 4000000000000) 2 (IntervalRat.scale (867 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-2828416262 / 1000000000000) (-2828416261 / 1000000000000), orderedInterval (-30874992333 / 1000000000000) (-30874992332 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (3003376100323779 / 4000000000000) 2 (IntervalRat.scale (867 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-20655783204 / 1000000000000) (-20655783203 / 1000000000000), orderedInterval (-20509666097 / 1000000000000) (-20509666096 / 1000000000000)))) (orderedInterval (-1729045801 / 1000000000000) (-1729037364 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2503901874751251 / 4000000000000) 2 (IntervalRat.scale (867 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-31887834233 / 1000000000000) (-31887832902 / 1000000000000), orderedInterval (437891027 / 1000000000000) (437892357 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2212273242068271 / 4000000000000) 2 (IntervalRat.scale (867 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (27261154818 / 1000000000000) (27261154819 / 1000000000000), orderedInterval (20171846275 / 1000000000000) (20171846276 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (641203013042829 / 800000000000) 2 (IntervalRat.scale (867 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-26089002246 / 1000000000000) (-26089002226 / 1000000000000), orderedInterval (-10644191665 / 1000000000000) (-10644191645 / 1000000000000)))) (orderedInterval (5595184729 / 1000000000000) (5595184853 / 1000000000000))) = true
  rfl'

theorem compactCertificate562_chunkChecks2_2 :
    compactCertificate562.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1773601278742263 / 4000000000000) 2 (IntervalRat.scale (867 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-35595231632 / 1000000000000) (-35595231629 / 1000000000000), orderedInterval (-12950099594 / 1000000000000) (-12950099592 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1503501446086143 / 4000000000000) 2 (IntervalRat.scale (867 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-13362759527 / 1000000000000) (-13362759410 / 1000000000000), orderedInterval (38942535809 / 1000000000000) (38942535926 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (940821395150229 / 4000000000000) 2 (IntervalRat.scale (867 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-18850383849 / 1000000000000) (-18850383848 / 1000000000000), orderedInterval (-48450367309 / 1000000000000) (-48450367308 / 1000000000000)))) (orderedInterval (-6340803160 / 1000000000000) (-6340803058 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (505976875342443 / 4000000000000) 2 (IntervalRat.scale (867 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (70872878774 / 1000000000000) (70872878850 / 1000000000000), orderedInterval (-3409557356 / 1000000000000) (-3409557280 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1373825643076329 / 4000000000000) 2 (IntervalRat.scale (867 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-41849086731 / 1000000000000) (-41849083425 / 1000000000000), orderedInterval (10171322663 / 1000000000000) (10171325969 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1875841463653833 / 4000000000000) 2 (IntervalRat.scale (867 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-36734136661 / 1000000000000) (-36734135546 / 1000000000000), orderedInterval (2887925450 / 1000000000000) (2887926565 / 1000000000000)))) (orderedInterval (-3778289787 / 1000000000000) (-3778289593 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (793178604849771 / 4000000000000) 2 (IntervalRat.scale (867 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-51926140224 / 1000000000000) (-51926140223 / 1000000000000), orderedInterval (-22543785687 / 1000000000000) (-22543785686 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3224226992754891 / 4000000000000) 2 (IntervalRat.scale (867 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (14624986854 / 1000000000000) (14624986969 / 1000000000000), orderedInterval (-24007093872 / 1000000000000) (-24007093757 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2153634207379269 / 4000000000000) 2 (IntervalRat.scale (867 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-31528384877 / 1000000000000) (-31528337418 / 1000000000000), orderedInterval (13754132798 / 1000000000000) (13754180257 / 1000000000000)))) (orderedInterval (-4944465389 / 1000000000000) (-4944451346 / 1000000000000))) = true
  rfl'

theorem compactCertificate562_chunkChecks2 :
    compactCertificate562.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate562.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate562_chunkChecks2_0
    compactCertificate562_chunkChecks2_1 compactCertificate562_chunkChecks2_2

theorem compactCertificate562_chunkChecks3_0 :
    compactCertificate562.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (867 / 2) 3 (IntervalRat.scale (867 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (25990183106 / 1000000000000) (25990183107 / 1000000000000), orderedInterval (28131489158 / 1000000000000) (28131489159 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1277256551830167 / 4000000000000) 3 (IntervalRat.scale (867 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-15029600585 / 1000000000000) (-15029600380 / 1000000000000), orderedInterval (42069020640 / 1000000000000) (42069020845 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (413038525969911 / 800000000000) 3 (IntervalRat.scale (867 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (33635190098 / 1000000000000) (33635204268 / 1000000000000), orderedInterval (-10118202686 / 1000000000000) (-10118188516 / 1000000000000)))) (orderedInterval (-10273762133 / 1000000000000) (-10273760679 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (372700276300869 / 4000000000000) 3 (IntervalRat.scale (867 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-23529712088 / 1000000000000) (-23529711645 / 1000000000000), orderedInterval (79366069318 / 1000000000000) (79366069762 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (1001125366774593 / 4000000000000) 3 (IntervalRat.scale (867 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-13022766341 / 1000000000000) (-13022766233 / 1000000000000), orderedInterval (48750019881 / 1000000000000) (48750019989 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2718250117411581 / 4000000000000) 3 (IntervalRat.scale (867 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30039421041 / 1000000000000) (30039433204 / 1000000000000), orderedInterval (-5890737039 / 1000000000000) (-5890724876 / 1000000000000)))) (orderedInterval (-1959661748 / 1000000000000) (-1959658289 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (2002250733550053 / 4000000000000) 3 (IntervalRat.scale (867 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-34428681902 / 1000000000000) (-34428671909 / 1000000000000), orderedInterval (9333521490 / 1000000000000) (9333531483 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3430890759208569 / 4000000000000) 3 (IntervalRat.scale (867 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-20524178103 / 1000000000000) (-20524178102 / 1000000000000), orderedInterval (-17903924493 / 1000000000000) (-17903924492 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2527178604849771 / 4000000000000) 3 (IntervalRat.scale (867 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-28568394249 / 1000000000000) (-28568394246 / 1000000000000), orderedInterval (-13815159023 / 1000000000000) (-13815159021 / 1000000000000)))) (orderedInterval (-3241570432 / 1000000000000) (-3241570295 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate562_chunkChecks3_1 :
    compactCertificate562.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3877341872984133 / 4000000000000) 3 (IntervalRat.scale (867 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (15127014563 / 1000000000000) (15127014679 / 1000000000000), orderedInterval (-20694330671 / 1000000000000) (-20694330554 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2238584374107357 / 4000000000000) 3 (IntervalRat.scale (867 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (31762574390 / 1000000000000) (31762574396 / 1000000000000), orderedInterval (11315274459 / 1000000000000) (11315274465 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3972407255256513 / 4000000000000) 3 (IntervalRat.scale (867 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (23045601834 / 1000000000000) (23045601882 / 1000000000000), orderedInterval (10473719245 / 1000000000000) (10473719292 / 1000000000000)))) (orderedInterval (-60798737565 / 1000000000000) (-60798735579 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3711538144976997 / 4000000000000) 3 (IntervalRat.scale (867 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-24787213676 / 1000000000000) (-24787113461 / 1000000000000), orderedInterval (8480562879 / 1000000000000) (8480663094 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2648728751683701 / 4000000000000) 3 (IntervalRat.scale (867 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-2828416262 / 1000000000000) (-2828416261 / 1000000000000), orderedInterval (-30874992333 / 1000000000000) (-30874992332 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (3003376100323779 / 4000000000000) 3 (IntervalRat.scale (867 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-20655783204 / 1000000000000) (-20655783203 / 1000000000000), orderedInterval (-20509666097 / 1000000000000) (-20509666096 / 1000000000000)))) (orderedInterval (11372243364 / 1000000000000) (11372261361 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2503901874751251 / 4000000000000) 3 (IntervalRat.scale (867 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-31887834233 / 1000000000000) (-31887832902 / 1000000000000), orderedInterval (437891027 / 1000000000000) (437892357 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2212273242068271 / 4000000000000) 3 (IntervalRat.scale (867 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (27261154818 / 1000000000000) (27261154819 / 1000000000000), orderedInterval (20171846275 / 1000000000000) (20171846276 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (641203013042829 / 800000000000) 3 (IntervalRat.scale (867 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-26089002246 / 1000000000000) (-26089002226 / 1000000000000), orderedInterval (-10644191665 / 1000000000000) (-10644191645 / 1000000000000)))) (orderedInterval (4091645377 / 1000000000000) (4091645565 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate562_chunkChecks3_2 :
    compactCertificate562.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1773601278742263 / 4000000000000) 3 (IntervalRat.scale (867 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-35595231632 / 1000000000000) (-35595231629 / 1000000000000), orderedInterval (-12950099594 / 1000000000000) (-12950099592 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1503501446086143 / 4000000000000) 3 (IntervalRat.scale (867 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-13362759527 / 1000000000000) (-13362759410 / 1000000000000), orderedInterval (38942535809 / 1000000000000) (38942535926 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (940821395150229 / 4000000000000) 3 (IntervalRat.scale (867 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-18850383849 / 1000000000000) (-18850383848 / 1000000000000), orderedInterval (-48450367309 / 1000000000000) (-48450367308 / 1000000000000)))) (orderedInterval (-512366752 / 1000000000000) (-512366654 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (505976875342443 / 4000000000000) 3 (IntervalRat.scale (867 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (70872878774 / 1000000000000) (70872878850 / 1000000000000), orderedInterval (-3409557356 / 1000000000000) (-3409557280 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1373825643076329 / 4000000000000) 3 (IntervalRat.scale (867 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-41849086731 / 1000000000000) (-41849083425 / 1000000000000), orderedInterval (10171322663 / 1000000000000) (10171325969 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1875841463653833 / 4000000000000) 3 (IntervalRat.scale (867 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-36734136661 / 1000000000000) (-36734135546 / 1000000000000), orderedInterval (2887925450 / 1000000000000) (2887926565 / 1000000000000)))) (orderedInterval (402116943 / 1000000000000) (402117137 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (793178604849771 / 4000000000000) 3 (IntervalRat.scale (867 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-51926140224 / 1000000000000) (-51926140223 / 1000000000000), orderedInterval (-22543785687 / 1000000000000) (-22543785686 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3224226992754891 / 4000000000000) 3 (IntervalRat.scale (867 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (14624986854 / 1000000000000) (14624986969 / 1000000000000), orderedInterval (-24007093872 / 1000000000000) (-24007093757 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2153634207379269 / 4000000000000) 3 (IntervalRat.scale (867 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-31528384877 / 1000000000000) (-31528337418 / 1000000000000), orderedInterval (13754132798 / 1000000000000) (13754180257 / 1000000000000)))) (orderedInterval (-7594664985 / 1000000000000) (-7594647449 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate562_chunkChecks3 :
    compactCertificate562.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate562.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate562_chunkChecks3_0
    compactCertificate562_chunkChecks3_1 compactCertificate562_chunkChecks3_2

theorem compactCertificate562_chunkChecks4_0 :
    compactCertificate562.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (867 / 2) 4 (IntervalRat.scale (867 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (25990183106 / 1000000000000) (25990183107 / 1000000000000), orderedInterval (28131489158 / 1000000000000) (28131489159 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1277256551830167 / 4000000000000) 4 (IntervalRat.scale (867 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-15029600585 / 1000000000000) (-15029600380 / 1000000000000), orderedInterval (42069020640 / 1000000000000) (42069020845 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (413038525969911 / 800000000000) 4 (IntervalRat.scale (867 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (33635190098 / 1000000000000) (33635204268 / 1000000000000), orderedInterval (-10118202686 / 1000000000000) (-10118188516 / 1000000000000)))) (orderedInterval (14279052018 / 1000000000000) (14279053751 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (372700276300869 / 4000000000000) 4 (IntervalRat.scale (867 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-23529712088 / 1000000000000) (-23529711645 / 1000000000000), orderedInterval (79366069318 / 1000000000000) (79366069762 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (1001125366774593 / 4000000000000) 4 (IntervalRat.scale (867 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-13022766341 / 1000000000000) (-13022766233 / 1000000000000), orderedInterval (48750019881 / 1000000000000) (48750019989 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2718250117411581 / 4000000000000) 4 (IntervalRat.scale (867 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30039421041 / 1000000000000) (30039433204 / 1000000000000), orderedInterval (-5890737039 / 1000000000000) (-5890724876 / 1000000000000)))) (orderedInterval (-12939345320 / 1000000000000) (-12939339894 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (2002250733550053 / 4000000000000) 4 (IntervalRat.scale (867 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-34428681902 / 1000000000000) (-34428671909 / 1000000000000), orderedInterval (9333521490 / 1000000000000) (9333531483 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3430890759208569 / 4000000000000) 4 (IntervalRat.scale (867 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-20524178103 / 1000000000000) (-20524178102 / 1000000000000), orderedInterval (-17903924493 / 1000000000000) (-17903924492 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2527178604849771 / 4000000000000) 4 (IntervalRat.scale (867 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-28568394249 / 1000000000000) (-28568394246 / 1000000000000), orderedInterval (-13815159023 / 1000000000000) (-13815159021 / 1000000000000)))) (orderedInterval (6601975549 / 1000000000000) (6601975803 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate562_chunkChecks4_1 :
    compactCertificate562.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3877341872984133 / 4000000000000) 4 (IntervalRat.scale (867 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (15127014563 / 1000000000000) (15127014679 / 1000000000000), orderedInterval (-20694330671 / 1000000000000) (-20694330554 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2238584374107357 / 4000000000000) 4 (IntervalRat.scale (867 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (31762574390 / 1000000000000) (31762574396 / 1000000000000), orderedInterval (11315274459 / 1000000000000) (11315274465 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3972407255256513 / 4000000000000) 4 (IntervalRat.scale (867 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (23045601834 / 1000000000000) (23045601882 / 1000000000000), orderedInterval (10473719245 / 1000000000000) (10473719292 / 1000000000000)))) (orderedInterval (29854623926 / 1000000000000) (29854628345 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3711538144976997 / 4000000000000) 4 (IntervalRat.scale (867 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-24787213676 / 1000000000000) (-24787113461 / 1000000000000), orderedInterval (8480562879 / 1000000000000) (8480663094 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2648728751683701 / 4000000000000) 4 (IntervalRat.scale (867 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-2828416262 / 1000000000000) (-2828416261 / 1000000000000), orderedInterval (-30874992333 / 1000000000000) (-30874992332 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (3003376100323779 / 4000000000000) 4 (IntervalRat.scale (867 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-20655783204 / 1000000000000) (-20655783203 / 1000000000000), orderedInterval (-20509666097 / 1000000000000) (-20509666096 / 1000000000000)))) (orderedInterval (8824942818 / 1000000000000) (8824981284 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2503901874751251 / 4000000000000) 4 (IntervalRat.scale (867 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-31887834233 / 1000000000000) (-31887832902 / 1000000000000), orderedInterval (437891027 / 1000000000000) (437892357 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2212273242068271 / 4000000000000) 4 (IntervalRat.scale (867 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (27261154818 / 1000000000000) (27261154819 / 1000000000000), orderedInterval (20171846275 / 1000000000000) (20171846276 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (641203013042829 / 800000000000) 4 (IntervalRat.scale (867 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-26089002246 / 1000000000000) (-26089002226 / 1000000000000), orderedInterval (-10644191665 / 1000000000000) (-10644191645 / 1000000000000)))) (orderedInterval (-13559225707 / 1000000000000) (-13559225415 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate562_chunkChecks4_2 :
    compactCertificate562.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1773601278742263 / 4000000000000) 4 (IntervalRat.scale (867 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-35595231632 / 1000000000000) (-35595231629 / 1000000000000), orderedInterval (-12950099594 / 1000000000000) (-12950099592 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1503501446086143 / 4000000000000) 4 (IntervalRat.scale (867 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-13362759527 / 1000000000000) (-13362759410 / 1000000000000), orderedInterval (38942535809 / 1000000000000) (38942535926 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (940821395150229 / 4000000000000) 4 (IntervalRat.scale (867 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-18850383849 / 1000000000000) (-18850383848 / 1000000000000), orderedInterval (-48450367309 / 1000000000000) (-48450367308 / 1000000000000)))) (orderedInterval (6606058541 / 1000000000000) (6606058637 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (505976875342443 / 4000000000000) 4 (IntervalRat.scale (867 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (70872878774 / 1000000000000) (70872878850 / 1000000000000), orderedInterval (-3409557356 / 1000000000000) (-3409557280 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1373825643076329 / 4000000000000) 4 (IntervalRat.scale (867 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-41849086731 / 1000000000000) (-41849083425 / 1000000000000), orderedInterval (10171322663 / 1000000000000) (10171325969 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1875841463653833 / 4000000000000) 4 (IntervalRat.scale (867 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-36734136661 / 1000000000000) (-36734135546 / 1000000000000), orderedInterval (2887925450 / 1000000000000) (2887926565 / 1000000000000)))) (orderedInterval (4218473444 / 1000000000000) (4218473642 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (793178604849771 / 4000000000000) 4 (IntervalRat.scale (867 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-51926140224 / 1000000000000) (-51926140223 / 1000000000000), orderedInterval (-22543785687 / 1000000000000) (-22543785686 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3224226992754891 / 4000000000000) 4 (IntervalRat.scale (867 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (14624986854 / 1000000000000) (14624986969 / 1000000000000), orderedInterval (-24007093872 / 1000000000000) (-24007093757 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2153634207379269 / 4000000000000) 4 (IntervalRat.scale (867 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-31528384877 / 1000000000000) (-31528337418 / 1000000000000), orderedInterval (13754132798 / 1000000000000) (13754180257 / 1000000000000)))) (orderedInterval (-133452077 / 1000000000000) (-133430081 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate562_chunkChecks4 :
    compactCertificate562.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate562.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate562_chunkChecks4_0
    compactCertificate562_chunkChecks4_1 compactCertificate562_chunkChecks4_2

theorem compactCertificate562_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate562.chunkCheck r b = true :=
  compactCertificate562.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate562_chunkChecks0
    · exact compactCertificate562_chunkChecks1
    · exact compactCertificate562_chunkChecks2
    · exact compactCertificate562_chunkChecks3
    · exact compactCertificate562_chunkChecks4)

theorem compactCertificate562_coefficient0 :
    compactCertificate562.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate562_coefficient1 :
    compactCertificate562.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate562_coefficient2 :
    compactCertificate562.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate562_coefficient3 :
    compactCertificate562.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate562_coefficient4 :
    compactCertificate562.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate562_coefficients : ∀ r : Fin 5,
    compactCertificate562.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate562_coefficient0
  · exact compactCertificate562_coefficient1
  · exact compactCertificate562_coefficient2
  · exact compactCertificate562_coefficient3
  · exact compactCertificate562_coefficient4

theorem compactCertificate562_lower : (1 : ℚ) ≤ compactCertificate562.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate562, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate562_proves {t : ℝ} (ht : t ∈ compactCertificate562.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate562.proves compactCertificate562_states compactCertificate562_chunks
    compactCertificate562_coefficients compactCertificate562_lower ht

end Erdos232
