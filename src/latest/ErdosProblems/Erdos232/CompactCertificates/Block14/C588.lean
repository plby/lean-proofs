/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate588 : CompactCertificate where
  left := 459
  right := 460
  center := 919 / 2
  grid := fun i =>
    match i.val with
    | 0 => 146
    | 1 => 108
    | 2 => 174
    | 3 => 31
    | 4 => 84
    | 5 => 229
    | 6 => 169
    | 7 => 290
    | 8 => 213
    | 9 => 327
    | 10 => 189
    | 11 => 335
    | 12 => 313
    | 13 => 224
    | 14 => 253
    | 15 => 211
    | 16 => 187
    | 17 => 271
    | 18 => 150
    | 19 => 127
    | 20 => 79
    | 21 => 43
    | 22 => 116
    | 23 => 158
    | 24 => 67
    | 25 => 272
    | _ => 182
  point := fun i =>
    match i.val with
    | 0 => 919 / 2
    | 1 => 1353862481121019 / 4000000000000
    | 2 => 437811309534427 / 800000000000
    | 3 => 395053695410033 / 4000000000000
    | 4 => 1061169794770301 / 4000000000000
    | 5 => 2881282419724617 / 4000000000000
    | 6 => 2122339589541521 / 4000000000000
    | 7 => 3636665060798933 / 4000000000000
    | 8 => 2678751024056447 / 4000000000000
    | 9 => 4109892942644081 / 4000000000000
    | 10 => 2372847796775849 / 4000000000000
    | 11 => 4210660054879741 / 4000000000000
    | 12 => 3934144815725329 / 4000000000000
    | 13 => 2807591375775457 / 4000000000000
    | 14 => 3183509384310903 / 4000000000000
    | 15 => 2654078227100807 / 4000000000000
    | 16 => 2344958603760947 / 4000000000000
    | 17 => 679660402521753 / 800000000000
    | 18 => 1879976441942491 / 4000000000000
    | 19 => 1593676850003651 / 4000000000000
    | 20 => 997248975943553 / 4000000000000
    | 21 => 536323815962751 / 4000000000000
    | 22 => 1456223490181253 / 4000000000000
    | 23 => 1988348679466981 / 4000000000000
    | 24 => 840751024056447 / 4000000000000
    | 25 => 3417606235688287 / 4000000000000
    | _ => 2282802579678833 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (37189266174 / 1000000000000) (37189266860 / 1000000000000), orderedInterval (-1595974256 / 1000000000000) (-1595973570 / 1000000000000))
    | 1 => (orderedInterval (-1793133187 / 1000000000000) (-1793133185 / 1000000000000), orderedInterval (43334924291 / 1000000000000) (43334924293 / 1000000000000))
    | 2 => (orderedInterval (33678715449 / 1000000000000) (33678715537 / 1000000000000), orderedInterval (5356310865 / 1000000000000) (5356310953 / 1000000000000))
    | 3 => (orderedInterval (-66829276467 / 1000000000000) (-66829244837 / 1000000000000), orderedInterval (44832396501 / 1000000000000) (44832428131 / 1000000000000))
    | 4 => (orderedInterval (40073087528 / 1000000000000) (40073170088 / 1000000000000), orderedInterval (-28250613463 / 1000000000000) (-28250530902 / 1000000000000))
    | 5 => (orderedInterval (-29548074216 / 1000000000000) (-29548067695 / 1000000000000), orderedInterval (3293407220 / 1000000000000) (3293413741 / 1000000000000))
    | 6 => (orderedInterval (-14782267895 / 1000000000000) (-14782267894 / 1000000000000), orderedInterval (-31312259392 / 1000000000000) (-31312259391 / 1000000000000))
    | 7 => (orderedInterval (-23705803619 / 1000000000000) (-23705768877 / 1000000000000), orderedInterval (11771391961 / 1000000000000) (11771426703 / 1000000000000))
    | 8 => (orderedInterval (-29819024730 / 1000000000000) (-29819024678 / 1000000000000), orderedInterval (-7816570977 / 1000000000000) (-7816570926 / 1000000000000))
    | 9 => (orderedInterval (-20358399428 / 1000000000000) (-20358399424 / 1000000000000), orderedInterval (-14312556956 / 1000000000000) (-14312556952 / 1000000000000))
    | 10 => (orderedInterval (-7663620712 / 1000000000000) (-7663620711 / 1000000000000), orderedInterval (-31843869925 / 1000000000000) (-31843869924 / 1000000000000))
    | 11 => (orderedInterval (-20913207129 / 1000000000000) (-20913207118 / 1000000000000), orderedInterval (-12928664302 / 1000000000000) (-12928664291 / 1000000000000))
    | 12 => (orderedInterval (-21449182025 / 1000000000000) (-21449182020 / 1000000000000), orderedInterval (-13671528215 / 1000000000000) (-13671528210 / 1000000000000))
    | 13 => (orderedInterval (-25875822396 / 1000000000000) (-25875777555 / 1000000000000), orderedInterval (15427517572 / 1000000000000) (15427562413 / 1000000000000))
    | 14 => (orderedInterval (-27266479200 / 1000000000000) (-27266436239 / 1000000000000), orderedInterval (7529561469 / 1000000000000) (7529604430 / 1000000000000))
    | 15 => (orderedInterval (-30663013716 / 1000000000000) (-30663013470 / 1000000000000), orderedInterval (-4363039985 / 1000000000000) (-4363039738 / 1000000000000))
    | 16 => (orderedInterval (14422332364 / 1000000000000) (14422332509 / 1000000000000), orderedInterval (-29642257391 / 1000000000000) (-29642257246 / 1000000000000))
    | 17 => (orderedInterval (23193645406 / 1000000000000) (23193663662 / 1000000000000), orderedInterval (-14553019075 / 1000000000000) (-14553000818 / 1000000000000))
    | 18 => (orderedInterval (-16327650788 / 1000000000000) (-16327650441 / 1000000000000), orderedInterval (33001235879 / 1000000000000) (33001236226 / 1000000000000))
    | 19 => (orderedInterval (-8802521962 / 1000000000000) (-8802521961 / 1000000000000), orderedInterval (-38981015009 / 1000000000000) (-38981015008 / 1000000000000))
    | 20 => (orderedInterval (-47630577288 / 1000000000000) (-47630571307 / 1000000000000), orderedInterval (16972375385 / 1000000000000) (16972381366 / 1000000000000))
    | 21 => (orderedInterval (15243240468 / 1000000000000) (15243240611 / 1000000000000), orderedInterval (-67255791919 / 1000000000000) (-67255791776 / 1000000000000))
    | 22 => (orderedInterval (16905434874 / 1000000000000) (16905434875 / 1000000000000), orderedInterval (38224584198 / 1000000000000) (38224584199 / 1000000000000))
    | 23 => (orderedInterval (35698926303 / 1000000000000) (35698926513 / 1000000000000), orderedInterval (2471377635 / 1000000000000) (2471377844 / 1000000000000))
    | 24 => (orderedInterval (-25699043628 / 1000000000000) (-25699043627 / 1000000000000), orderedInterval (-48604858248 / 1000000000000) (-48604858247 / 1000000000000))
    | 25 => (orderedInterval (17027930407 / 1000000000000) (17027930408 / 1000000000000), orderedInterval (21324412744 / 1000000000000) (21324412745 / 1000000000000))
    | _ => (orderedInterval (-9359618701 / 1000000000000) (-9359618687 / 1000000000000), orderedInterval (32069134445 / 1000000000000) (32069134458 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (16700120104 / 1000000000000) (16700120414 / 1000000000000)
      | 1 => orderedInterval (4288749815 / 1000000000000) (4288753691 / 1000000000000)
      | 2 => orderedInterval (10513751 / 1000000000000) (10514850 / 1000000000000)
      | 3 => orderedInterval (76694834 / 1000000000000) (76695019 / 1000000000000)
      | 4 => orderedInterval (-1921684153 / 1000000000000) (-1921679640 / 1000000000000)
      | 5 => orderedInterval (-585579613 / 1000000000000) (-585579090 / 1000000000000)
      | 6 => orderedInterval (1558263848 / 1000000000000) (1558264213 / 1000000000000)
      | 7 => orderedInterval (-3400924905 / 1000000000000) (-3400924831 / 1000000000000)
      | _ => orderedInterval (215086626 / 1000000000000) (215086757 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (39195248 / 1000000000000) (39195562 / 1000000000000)
      | 1 => orderedInterval (-1067092782 / 1000000000000) (-1067090178 / 1000000000000)
      | 2 => orderedInterval (-993709762 / 1000000000000) (-993707595 / 1000000000000)
      | 3 => orderedInterval (-1569632776 / 1000000000000) (-1569632393 / 1000000000000)
      | 4 => orderedInterval (2690753981 / 1000000000000) (2690760924 / 1000000000000)
      | 5 => orderedInterval (1402524912 / 1000000000000) (1402525855 / 1000000000000)
      | 6 => orderedInterval (-3184323837 / 1000000000000) (-3184323567 / 1000000000000)
      | 7 => orderedInterval (-529585622 / 1000000000000) (-529585554 / 1000000000000)
      | _ => orderedInterval (-10834847553 / 1000000000000) (-10834847371 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-17534891199 / 1000000000000) (-17534890878 / 1000000000000)
      | 1 => orderedInterval (-5680865255 / 1000000000000) (-5680863003 / 1000000000000)
      | 2 => orderedInterval (-1329543453 / 1000000000000) (-1329539170 / 1000000000000)
      | 3 => orderedInterval (-1534917586 / 1000000000000) (-1534916765 / 1000000000000)
      | 4 => orderedInterval (3515521899 / 1000000000000) (3515532608 / 1000000000000)
      | 5 => orderedInterval (48632401 / 1000000000000) (48634115 / 1000000000000)
      | 6 => orderedInterval (-2642433291 / 1000000000000) (-2642433073 / 1000000000000)
      | 7 => orderedInterval (3467698470 / 1000000000000) (3467698538 / 1000000000000)
      | _ => orderedInterval (2139416286 / 1000000000000) (2139416554 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-21636502 / 1000000000000) (-21636173 / 1000000000000)
      | 1 => orderedInterval (1117625235 / 1000000000000) (1117627739 / 1000000000000)
      | 2 => orderedInterval (3400069519 / 1000000000000) (3400077978 / 1000000000000)
      | 3 => orderedInterval (-1256642925 / 1000000000000) (-1256641125 / 1000000000000)
      | 4 => orderedInterval (-7429779220 / 1000000000000) (-7429762704 / 1000000000000)
      | 5 => orderedInterval (-1016026362 / 1000000000000) (-1016023233 / 1000000000000)
      | 6 => orderedInterval (4125727226 / 1000000000000) (4125727416 / 1000000000000)
      | 7 => orderedInterval (632670175 / 1000000000000) (632670247 / 1000000000000)
      | _ => orderedInterval (22710623413 / 1000000000000) (22710623825 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (18712106124 / 1000000000000) (18712106464 / 1000000000000)
      | 1 => orderedInterval (12844408625 / 1000000000000) (12844411970 / 1000000000000)
      | 2 => orderedInterval (7939845061 / 1000000000000) (7939861794 / 1000000000000)
      | 3 => orderedInterval (6979280753 / 1000000000000) (6979284750 / 1000000000000)
      | 4 => orderedInterval (-3919798006 / 1000000000000) (-3919772459 / 1000000000000)
      | 5 => orderedInterval (3217914688 / 1000000000000) (3217920429 / 1000000000000)
      | 6 => orderedInterval (2986708591 / 1000000000000) (2986708766 / 1000000000000)
      | 7 => orderedInterval (-3902976169 / 1000000000000) (-3902976093 / 1000000000000)
      | _ => orderedInterval (-12496107690 / 1000000000000) (-12496107029 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (16941240307 / 1000000000000) (16941251383 / 1000000000000)
    | 1 => orderedInterval (-14046718191 / 1000000000000) (-14046704317 / 1000000000000)
    | 2 => orderedInterval (-19551381728 / 1000000000000) (-19551361074 / 1000000000000)
    | 3 => orderedInterval (22262630559 / 1000000000000) (22262663970 / 1000000000000)
    | _ => orderedInterval (32361381977 / 1000000000000) (32361438592 / 1000000000000)

theorem compactCertificate588_stateChecks0 :
    compactCertificate588.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 146 12 (919 / 2)) (orderedInterval (37189266174 / 1000000000000) (37189266860 / 1000000000000), orderedInterval (-1595974256 / 1000000000000) (-1595973570 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 108 12 (1353862481121019 / 4000000000000)) (orderedInterval (-1793133187 / 1000000000000) (-1793133185 / 1000000000000), orderedInterval (43334924291 / 1000000000000) (43334924293 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 174 12 (437811309534427 / 800000000000)) (orderedInterval (33678715449 / 1000000000000) (33678715537 / 1000000000000), orderedInterval (5356310865 / 1000000000000) (5356310953 / 1000000000000))) = true
  rfl'

theorem compactCertificate588_stateChecks1 :
    compactCertificate588.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 31 12 (395053695410033 / 4000000000000)) (orderedInterval (-66829276467 / 1000000000000) (-66829244837 / 1000000000000), orderedInterval (44832396501 / 1000000000000) (44832428131 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 84 12 (1061169794770301 / 4000000000000)) (orderedInterval (40073087528 / 1000000000000) (40073170088 / 1000000000000), orderedInterval (-28250613463 / 1000000000000) (-28250530902 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 229 12 (2881282419724617 / 4000000000000)) (orderedInterval (-29548074216 / 1000000000000) (-29548067695 / 1000000000000), orderedInterval (3293407220 / 1000000000000) (3293413741 / 1000000000000))) = true
  rfl'

theorem compactCertificate588_stateChecks2 :
    compactCertificate588.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 169 12 (2122339589541521 / 4000000000000)) (orderedInterval (-14782267895 / 1000000000000) (-14782267894 / 1000000000000), orderedInterval (-31312259392 / 1000000000000) (-31312259391 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 290 12 (3636665060798933 / 4000000000000)) (orderedInterval (-23705803619 / 1000000000000) (-23705768877 / 1000000000000), orderedInterval (11771391961 / 1000000000000) (11771426703 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 213 12 (2678751024056447 / 4000000000000)) (orderedInterval (-29819024730 / 1000000000000) (-29819024678 / 1000000000000), orderedInterval (-7816570977 / 1000000000000) (-7816570926 / 1000000000000))) = true
  rfl'

theorem compactCertificate588_stateChecks3 :
    compactCertificate588.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 327 12 (4109892942644081 / 4000000000000)) (orderedInterval (-20358399428 / 1000000000000) (-20358399424 / 1000000000000), orderedInterval (-14312556956 / 1000000000000) (-14312556952 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 189 12 (2372847796775849 / 4000000000000)) (orderedInterval (-7663620712 / 1000000000000) (-7663620711 / 1000000000000), orderedInterval (-31843869925 / 1000000000000) (-31843869924 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 335 12 (4210660054879741 / 4000000000000)) (orderedInterval (-20913207129 / 1000000000000) (-20913207118 / 1000000000000), orderedInterval (-12928664302 / 1000000000000) (-12928664291 / 1000000000000))) = true
  rfl'

theorem compactCertificate588_stateChecks4 :
    compactCertificate588.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 313 12 (3934144815725329 / 4000000000000)) (orderedInterval (-21449182025 / 1000000000000) (-21449182020 / 1000000000000), orderedInterval (-13671528215 / 1000000000000) (-13671528210 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 224 12 (2807591375775457 / 4000000000000)) (orderedInterval (-25875822396 / 1000000000000) (-25875777555 / 1000000000000), orderedInterval (15427517572 / 1000000000000) (15427562413 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 253 12 (3183509384310903 / 4000000000000)) (orderedInterval (-27266479200 / 1000000000000) (-27266436239 / 1000000000000), orderedInterval (7529561469 / 1000000000000) (7529604430 / 1000000000000))) = true
  rfl'

theorem compactCertificate588_stateChecks5 :
    compactCertificate588.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 211 12 (2654078227100807 / 4000000000000)) (orderedInterval (-30663013716 / 1000000000000) (-30663013470 / 1000000000000), orderedInterval (-4363039985 / 1000000000000) (-4363039738 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 187 12 (2344958603760947 / 4000000000000)) (orderedInterval (14422332364 / 1000000000000) (14422332509 / 1000000000000), orderedInterval (-29642257391 / 1000000000000) (-29642257246 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 271 12 (679660402521753 / 800000000000)) (orderedInterval (23193645406 / 1000000000000) (23193663662 / 1000000000000), orderedInterval (-14553019075 / 1000000000000) (-14553000818 / 1000000000000))) = true
  rfl'

theorem compactCertificate588_stateChecks6 :
    compactCertificate588.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 150 12 (1879976441942491 / 4000000000000)) (orderedInterval (-16327650788 / 1000000000000) (-16327650441 / 1000000000000), orderedInterval (33001235879 / 1000000000000) (33001236226 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 127 12 (1593676850003651 / 4000000000000)) (orderedInterval (-8802521962 / 1000000000000) (-8802521961 / 1000000000000), orderedInterval (-38981015009 / 1000000000000) (-38981015008 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 79 12 (997248975943553 / 4000000000000)) (orderedInterval (-47630577288 / 1000000000000) (-47630571307 / 1000000000000), orderedInterval (16972375385 / 1000000000000) (16972381366 / 1000000000000))) = true
  rfl'

theorem compactCertificate588_stateChecks7 :
    compactCertificate588.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (536323815962751 / 4000000000000)) (orderedInterval (15243240468 / 1000000000000) (15243240611 / 1000000000000), orderedInterval (-67255791919 / 1000000000000) (-67255791776 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 116 12 (1456223490181253 / 4000000000000)) (orderedInterval (16905434874 / 1000000000000) (16905434875 / 1000000000000), orderedInterval (38224584198 / 1000000000000) (38224584199 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 158 12 (1988348679466981 / 4000000000000)) (orderedInterval (35698926303 / 1000000000000) (35698926513 / 1000000000000), orderedInterval (2471377635 / 1000000000000) (2471377844 / 1000000000000))) = true
  rfl'

theorem compactCertificate588_stateChecks8 :
    compactCertificate588.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (840751024056447 / 4000000000000)) (orderedInterval (-25699043628 / 1000000000000) (-25699043627 / 1000000000000), orderedInterval (-48604858248 / 1000000000000) (-48604858247 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 272 12 (3417606235688287 / 4000000000000)) (orderedInterval (17027930407 / 1000000000000) (17027930408 / 1000000000000), orderedInterval (21324412744 / 1000000000000) (21324412745 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 182 12 (2282802579678833 / 4000000000000)) (orderedInterval (-9359618701 / 1000000000000) (-9359618687 / 1000000000000), orderedInterval (32069134445 / 1000000000000) (32069134458 / 1000000000000))) = true
  rfl'

theorem compactCertificate588_states : ∀ j,
    BesselStateValid (compactCertificate588.point j) (compactCertificate588.state j) :=
  compactCertificate588.statesValid_of_checks3 compactCertificate588_stateChecks0
    compactCertificate588_stateChecks1 compactCertificate588_stateChecks2
    compactCertificate588_stateChecks3 compactCertificate588_stateChecks4
    compactCertificate588_stateChecks5 compactCertificate588_stateChecks6
    compactCertificate588_stateChecks7 compactCertificate588_stateChecks8

theorem compactCertificate588_chunkChecks0_0 :
    compactCertificate588.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (919 / 2) 0 (IntervalRat.scale (919 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (37189266174 / 1000000000000) (37189266860 / 1000000000000), orderedInterval (-1595974256 / 1000000000000) (-1595973570 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1353862481121019 / 4000000000000) 0 (IntervalRat.scale (919 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-1793133187 / 1000000000000) (-1793133185 / 1000000000000), orderedInterval (43334924291 / 1000000000000) (43334924293 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (437811309534427 / 800000000000) 0 (IntervalRat.scale (919 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (33678715449 / 1000000000000) (33678715537 / 1000000000000), orderedInterval (5356310865 / 1000000000000) (5356310953 / 1000000000000)))) (orderedInterval (16700120104 / 1000000000000) (16700120414 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (395053695410033 / 4000000000000) 0 (IntervalRat.scale (919 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-66829276467 / 1000000000000) (-66829244837 / 1000000000000), orderedInterval (44832396501 / 1000000000000) (44832428131 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (1061169794770301 / 4000000000000) 0 (IntervalRat.scale (919 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (40073087528 / 1000000000000) (40073170088 / 1000000000000), orderedInterval (-28250613463 / 1000000000000) (-28250530902 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2881282419724617 / 4000000000000) 0 (IntervalRat.scale (919 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29548074216 / 1000000000000) (-29548067695 / 1000000000000), orderedInterval (3293407220 / 1000000000000) (3293413741 / 1000000000000)))) (orderedInterval (4288749815 / 1000000000000) (4288753691 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (2122339589541521 / 4000000000000) 0 (IntervalRat.scale (919 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-14782267895 / 1000000000000) (-14782267894 / 1000000000000), orderedInterval (-31312259392 / 1000000000000) (-31312259391 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3636665060798933 / 4000000000000) 0 (IntervalRat.scale (919 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-23705803619 / 1000000000000) (-23705768877 / 1000000000000), orderedInterval (11771391961 / 1000000000000) (11771426703 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2678751024056447 / 4000000000000) 0 (IntervalRat.scale (919 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-29819024730 / 1000000000000) (-29819024678 / 1000000000000), orderedInterval (-7816570977 / 1000000000000) (-7816570926 / 1000000000000)))) (orderedInterval (10513751 / 1000000000000) (10514850 / 1000000000000))) = true
  rfl'

theorem compactCertificate588_chunkChecks0_1 :
    compactCertificate588.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (4109892942644081 / 4000000000000) 0 (IntervalRat.scale (919 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-20358399428 / 1000000000000) (-20358399424 / 1000000000000), orderedInterval (-14312556956 / 1000000000000) (-14312556952 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2372847796775849 / 4000000000000) 0 (IntervalRat.scale (919 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-7663620712 / 1000000000000) (-7663620711 / 1000000000000), orderedInterval (-31843869925 / 1000000000000) (-31843869924 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (4210660054879741 / 4000000000000) 0 (IntervalRat.scale (919 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-20913207129 / 1000000000000) (-20913207118 / 1000000000000), orderedInterval (-12928664302 / 1000000000000) (-12928664291 / 1000000000000)))) (orderedInterval (76694834 / 1000000000000) (76695019 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3934144815725329 / 4000000000000) 0 (IntervalRat.scale (919 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-21449182025 / 1000000000000) (-21449182020 / 1000000000000), orderedInterval (-13671528215 / 1000000000000) (-13671528210 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2807591375775457 / 4000000000000) 0 (IntervalRat.scale (919 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-25875822396 / 1000000000000) (-25875777555 / 1000000000000), orderedInterval (15427517572 / 1000000000000) (15427562413 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (3183509384310903 / 4000000000000) 0 (IntervalRat.scale (919 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-27266479200 / 1000000000000) (-27266436239 / 1000000000000), orderedInterval (7529561469 / 1000000000000) (7529604430 / 1000000000000)))) (orderedInterval (-1921684153 / 1000000000000) (-1921679640 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2654078227100807 / 4000000000000) 0 (IntervalRat.scale (919 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-30663013716 / 1000000000000) (-30663013470 / 1000000000000), orderedInterval (-4363039985 / 1000000000000) (-4363039738 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2344958603760947 / 4000000000000) 0 (IntervalRat.scale (919 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (14422332364 / 1000000000000) (14422332509 / 1000000000000), orderedInterval (-29642257391 / 1000000000000) (-29642257246 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (679660402521753 / 800000000000) 0 (IntervalRat.scale (919 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (23193645406 / 1000000000000) (23193663662 / 1000000000000), orderedInterval (-14553019075 / 1000000000000) (-14553000818 / 1000000000000)))) (orderedInterval (-585579613 / 1000000000000) (-585579090 / 1000000000000))) = true
  rfl'

theorem compactCertificate588_chunkChecks0_2 :
    compactCertificate588.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1879976441942491 / 4000000000000) 0 (IntervalRat.scale (919 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-16327650788 / 1000000000000) (-16327650441 / 1000000000000), orderedInterval (33001235879 / 1000000000000) (33001236226 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1593676850003651 / 4000000000000) 0 (IntervalRat.scale (919 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-8802521962 / 1000000000000) (-8802521961 / 1000000000000), orderedInterval (-38981015009 / 1000000000000) (-38981015008 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (997248975943553 / 4000000000000) 0 (IntervalRat.scale (919 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-47630577288 / 1000000000000) (-47630571307 / 1000000000000), orderedInterval (16972375385 / 1000000000000) (16972381366 / 1000000000000)))) (orderedInterval (1558263848 / 1000000000000) (1558264213 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (536323815962751 / 4000000000000) 0 (IntervalRat.scale (919 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (15243240468 / 1000000000000) (15243240611 / 1000000000000), orderedInterval (-67255791919 / 1000000000000) (-67255791776 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1456223490181253 / 4000000000000) 0 (IntervalRat.scale (919 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (16905434874 / 1000000000000) (16905434875 / 1000000000000), orderedInterval (38224584198 / 1000000000000) (38224584199 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1988348679466981 / 4000000000000) 0 (IntervalRat.scale (919 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (35698926303 / 1000000000000) (35698926513 / 1000000000000), orderedInterval (2471377635 / 1000000000000) (2471377844 / 1000000000000)))) (orderedInterval (-3400924905 / 1000000000000) (-3400924831 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (840751024056447 / 4000000000000) 0 (IntervalRat.scale (919 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-25699043628 / 1000000000000) (-25699043627 / 1000000000000), orderedInterval (-48604858248 / 1000000000000) (-48604858247 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3417606235688287 / 4000000000000) 0 (IntervalRat.scale (919 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (17027930407 / 1000000000000) (17027930408 / 1000000000000), orderedInterval (21324412744 / 1000000000000) (21324412745 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2282802579678833 / 4000000000000) 0 (IntervalRat.scale (919 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-9359618701 / 1000000000000) (-9359618687 / 1000000000000), orderedInterval (32069134445 / 1000000000000) (32069134458 / 1000000000000)))) (orderedInterval (215086626 / 1000000000000) (215086757 / 1000000000000))) = true
  rfl'

theorem compactCertificate588_chunkChecks0 :
    compactCertificate588.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate588.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate588_chunkChecks0_0
    compactCertificate588_chunkChecks0_1 compactCertificate588_chunkChecks0_2

theorem compactCertificate588_chunkChecks1_0 :
    compactCertificate588.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (919 / 2) 1 (IntervalRat.scale (919 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (37189266174 / 1000000000000) (37189266860 / 1000000000000), orderedInterval (-1595974256 / 1000000000000) (-1595973570 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1353862481121019 / 4000000000000) 1 (IntervalRat.scale (919 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-1793133187 / 1000000000000) (-1793133185 / 1000000000000), orderedInterval (43334924291 / 1000000000000) (43334924293 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (437811309534427 / 800000000000) 1 (IntervalRat.scale (919 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (33678715449 / 1000000000000) (33678715537 / 1000000000000), orderedInterval (5356310865 / 1000000000000) (5356310953 / 1000000000000)))) (orderedInterval (39195248 / 1000000000000) (39195562 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (395053695410033 / 4000000000000) 1 (IntervalRat.scale (919 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-66829276467 / 1000000000000) (-66829244837 / 1000000000000), orderedInterval (44832396501 / 1000000000000) (44832428131 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (1061169794770301 / 4000000000000) 1 (IntervalRat.scale (919 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (40073087528 / 1000000000000) (40073170088 / 1000000000000), orderedInterval (-28250613463 / 1000000000000) (-28250530902 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2881282419724617 / 4000000000000) 1 (IntervalRat.scale (919 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29548074216 / 1000000000000) (-29548067695 / 1000000000000), orderedInterval (3293407220 / 1000000000000) (3293413741 / 1000000000000)))) (orderedInterval (-1067092782 / 1000000000000) (-1067090178 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (2122339589541521 / 4000000000000) 1 (IntervalRat.scale (919 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-14782267895 / 1000000000000) (-14782267894 / 1000000000000), orderedInterval (-31312259392 / 1000000000000) (-31312259391 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3636665060798933 / 4000000000000) 1 (IntervalRat.scale (919 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-23705803619 / 1000000000000) (-23705768877 / 1000000000000), orderedInterval (11771391961 / 1000000000000) (11771426703 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2678751024056447 / 4000000000000) 1 (IntervalRat.scale (919 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-29819024730 / 1000000000000) (-29819024678 / 1000000000000), orderedInterval (-7816570977 / 1000000000000) (-7816570926 / 1000000000000)))) (orderedInterval (-993709762 / 1000000000000) (-993707595 / 1000000000000))) = true
  rfl'

theorem compactCertificate588_chunkChecks1_1 :
    compactCertificate588.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (4109892942644081 / 4000000000000) 1 (IntervalRat.scale (919 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-20358399428 / 1000000000000) (-20358399424 / 1000000000000), orderedInterval (-14312556956 / 1000000000000) (-14312556952 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2372847796775849 / 4000000000000) 1 (IntervalRat.scale (919 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-7663620712 / 1000000000000) (-7663620711 / 1000000000000), orderedInterval (-31843869925 / 1000000000000) (-31843869924 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (4210660054879741 / 4000000000000) 1 (IntervalRat.scale (919 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-20913207129 / 1000000000000) (-20913207118 / 1000000000000), orderedInterval (-12928664302 / 1000000000000) (-12928664291 / 1000000000000)))) (orderedInterval (-1569632776 / 1000000000000) (-1569632393 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3934144815725329 / 4000000000000) 1 (IntervalRat.scale (919 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-21449182025 / 1000000000000) (-21449182020 / 1000000000000), orderedInterval (-13671528215 / 1000000000000) (-13671528210 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2807591375775457 / 4000000000000) 1 (IntervalRat.scale (919 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-25875822396 / 1000000000000) (-25875777555 / 1000000000000), orderedInterval (15427517572 / 1000000000000) (15427562413 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (3183509384310903 / 4000000000000) 1 (IntervalRat.scale (919 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-27266479200 / 1000000000000) (-27266436239 / 1000000000000), orderedInterval (7529561469 / 1000000000000) (7529604430 / 1000000000000)))) (orderedInterval (2690753981 / 1000000000000) (2690760924 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2654078227100807 / 4000000000000) 1 (IntervalRat.scale (919 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-30663013716 / 1000000000000) (-30663013470 / 1000000000000), orderedInterval (-4363039985 / 1000000000000) (-4363039738 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2344958603760947 / 4000000000000) 1 (IntervalRat.scale (919 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (14422332364 / 1000000000000) (14422332509 / 1000000000000), orderedInterval (-29642257391 / 1000000000000) (-29642257246 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (679660402521753 / 800000000000) 1 (IntervalRat.scale (919 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (23193645406 / 1000000000000) (23193663662 / 1000000000000), orderedInterval (-14553019075 / 1000000000000) (-14553000818 / 1000000000000)))) (orderedInterval (1402524912 / 1000000000000) (1402525855 / 1000000000000))) = true
  rfl'

theorem compactCertificate588_chunkChecks1_2 :
    compactCertificate588.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1879976441942491 / 4000000000000) 1 (IntervalRat.scale (919 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-16327650788 / 1000000000000) (-16327650441 / 1000000000000), orderedInterval (33001235879 / 1000000000000) (33001236226 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1593676850003651 / 4000000000000) 1 (IntervalRat.scale (919 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-8802521962 / 1000000000000) (-8802521961 / 1000000000000), orderedInterval (-38981015009 / 1000000000000) (-38981015008 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (997248975943553 / 4000000000000) 1 (IntervalRat.scale (919 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-47630577288 / 1000000000000) (-47630571307 / 1000000000000), orderedInterval (16972375385 / 1000000000000) (16972381366 / 1000000000000)))) (orderedInterval (-3184323837 / 1000000000000) (-3184323567 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (536323815962751 / 4000000000000) 1 (IntervalRat.scale (919 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (15243240468 / 1000000000000) (15243240611 / 1000000000000), orderedInterval (-67255791919 / 1000000000000) (-67255791776 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1456223490181253 / 4000000000000) 1 (IntervalRat.scale (919 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (16905434874 / 1000000000000) (16905434875 / 1000000000000), orderedInterval (38224584198 / 1000000000000) (38224584199 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1988348679466981 / 4000000000000) 1 (IntervalRat.scale (919 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (35698926303 / 1000000000000) (35698926513 / 1000000000000), orderedInterval (2471377635 / 1000000000000) (2471377844 / 1000000000000)))) (orderedInterval (-529585622 / 1000000000000) (-529585554 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (840751024056447 / 4000000000000) 1 (IntervalRat.scale (919 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-25699043628 / 1000000000000) (-25699043627 / 1000000000000), orderedInterval (-48604858248 / 1000000000000) (-48604858247 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3417606235688287 / 4000000000000) 1 (IntervalRat.scale (919 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (17027930407 / 1000000000000) (17027930408 / 1000000000000), orderedInterval (21324412744 / 1000000000000) (21324412745 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2282802579678833 / 4000000000000) 1 (IntervalRat.scale (919 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-9359618701 / 1000000000000) (-9359618687 / 1000000000000), orderedInterval (32069134445 / 1000000000000) (32069134458 / 1000000000000)))) (orderedInterval (-10834847553 / 1000000000000) (-10834847371 / 1000000000000))) = true
  rfl'

theorem compactCertificate588_chunkChecks1 :
    compactCertificate588.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate588.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate588_chunkChecks1_0
    compactCertificate588_chunkChecks1_1 compactCertificate588_chunkChecks1_2

theorem compactCertificate588_chunkChecks2_0 :
    compactCertificate588.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (919 / 2) 2 (IntervalRat.scale (919 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (37189266174 / 1000000000000) (37189266860 / 1000000000000), orderedInterval (-1595974256 / 1000000000000) (-1595973570 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1353862481121019 / 4000000000000) 2 (IntervalRat.scale (919 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-1793133187 / 1000000000000) (-1793133185 / 1000000000000), orderedInterval (43334924291 / 1000000000000) (43334924293 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (437811309534427 / 800000000000) 2 (IntervalRat.scale (919 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (33678715449 / 1000000000000) (33678715537 / 1000000000000), orderedInterval (5356310865 / 1000000000000) (5356310953 / 1000000000000)))) (orderedInterval (-17534891199 / 1000000000000) (-17534890878 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (395053695410033 / 4000000000000) 2 (IntervalRat.scale (919 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-66829276467 / 1000000000000) (-66829244837 / 1000000000000), orderedInterval (44832396501 / 1000000000000) (44832428131 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (1061169794770301 / 4000000000000) 2 (IntervalRat.scale (919 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (40073087528 / 1000000000000) (40073170088 / 1000000000000), orderedInterval (-28250613463 / 1000000000000) (-28250530902 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2881282419724617 / 4000000000000) 2 (IntervalRat.scale (919 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29548074216 / 1000000000000) (-29548067695 / 1000000000000), orderedInterval (3293407220 / 1000000000000) (3293413741 / 1000000000000)))) (orderedInterval (-5680865255 / 1000000000000) (-5680863003 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (2122339589541521 / 4000000000000) 2 (IntervalRat.scale (919 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-14782267895 / 1000000000000) (-14782267894 / 1000000000000), orderedInterval (-31312259392 / 1000000000000) (-31312259391 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3636665060798933 / 4000000000000) 2 (IntervalRat.scale (919 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-23705803619 / 1000000000000) (-23705768877 / 1000000000000), orderedInterval (11771391961 / 1000000000000) (11771426703 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2678751024056447 / 4000000000000) 2 (IntervalRat.scale (919 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-29819024730 / 1000000000000) (-29819024678 / 1000000000000), orderedInterval (-7816570977 / 1000000000000) (-7816570926 / 1000000000000)))) (orderedInterval (-1329543453 / 1000000000000) (-1329539170 / 1000000000000))) = true
  rfl'

theorem compactCertificate588_chunkChecks2_1 :
    compactCertificate588.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (4109892942644081 / 4000000000000) 2 (IntervalRat.scale (919 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-20358399428 / 1000000000000) (-20358399424 / 1000000000000), orderedInterval (-14312556956 / 1000000000000) (-14312556952 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2372847796775849 / 4000000000000) 2 (IntervalRat.scale (919 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-7663620712 / 1000000000000) (-7663620711 / 1000000000000), orderedInterval (-31843869925 / 1000000000000) (-31843869924 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (4210660054879741 / 4000000000000) 2 (IntervalRat.scale (919 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-20913207129 / 1000000000000) (-20913207118 / 1000000000000), orderedInterval (-12928664302 / 1000000000000) (-12928664291 / 1000000000000)))) (orderedInterval (-1534917586 / 1000000000000) (-1534916765 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3934144815725329 / 4000000000000) 2 (IntervalRat.scale (919 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-21449182025 / 1000000000000) (-21449182020 / 1000000000000), orderedInterval (-13671528215 / 1000000000000) (-13671528210 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2807591375775457 / 4000000000000) 2 (IntervalRat.scale (919 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-25875822396 / 1000000000000) (-25875777555 / 1000000000000), orderedInterval (15427517572 / 1000000000000) (15427562413 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (3183509384310903 / 4000000000000) 2 (IntervalRat.scale (919 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-27266479200 / 1000000000000) (-27266436239 / 1000000000000), orderedInterval (7529561469 / 1000000000000) (7529604430 / 1000000000000)))) (orderedInterval (3515521899 / 1000000000000) (3515532608 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2654078227100807 / 4000000000000) 2 (IntervalRat.scale (919 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-30663013716 / 1000000000000) (-30663013470 / 1000000000000), orderedInterval (-4363039985 / 1000000000000) (-4363039738 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2344958603760947 / 4000000000000) 2 (IntervalRat.scale (919 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (14422332364 / 1000000000000) (14422332509 / 1000000000000), orderedInterval (-29642257391 / 1000000000000) (-29642257246 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (679660402521753 / 800000000000) 2 (IntervalRat.scale (919 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (23193645406 / 1000000000000) (23193663662 / 1000000000000), orderedInterval (-14553019075 / 1000000000000) (-14553000818 / 1000000000000)))) (orderedInterval (48632401 / 1000000000000) (48634115 / 1000000000000))) = true
  rfl'

theorem compactCertificate588_chunkChecks2_2 :
    compactCertificate588.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1879976441942491 / 4000000000000) 2 (IntervalRat.scale (919 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-16327650788 / 1000000000000) (-16327650441 / 1000000000000), orderedInterval (33001235879 / 1000000000000) (33001236226 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1593676850003651 / 4000000000000) 2 (IntervalRat.scale (919 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-8802521962 / 1000000000000) (-8802521961 / 1000000000000), orderedInterval (-38981015009 / 1000000000000) (-38981015008 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (997248975943553 / 4000000000000) 2 (IntervalRat.scale (919 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-47630577288 / 1000000000000) (-47630571307 / 1000000000000), orderedInterval (16972375385 / 1000000000000) (16972381366 / 1000000000000)))) (orderedInterval (-2642433291 / 1000000000000) (-2642433073 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (536323815962751 / 4000000000000) 2 (IntervalRat.scale (919 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (15243240468 / 1000000000000) (15243240611 / 1000000000000), orderedInterval (-67255791919 / 1000000000000) (-67255791776 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1456223490181253 / 4000000000000) 2 (IntervalRat.scale (919 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (16905434874 / 1000000000000) (16905434875 / 1000000000000), orderedInterval (38224584198 / 1000000000000) (38224584199 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1988348679466981 / 4000000000000) 2 (IntervalRat.scale (919 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (35698926303 / 1000000000000) (35698926513 / 1000000000000), orderedInterval (2471377635 / 1000000000000) (2471377844 / 1000000000000)))) (orderedInterval (3467698470 / 1000000000000) (3467698538 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (840751024056447 / 4000000000000) 2 (IntervalRat.scale (919 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-25699043628 / 1000000000000) (-25699043627 / 1000000000000), orderedInterval (-48604858248 / 1000000000000) (-48604858247 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3417606235688287 / 4000000000000) 2 (IntervalRat.scale (919 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (17027930407 / 1000000000000) (17027930408 / 1000000000000), orderedInterval (21324412744 / 1000000000000) (21324412745 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2282802579678833 / 4000000000000) 2 (IntervalRat.scale (919 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-9359618701 / 1000000000000) (-9359618687 / 1000000000000), orderedInterval (32069134445 / 1000000000000) (32069134458 / 1000000000000)))) (orderedInterval (2139416286 / 1000000000000) (2139416554 / 1000000000000))) = true
  rfl'

theorem compactCertificate588_chunkChecks2 :
    compactCertificate588.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate588.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate588_chunkChecks2_0
    compactCertificate588_chunkChecks2_1 compactCertificate588_chunkChecks2_2

theorem compactCertificate588_chunkChecks3_0 :
    compactCertificate588.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (919 / 2) 3 (IntervalRat.scale (919 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (37189266174 / 1000000000000) (37189266860 / 1000000000000), orderedInterval (-1595974256 / 1000000000000) (-1595973570 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1353862481121019 / 4000000000000) 3 (IntervalRat.scale (919 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-1793133187 / 1000000000000) (-1793133185 / 1000000000000), orderedInterval (43334924291 / 1000000000000) (43334924293 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (437811309534427 / 800000000000) 3 (IntervalRat.scale (919 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (33678715449 / 1000000000000) (33678715537 / 1000000000000), orderedInterval (5356310865 / 1000000000000) (5356310953 / 1000000000000)))) (orderedInterval (-21636502 / 1000000000000) (-21636173 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (395053695410033 / 4000000000000) 3 (IntervalRat.scale (919 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-66829276467 / 1000000000000) (-66829244837 / 1000000000000), orderedInterval (44832396501 / 1000000000000) (44832428131 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (1061169794770301 / 4000000000000) 3 (IntervalRat.scale (919 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (40073087528 / 1000000000000) (40073170088 / 1000000000000), orderedInterval (-28250613463 / 1000000000000) (-28250530902 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2881282419724617 / 4000000000000) 3 (IntervalRat.scale (919 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29548074216 / 1000000000000) (-29548067695 / 1000000000000), orderedInterval (3293407220 / 1000000000000) (3293413741 / 1000000000000)))) (orderedInterval (1117625235 / 1000000000000) (1117627739 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (2122339589541521 / 4000000000000) 3 (IntervalRat.scale (919 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-14782267895 / 1000000000000) (-14782267894 / 1000000000000), orderedInterval (-31312259392 / 1000000000000) (-31312259391 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3636665060798933 / 4000000000000) 3 (IntervalRat.scale (919 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-23705803619 / 1000000000000) (-23705768877 / 1000000000000), orderedInterval (11771391961 / 1000000000000) (11771426703 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2678751024056447 / 4000000000000) 3 (IntervalRat.scale (919 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-29819024730 / 1000000000000) (-29819024678 / 1000000000000), orderedInterval (-7816570977 / 1000000000000) (-7816570926 / 1000000000000)))) (orderedInterval (3400069519 / 1000000000000) (3400077978 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate588_chunkChecks3_1 :
    compactCertificate588.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (4109892942644081 / 4000000000000) 3 (IntervalRat.scale (919 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-20358399428 / 1000000000000) (-20358399424 / 1000000000000), orderedInterval (-14312556956 / 1000000000000) (-14312556952 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2372847796775849 / 4000000000000) 3 (IntervalRat.scale (919 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-7663620712 / 1000000000000) (-7663620711 / 1000000000000), orderedInterval (-31843869925 / 1000000000000) (-31843869924 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (4210660054879741 / 4000000000000) 3 (IntervalRat.scale (919 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-20913207129 / 1000000000000) (-20913207118 / 1000000000000), orderedInterval (-12928664302 / 1000000000000) (-12928664291 / 1000000000000)))) (orderedInterval (-1256642925 / 1000000000000) (-1256641125 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3934144815725329 / 4000000000000) 3 (IntervalRat.scale (919 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-21449182025 / 1000000000000) (-21449182020 / 1000000000000), orderedInterval (-13671528215 / 1000000000000) (-13671528210 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2807591375775457 / 4000000000000) 3 (IntervalRat.scale (919 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-25875822396 / 1000000000000) (-25875777555 / 1000000000000), orderedInterval (15427517572 / 1000000000000) (15427562413 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (3183509384310903 / 4000000000000) 3 (IntervalRat.scale (919 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-27266479200 / 1000000000000) (-27266436239 / 1000000000000), orderedInterval (7529561469 / 1000000000000) (7529604430 / 1000000000000)))) (orderedInterval (-7429779220 / 1000000000000) (-7429762704 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2654078227100807 / 4000000000000) 3 (IntervalRat.scale (919 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-30663013716 / 1000000000000) (-30663013470 / 1000000000000), orderedInterval (-4363039985 / 1000000000000) (-4363039738 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2344958603760947 / 4000000000000) 3 (IntervalRat.scale (919 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (14422332364 / 1000000000000) (14422332509 / 1000000000000), orderedInterval (-29642257391 / 1000000000000) (-29642257246 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (679660402521753 / 800000000000) 3 (IntervalRat.scale (919 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (23193645406 / 1000000000000) (23193663662 / 1000000000000), orderedInterval (-14553019075 / 1000000000000) (-14553000818 / 1000000000000)))) (orderedInterval (-1016026362 / 1000000000000) (-1016023233 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate588_chunkChecks3_2 :
    compactCertificate588.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1879976441942491 / 4000000000000) 3 (IntervalRat.scale (919 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-16327650788 / 1000000000000) (-16327650441 / 1000000000000), orderedInterval (33001235879 / 1000000000000) (33001236226 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1593676850003651 / 4000000000000) 3 (IntervalRat.scale (919 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-8802521962 / 1000000000000) (-8802521961 / 1000000000000), orderedInterval (-38981015009 / 1000000000000) (-38981015008 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (997248975943553 / 4000000000000) 3 (IntervalRat.scale (919 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-47630577288 / 1000000000000) (-47630571307 / 1000000000000), orderedInterval (16972375385 / 1000000000000) (16972381366 / 1000000000000)))) (orderedInterval (4125727226 / 1000000000000) (4125727416 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (536323815962751 / 4000000000000) 3 (IntervalRat.scale (919 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (15243240468 / 1000000000000) (15243240611 / 1000000000000), orderedInterval (-67255791919 / 1000000000000) (-67255791776 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1456223490181253 / 4000000000000) 3 (IntervalRat.scale (919 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (16905434874 / 1000000000000) (16905434875 / 1000000000000), orderedInterval (38224584198 / 1000000000000) (38224584199 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1988348679466981 / 4000000000000) 3 (IntervalRat.scale (919 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (35698926303 / 1000000000000) (35698926513 / 1000000000000), orderedInterval (2471377635 / 1000000000000) (2471377844 / 1000000000000)))) (orderedInterval (632670175 / 1000000000000) (632670247 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (840751024056447 / 4000000000000) 3 (IntervalRat.scale (919 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-25699043628 / 1000000000000) (-25699043627 / 1000000000000), orderedInterval (-48604858248 / 1000000000000) (-48604858247 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3417606235688287 / 4000000000000) 3 (IntervalRat.scale (919 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (17027930407 / 1000000000000) (17027930408 / 1000000000000), orderedInterval (21324412744 / 1000000000000) (21324412745 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2282802579678833 / 4000000000000) 3 (IntervalRat.scale (919 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-9359618701 / 1000000000000) (-9359618687 / 1000000000000), orderedInterval (32069134445 / 1000000000000) (32069134458 / 1000000000000)))) (orderedInterval (22710623413 / 1000000000000) (22710623825 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate588_chunkChecks3 :
    compactCertificate588.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate588.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate588_chunkChecks3_0
    compactCertificate588_chunkChecks3_1 compactCertificate588_chunkChecks3_2

theorem compactCertificate588_chunkChecks4_0 :
    compactCertificate588.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (919 / 2) 4 (IntervalRat.scale (919 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (37189266174 / 1000000000000) (37189266860 / 1000000000000), orderedInterval (-1595974256 / 1000000000000) (-1595973570 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1353862481121019 / 4000000000000) 4 (IntervalRat.scale (919 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-1793133187 / 1000000000000) (-1793133185 / 1000000000000), orderedInterval (43334924291 / 1000000000000) (43334924293 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (437811309534427 / 800000000000) 4 (IntervalRat.scale (919 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (33678715449 / 1000000000000) (33678715537 / 1000000000000), orderedInterval (5356310865 / 1000000000000) (5356310953 / 1000000000000)))) (orderedInterval (18712106124 / 1000000000000) (18712106464 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (395053695410033 / 4000000000000) 4 (IntervalRat.scale (919 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-66829276467 / 1000000000000) (-66829244837 / 1000000000000), orderedInterval (44832396501 / 1000000000000) (44832428131 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (1061169794770301 / 4000000000000) 4 (IntervalRat.scale (919 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (40073087528 / 1000000000000) (40073170088 / 1000000000000), orderedInterval (-28250613463 / 1000000000000) (-28250530902 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2881282419724617 / 4000000000000) 4 (IntervalRat.scale (919 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29548074216 / 1000000000000) (-29548067695 / 1000000000000), orderedInterval (3293407220 / 1000000000000) (3293413741 / 1000000000000)))) (orderedInterval (12844408625 / 1000000000000) (12844411970 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (2122339589541521 / 4000000000000) 4 (IntervalRat.scale (919 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-14782267895 / 1000000000000) (-14782267894 / 1000000000000), orderedInterval (-31312259392 / 1000000000000) (-31312259391 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3636665060798933 / 4000000000000) 4 (IntervalRat.scale (919 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-23705803619 / 1000000000000) (-23705768877 / 1000000000000), orderedInterval (11771391961 / 1000000000000) (11771426703 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2678751024056447 / 4000000000000) 4 (IntervalRat.scale (919 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-29819024730 / 1000000000000) (-29819024678 / 1000000000000), orderedInterval (-7816570977 / 1000000000000) (-7816570926 / 1000000000000)))) (orderedInterval (7939845061 / 1000000000000) (7939861794 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate588_chunkChecks4_1 :
    compactCertificate588.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (4109892942644081 / 4000000000000) 4 (IntervalRat.scale (919 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-20358399428 / 1000000000000) (-20358399424 / 1000000000000), orderedInterval (-14312556956 / 1000000000000) (-14312556952 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2372847796775849 / 4000000000000) 4 (IntervalRat.scale (919 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-7663620712 / 1000000000000) (-7663620711 / 1000000000000), orderedInterval (-31843869925 / 1000000000000) (-31843869924 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (4210660054879741 / 4000000000000) 4 (IntervalRat.scale (919 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-20913207129 / 1000000000000) (-20913207118 / 1000000000000), orderedInterval (-12928664302 / 1000000000000) (-12928664291 / 1000000000000)))) (orderedInterval (6979280753 / 1000000000000) (6979284750 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3934144815725329 / 4000000000000) 4 (IntervalRat.scale (919 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-21449182025 / 1000000000000) (-21449182020 / 1000000000000), orderedInterval (-13671528215 / 1000000000000) (-13671528210 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2807591375775457 / 4000000000000) 4 (IntervalRat.scale (919 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-25875822396 / 1000000000000) (-25875777555 / 1000000000000), orderedInterval (15427517572 / 1000000000000) (15427562413 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (3183509384310903 / 4000000000000) 4 (IntervalRat.scale (919 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-27266479200 / 1000000000000) (-27266436239 / 1000000000000), orderedInterval (7529561469 / 1000000000000) (7529604430 / 1000000000000)))) (orderedInterval (-3919798006 / 1000000000000) (-3919772459 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2654078227100807 / 4000000000000) 4 (IntervalRat.scale (919 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-30663013716 / 1000000000000) (-30663013470 / 1000000000000), orderedInterval (-4363039985 / 1000000000000) (-4363039738 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2344958603760947 / 4000000000000) 4 (IntervalRat.scale (919 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (14422332364 / 1000000000000) (14422332509 / 1000000000000), orderedInterval (-29642257391 / 1000000000000) (-29642257246 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (679660402521753 / 800000000000) 4 (IntervalRat.scale (919 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (23193645406 / 1000000000000) (23193663662 / 1000000000000), orderedInterval (-14553019075 / 1000000000000) (-14553000818 / 1000000000000)))) (orderedInterval (3217914688 / 1000000000000) (3217920429 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate588_chunkChecks4_2 :
    compactCertificate588.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1879976441942491 / 4000000000000) 4 (IntervalRat.scale (919 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-16327650788 / 1000000000000) (-16327650441 / 1000000000000), orderedInterval (33001235879 / 1000000000000) (33001236226 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1593676850003651 / 4000000000000) 4 (IntervalRat.scale (919 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-8802521962 / 1000000000000) (-8802521961 / 1000000000000), orderedInterval (-38981015009 / 1000000000000) (-38981015008 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (997248975943553 / 4000000000000) 4 (IntervalRat.scale (919 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-47630577288 / 1000000000000) (-47630571307 / 1000000000000), orderedInterval (16972375385 / 1000000000000) (16972381366 / 1000000000000)))) (orderedInterval (2986708591 / 1000000000000) (2986708766 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (536323815962751 / 4000000000000) 4 (IntervalRat.scale (919 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (15243240468 / 1000000000000) (15243240611 / 1000000000000), orderedInterval (-67255791919 / 1000000000000) (-67255791776 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1456223490181253 / 4000000000000) 4 (IntervalRat.scale (919 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (16905434874 / 1000000000000) (16905434875 / 1000000000000), orderedInterval (38224584198 / 1000000000000) (38224584199 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1988348679466981 / 4000000000000) 4 (IntervalRat.scale (919 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (35698926303 / 1000000000000) (35698926513 / 1000000000000), orderedInterval (2471377635 / 1000000000000) (2471377844 / 1000000000000)))) (orderedInterval (-3902976169 / 1000000000000) (-3902976093 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (840751024056447 / 4000000000000) 4 (IntervalRat.scale (919 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-25699043628 / 1000000000000) (-25699043627 / 1000000000000), orderedInterval (-48604858248 / 1000000000000) (-48604858247 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3417606235688287 / 4000000000000) 4 (IntervalRat.scale (919 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (17027930407 / 1000000000000) (17027930408 / 1000000000000), orderedInterval (21324412744 / 1000000000000) (21324412745 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2282802579678833 / 4000000000000) 4 (IntervalRat.scale (919 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-9359618701 / 1000000000000) (-9359618687 / 1000000000000), orderedInterval (32069134445 / 1000000000000) (32069134458 / 1000000000000)))) (orderedInterval (-12496107690 / 1000000000000) (-12496107029 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate588_chunkChecks4 :
    compactCertificate588.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate588.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate588_chunkChecks4_0
    compactCertificate588_chunkChecks4_1 compactCertificate588_chunkChecks4_2

theorem compactCertificate588_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate588.chunkCheck r b = true :=
  compactCertificate588.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate588_chunkChecks0
    · exact compactCertificate588_chunkChecks1
    · exact compactCertificate588_chunkChecks2
    · exact compactCertificate588_chunkChecks3
    · exact compactCertificate588_chunkChecks4)

theorem compactCertificate588_coefficient0 :
    compactCertificate588.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate588_coefficient1 :
    compactCertificate588.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate588_coefficient2 :
    compactCertificate588.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate588_coefficient3 :
    compactCertificate588.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate588_coefficient4 :
    compactCertificate588.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate588_coefficients : ∀ r : Fin 5,
    compactCertificate588.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate588_coefficient0
  · exact compactCertificate588_coefficient1
  · exact compactCertificate588_coefficient2
  · exact compactCertificate588_coefficient3
  · exact compactCertificate588_coefficient4

theorem compactCertificate588_lower : (1 : ℚ) ≤ compactCertificate588.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate588, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate588_proves {t : ℝ} (ht : t ∈ compactCertificate588.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate588.proves compactCertificate588_states compactCertificate588_chunks
    compactCertificate588_coefficients compactCertificate588_lower ht

end Erdos232
