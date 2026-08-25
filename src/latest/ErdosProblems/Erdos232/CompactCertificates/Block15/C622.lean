/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate622 : CompactCertificate where
  left := 493
  right := 494
  center := 987 / 2
  grid := fun i =>
    match i.val with
    | 0 => 157
    | 1 => 116
    | 2 => 187
    | 3 => 34
    | 4 => 91
    | 5 => 246
    | 6 => 181
    | 7 => 311
    | 8 => 229
    | 9 => 351
    | 10 => 203
    | 11 => 360
    | 12 => 336
    | 13 => 240
    | 14 => 272
    | 15 => 227
    | 16 => 201
    | 17 => 291
    | 18 => 161
    | 19 => 136
    | 20 => 85
    | 21 => 46
    | 22 => 125
    | 23 => 170
    | 24 => 72
    | 25 => 292
    | _ => 195
  point := fun i =>
    match i.val with
    | 0 => 987 / 2
    | 1 => 1454039465578287 / 4000000000000
    | 2 => 470206488041871 / 800000000000
    | 3 => 424285089629709 / 4000000000000
    | 4 => 1139689431380073 / 4000000000000
    | 5 => 3094478507364741 / 4000000000000
    | 6 => 2279378862761133 / 4000000000000
    | 7 => 3905754532109409 / 4000000000000
    | 8 => 2876961110711331 / 4000000000000
    | 9 => 4413998187584013 / 4000000000000
    | 10 => 2548423041803877 / 4000000000000
    | 11 => 4522221408233193 / 4000000000000
    | 12 => 4225245846703917 / 4000000000000
    | 13 => 3015334807280061 / 4000000000000
    | 14 => 3419068294140219 / 4000000000000
    | 15 => 2850462687865611 / 4000000000000
    | 16 => 2518470230589831 / 4000000000000
    | 17 => 729950834917269 / 800000000000
    | 18 => 2019082424588943 / 4000000000000
    | 19 => 1711598532049623 / 4000000000000
    | 20 => 1071038889288669 / 4000000000000
    | 21 => 576008276773923 / 4000000000000
    | 22 => 1563974521010769 / 4000000000000
    | 23 => 2135473500145713 / 4000000000000
    | 24 => 902961110711331 / 4000000000000
    | 25 => 3670486784139651 / 4000000000000
    | _ => 2451715066532109 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-31245681998 / 1000000000000) (-31245681997 / 1000000000000), orderedInterval (-17680392008 / 1000000000000) (-17680392007 / 1000000000000))
    | 1 => (orderedInterval (-5417844084 / 1000000000000) (-5417844077 / 1000000000000), orderedInterval (41503984081 / 1000000000000) (41503984088 / 1000000000000))
    | 2 => (orderedInterval (-28797631591 / 1000000000000) (-28797631590 / 1000000000000), orderedInterval (-15907497339 / 1000000000000) (-15907497338 / 1000000000000))
    | 3 => (orderedInterval (3201887004 / 1000000000000) (3201887007 / 1000000000000), orderedInterval (77390499847 / 1000000000000) (77390499851 / 1000000000000))
    | 4 => (orderedInterval (8351572605 / 1000000000000) (8351572629 / 1000000000000), orderedInterval (-46540097826 / 1000000000000) (-46540097801 / 1000000000000))
    | 5 => (orderedInterval (28686339366 / 1000000000000) (28686342118 / 1000000000000), orderedInterval (-83783640 / 1000000000000) (-83780888 / 1000000000000))
    | 6 => (orderedInterval (-30369987617 / 1000000000000) (-30369922504 / 1000000000000), orderedInterval (13985362219 / 1000000000000) (13985427332 / 1000000000000))
    | 7 => (orderedInterval (-4786896430 / 1000000000000) (-4786896429 / 1000000000000), orderedInterval (-25078757824 / 1000000000000) (-25078757823 / 1000000000000))
    | 8 => (orderedInterval (-16817988840 / 1000000000000) (-16817988839 / 1000000000000), orderedInterval (-24529771739 / 1000000000000) (-24529771738 / 1000000000000))
    | 9 => (orderedInterval (-24016248132 / 1000000000000) (-24016230718 / 1000000000000), orderedInterval (371481152 / 1000000000000) (371498566 / 1000000000000))
    | 10 => (orderedInterval (-4650498050 / 1000000000000) (-4650498049 / 1000000000000), orderedInterval (-31263111502 / 1000000000000) (-31263111501 / 1000000000000))
    | 11 => (orderedInterval (8520950670 / 1000000000000) (8520950671 / 1000000000000), orderedInterval (22143398970 / 1000000000000) (22143398971 / 1000000000000))
    | 12 => (orderedInterval (24519884361 / 1000000000000) (24519891652 / 1000000000000), orderedInterval (1195409446 / 1000000000000) (1195416736 / 1000000000000))
    | 13 => (orderedInterval (17277686490 / 1000000000000) (17277686491 / 1000000000000), orderedInterval (23354994070 / 1000000000000) (23354994071 / 1000000000000))
    | 14 => (orderedInterval (23523578509 / 1000000000000) (23523578513 / 1000000000000), orderedInterval (13822013069 / 1000000000000) (13822013072 / 1000000000000))
    | 15 => (orderedInterval (-7665477605 / 1000000000000) (-7665477604 / 1000000000000), orderedInterval (-28884014900 / 1000000000000) (-28884014899 / 1000000000000))
    | 16 => (orderedInterval (27698193013 / 1000000000000) (27698268833 / 1000000000000), orderedInterval (-15640265023 / 1000000000000) (-15640189203 / 1000000000000))
    | 17 => (orderedInterval (21931914386 / 1000000000000) (21931924257 / 1000000000000), orderedInterval (-14732871144 / 1000000000000) (-14732861273 / 1000000000000))
    | 18 => (orderedInterval (8464425881 / 1000000000000) (8464425892 / 1000000000000), orderedInterval (-34498385185 / 1000000000000) (-34498385173 / 1000000000000))
    | 19 => (orderedInterval (38179887529 / 1000000000000) (38179887575 / 1000000000000), orderedInterval (5439315601 / 1000000000000) (5439315647 / 1000000000000))
    | 20 => (orderedInterval (-48668139882 / 1000000000000) (-48668139836 / 1000000000000), orderedInterval (-2906885735 / 1000000000000) (-2906885689 / 1000000000000))
    | 21 => (orderedInterval (17948649669 / 1000000000000) (17948649670 / 1000000000000), orderedInterval (63959362635 / 1000000000000) (63959362636 / 1000000000000))
    | 22 => (orderedInterval (32112456975 / 1000000000000) (32112523024 / 1000000000000), orderedInterval (-24474632761 / 1000000000000) (-24474566712 / 1000000000000))
    | 23 => (orderedInterval (19004867839 / 1000000000000) (19004867840 / 1000000000000), orderedInterval (28814144763 / 1000000000000) (28814144764 / 1000000000000))
    | 24 => (orderedInterval (17230947732 / 1000000000000) (17230947733 / 1000000000000), orderedInterval (50193722000 / 1000000000000) (50193722001 / 1000000000000))
    | 25 => (orderedInterval (23001906785 / 1000000000000) (23001906792 / 1000000000000), orderedInterval (12820382099 / 1000000000000) (12820382106 / 1000000000000))
    | _ => (orderedInterval (-28771379970 / 1000000000000) (-28771379968 / 1000000000000), orderedInterval (-14497535938 / 1000000000000) (-14497535937 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-14125056191 / 1000000000000) (-14125056156 / 1000000000000)
      | 1 => orderedInterval (-1769109499 / 1000000000000) (-1769109243 / 1000000000000)
      | 2 => orderedInterval (-258810584 / 1000000000000) (-258810556 / 1000000000000)
      | 3 => orderedInterval (5134133836 / 1000000000000) (5134137125 / 1000000000000)
      | 4 => orderedInterval (1072124953 / 1000000000000) (1072125144 / 1000000000000)
      | 5 => orderedInterval (-1112054674 / 1000000000000) (-1112050035 / 1000000000000)
      | 6 => orderedInterval (-5098782228 / 1000000000000) (-5098782098 / 1000000000000)
      | 7 => orderedInterval (-2516467920 / 1000000000000) (-2516466362 / 1000000000000)
      | _ => orderedInterval (3629751749 / 1000000000000) (3629751887 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-7834782160 / 1000000000000) (-7834782121 / 1000000000000)
      | 1 => orderedInterval (-1152199486 / 1000000000000) (-1152199111 / 1000000000000)
      | 2 => orderedInterval (666488654 / 1000000000000) (666488702 / 1000000000000)
      | 3 => orderedInterval (4073318281 / 1000000000000) (4073325605 / 1000000000000)
      | 4 => orderedInterval (3206217305 / 1000000000000) (3206217682 / 1000000000000)
      | 5 => orderedInterval (-37178140 / 1000000000000) (-37172069 / 1000000000000)
      | 6 => orderedInterval (5323719720 / 1000000000000) (5323719840 / 1000000000000)
      | 7 => orderedInterval (-2293621058 / 1000000000000) (-2293619817 / 1000000000000)
      | _ => orderedInterval (1576321953 / 1000000000000) (1576322147 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (14825018038 / 1000000000000) (14825018083 / 1000000000000)
      | 1 => orderedInterval (4913730984 / 1000000000000) (4913731559 / 1000000000000)
      | 2 => orderedInterval (283986868 / 1000000000000) (283986954 / 1000000000000)
      | 3 => orderedInterval (-27128115388 / 1000000000000) (-27128099033 / 1000000000000)
      | 4 => orderedInterval (-1433578578 / 1000000000000) (-1433577816 / 1000000000000)
      | 5 => orderedInterval (845080053 / 1000000000000) (845088094 / 1000000000000)
      | 6 => orderedInterval (3496211074 / 1000000000000) (3496211187 / 1000000000000)
      | 7 => orderedInterval (2194722662 / 1000000000000) (2194723659 / 1000000000000)
      | _ => orderedInterval (-1878487125 / 1000000000000) (-1878486839 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (8400265161 / 1000000000000) (8400265213 / 1000000000000)
      | 1 => orderedInterval (302453375 / 1000000000000) (302454269 / 1000000000000)
      | 2 => orderedInterval (-4157023633 / 1000000000000) (-4157023477 / 1000000000000)
      | 3 => orderedInterval (-32069333613 / 1000000000000) (-32069297081 / 1000000000000)
      | 4 => orderedInterval (-7293638527 / 1000000000000) (-7293636967 / 1000000000000)
      | 5 => orderedInterval (1528065583 / 1000000000000) (1528076364 / 1000000000000)
      | 6 => orderedInterval (-5693912725 / 1000000000000) (-5693912614 / 1000000000000)
      | 7 => orderedInterval (2544475008 / 1000000000000) (2544475810 / 1000000000000)
      | _ => orderedInterval (1472523146 / 1000000000000) (1472523587 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-15833713446 / 1000000000000) (-15833713385 / 1000000000000)
      | 1 => orderedInterval (-12282635928 / 1000000000000) (-12282634528 / 1000000000000)
      | 2 => orderedInterval (445853947 / 1000000000000) (445854236 / 1000000000000)
      | 3 => orderedInterval (139221088056 / 1000000000000) (139221169784 / 1000000000000)
      | 4 => orderedInterval (-1438124742 / 1000000000000) (-1438121508 / 1000000000000)
      | 5 => orderedInterval (1971527397 / 1000000000000) (1971542138 / 1000000000000)
      | 6 => orderedInterval (-2816986433 / 1000000000000) (-2816986325 / 1000000000000)
      | 7 => orderedInterval (-2294582449 / 1000000000000) (-2294581798 / 1000000000000)
      | _ => orderedInterval (-9538319250 / 1000000000000) (-9538318540 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-15044270558 / 1000000000000) (-15044260294 / 1000000000000)
    | 1 => orderedInterval (3528285069 / 1000000000000) (3528300858 / 1000000000000)
    | 2 => orderedInterval (-3881431412 / 1000000000000) (-3881404152 / 1000000000000)
    | 3 => orderedInterval (-34966126225 / 1000000000000) (-34966074896 / 1000000000000)
    | _ => orderedInterval (97434107152 / 1000000000000) (97434210074 / 1000000000000)

theorem compactCertificate622_stateChecks0 :
    compactCertificate622.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 157 12 (987 / 2)) (orderedInterval (-31245681998 / 1000000000000) (-31245681997 / 1000000000000), orderedInterval (-17680392008 / 1000000000000) (-17680392007 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 116 12 (1454039465578287 / 4000000000000)) (orderedInterval (-5417844084 / 1000000000000) (-5417844077 / 1000000000000), orderedInterval (41503984081 / 1000000000000) (41503984088 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 187 12 (470206488041871 / 800000000000)) (orderedInterval (-28797631591 / 1000000000000) (-28797631590 / 1000000000000), orderedInterval (-15907497339 / 1000000000000) (-15907497338 / 1000000000000))) = true
  rfl'

theorem compactCertificate622_stateChecks1 :
    compactCertificate622.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (424285089629709 / 4000000000000)) (orderedInterval (3201887004 / 1000000000000) (3201887007 / 1000000000000), orderedInterval (77390499847 / 1000000000000) (77390499851 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 91 12 (1139689431380073 / 4000000000000)) (orderedInterval (8351572605 / 1000000000000) (8351572629 / 1000000000000), orderedInterval (-46540097826 / 1000000000000) (-46540097801 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 246 12 (3094478507364741 / 4000000000000)) (orderedInterval (28686339366 / 1000000000000) (28686342118 / 1000000000000), orderedInterval (-83783640 / 1000000000000) (-83780888 / 1000000000000))) = true
  rfl'

theorem compactCertificate622_stateChecks2 :
    compactCertificate622.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 181 12 (2279378862761133 / 4000000000000)) (orderedInterval (-30369987617 / 1000000000000) (-30369922504 / 1000000000000), orderedInterval (13985362219 / 1000000000000) (13985427332 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 311 12 (3905754532109409 / 4000000000000)) (orderedInterval (-4786896430 / 1000000000000) (-4786896429 / 1000000000000), orderedInterval (-25078757824 / 1000000000000) (-25078757823 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 229 12 (2876961110711331 / 4000000000000)) (orderedInterval (-16817988840 / 1000000000000) (-16817988839 / 1000000000000), orderedInterval (-24529771739 / 1000000000000) (-24529771738 / 1000000000000))) = true
  rfl'

theorem compactCertificate622_stateChecks3 :
    compactCertificate622.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 351 12 (4413998187584013 / 4000000000000)) (orderedInterval (-24016248132 / 1000000000000) (-24016230718 / 1000000000000), orderedInterval (371481152 / 1000000000000) (371498566 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 203 12 (2548423041803877 / 4000000000000)) (orderedInterval (-4650498050 / 1000000000000) (-4650498049 / 1000000000000), orderedInterval (-31263111502 / 1000000000000) (-31263111501 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 360 12 (4522221408233193 / 4000000000000)) (orderedInterval (8520950670 / 1000000000000) (8520950671 / 1000000000000), orderedInterval (22143398970 / 1000000000000) (22143398971 / 1000000000000))) = true
  rfl'

theorem compactCertificate622_stateChecks4 :
    compactCertificate622.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 336 12 (4225245846703917 / 4000000000000)) (orderedInterval (24519884361 / 1000000000000) (24519891652 / 1000000000000), orderedInterval (1195409446 / 1000000000000) (1195416736 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 240 12 (3015334807280061 / 4000000000000)) (orderedInterval (17277686490 / 1000000000000) (17277686491 / 1000000000000), orderedInterval (23354994070 / 1000000000000) (23354994071 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 272 12 (3419068294140219 / 4000000000000)) (orderedInterval (23523578509 / 1000000000000) (23523578513 / 1000000000000), orderedInterval (13822013069 / 1000000000000) (13822013072 / 1000000000000))) = true
  rfl'

theorem compactCertificate622_stateChecks5 :
    compactCertificate622.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 227 12 (2850462687865611 / 4000000000000)) (orderedInterval (-7665477605 / 1000000000000) (-7665477604 / 1000000000000), orderedInterval (-28884014900 / 1000000000000) (-28884014899 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 201 12 (2518470230589831 / 4000000000000)) (orderedInterval (27698193013 / 1000000000000) (27698268833 / 1000000000000), orderedInterval (-15640265023 / 1000000000000) (-15640189203 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 291 12 (729950834917269 / 800000000000)) (orderedInterval (21931914386 / 1000000000000) (21931924257 / 1000000000000), orderedInterval (-14732871144 / 1000000000000) (-14732861273 / 1000000000000))) = true
  rfl'

theorem compactCertificate622_stateChecks6 :
    compactCertificate622.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 161 12 (2019082424588943 / 4000000000000)) (orderedInterval (8464425881 / 1000000000000) (8464425892 / 1000000000000), orderedInterval (-34498385185 / 1000000000000) (-34498385173 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 136 12 (1711598532049623 / 4000000000000)) (orderedInterval (38179887529 / 1000000000000) (38179887575 / 1000000000000), orderedInterval (5439315601 / 1000000000000) (5439315647 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 85 12 (1071038889288669 / 4000000000000)) (orderedInterval (-48668139882 / 1000000000000) (-48668139836 / 1000000000000), orderedInterval (-2906885735 / 1000000000000) (-2906885689 / 1000000000000))) = true
  rfl'

theorem compactCertificate622_stateChecks7 :
    compactCertificate622.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (576008276773923 / 4000000000000)) (orderedInterval (17948649669 / 1000000000000) (17948649670 / 1000000000000), orderedInterval (63959362635 / 1000000000000) (63959362636 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 125 12 (1563974521010769 / 4000000000000)) (orderedInterval (32112456975 / 1000000000000) (32112523024 / 1000000000000), orderedInterval (-24474632761 / 1000000000000) (-24474566712 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 170 12 (2135473500145713 / 4000000000000)) (orderedInterval (19004867839 / 1000000000000) (19004867840 / 1000000000000), orderedInterval (28814144763 / 1000000000000) (28814144764 / 1000000000000))) = true
  rfl'

theorem compactCertificate622_stateChecks8 :
    compactCertificate622.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 72 12 (902961110711331 / 4000000000000)) (orderedInterval (17230947732 / 1000000000000) (17230947733 / 1000000000000), orderedInterval (50193722000 / 1000000000000) (50193722001 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 292 12 (3670486784139651 / 4000000000000)) (orderedInterval (23001906785 / 1000000000000) (23001906792 / 1000000000000), orderedInterval (12820382099 / 1000000000000) (12820382106 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 195 12 (2451715066532109 / 4000000000000)) (orderedInterval (-28771379970 / 1000000000000) (-28771379968 / 1000000000000), orderedInterval (-14497535938 / 1000000000000) (-14497535937 / 1000000000000))) = true
  rfl'

theorem compactCertificate622_states : ∀ j,
    BesselStateValid (compactCertificate622.point j) (compactCertificate622.state j) :=
  compactCertificate622.statesValid_of_checks3 compactCertificate622_stateChecks0
    compactCertificate622_stateChecks1 compactCertificate622_stateChecks2
    compactCertificate622_stateChecks3 compactCertificate622_stateChecks4
    compactCertificate622_stateChecks5 compactCertificate622_stateChecks6
    compactCertificate622_stateChecks7 compactCertificate622_stateChecks8

theorem compactCertificate622_chunkChecks0_0 :
    compactCertificate622.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (987 / 2) 0 (IntervalRat.scale (987 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-31245681998 / 1000000000000) (-31245681997 / 1000000000000), orderedInterval (-17680392008 / 1000000000000) (-17680392007 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1454039465578287 / 4000000000000) 0 (IntervalRat.scale (987 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-5417844084 / 1000000000000) (-5417844077 / 1000000000000), orderedInterval (41503984081 / 1000000000000) (41503984088 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (470206488041871 / 800000000000) 0 (IntervalRat.scale (987 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-28797631591 / 1000000000000) (-28797631590 / 1000000000000), orderedInterval (-15907497339 / 1000000000000) (-15907497338 / 1000000000000)))) (orderedInterval (-14125056191 / 1000000000000) (-14125056156 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (424285089629709 / 4000000000000) 0 (IntervalRat.scale (987 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (3201887004 / 1000000000000) (3201887007 / 1000000000000), orderedInterval (77390499847 / 1000000000000) (77390499851 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (1139689431380073 / 4000000000000) 0 (IntervalRat.scale (987 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (8351572605 / 1000000000000) (8351572629 / 1000000000000), orderedInterval (-46540097826 / 1000000000000) (-46540097801 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (3094478507364741 / 4000000000000) 0 (IntervalRat.scale (987 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (28686339366 / 1000000000000) (28686342118 / 1000000000000), orderedInterval (-83783640 / 1000000000000) (-83780888 / 1000000000000)))) (orderedInterval (-1769109499 / 1000000000000) (-1769109243 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (2279378862761133 / 4000000000000) 0 (IntervalRat.scale (987 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-30369987617 / 1000000000000) (-30369922504 / 1000000000000), orderedInterval (13985362219 / 1000000000000) (13985427332 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3905754532109409 / 4000000000000) 0 (IntervalRat.scale (987 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-4786896430 / 1000000000000) (-4786896429 / 1000000000000), orderedInterval (-25078757824 / 1000000000000) (-25078757823 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2876961110711331 / 4000000000000) 0 (IntervalRat.scale (987 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-16817988840 / 1000000000000) (-16817988839 / 1000000000000), orderedInterval (-24529771739 / 1000000000000) (-24529771738 / 1000000000000)))) (orderedInterval (-258810584 / 1000000000000) (-258810556 / 1000000000000))) = true
  rfl'

theorem compactCertificate622_chunkChecks0_1 :
    compactCertificate622.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (4413998187584013 / 4000000000000) 0 (IntervalRat.scale (987 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-24016248132 / 1000000000000) (-24016230718 / 1000000000000), orderedInterval (371481152 / 1000000000000) (371498566 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2548423041803877 / 4000000000000) 0 (IntervalRat.scale (987 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-4650498050 / 1000000000000) (-4650498049 / 1000000000000), orderedInterval (-31263111502 / 1000000000000) (-31263111501 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (4522221408233193 / 4000000000000) 0 (IntervalRat.scale (987 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (8520950670 / 1000000000000) (8520950671 / 1000000000000), orderedInterval (22143398970 / 1000000000000) (22143398971 / 1000000000000)))) (orderedInterval (5134133836 / 1000000000000) (5134137125 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (4225245846703917 / 4000000000000) 0 (IntervalRat.scale (987 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (24519884361 / 1000000000000) (24519891652 / 1000000000000), orderedInterval (1195409446 / 1000000000000) (1195416736 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (3015334807280061 / 4000000000000) 0 (IntervalRat.scale (987 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (17277686490 / 1000000000000) (17277686491 / 1000000000000), orderedInterval (23354994070 / 1000000000000) (23354994071 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (3419068294140219 / 4000000000000) 0 (IntervalRat.scale (987 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (23523578509 / 1000000000000) (23523578513 / 1000000000000), orderedInterval (13822013069 / 1000000000000) (13822013072 / 1000000000000)))) (orderedInterval (1072124953 / 1000000000000) (1072125144 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2850462687865611 / 4000000000000) 0 (IntervalRat.scale (987 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-7665477605 / 1000000000000) (-7665477604 / 1000000000000), orderedInterval (-28884014900 / 1000000000000) (-28884014899 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2518470230589831 / 4000000000000) 0 (IntervalRat.scale (987 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (27698193013 / 1000000000000) (27698268833 / 1000000000000), orderedInterval (-15640265023 / 1000000000000) (-15640189203 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (729950834917269 / 800000000000) 0 (IntervalRat.scale (987 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (21931914386 / 1000000000000) (21931924257 / 1000000000000), orderedInterval (-14732871144 / 1000000000000) (-14732861273 / 1000000000000)))) (orderedInterval (-1112054674 / 1000000000000) (-1112050035 / 1000000000000))) = true
  rfl'

theorem compactCertificate622_chunkChecks0_2 :
    compactCertificate622.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (2019082424588943 / 4000000000000) 0 (IntervalRat.scale (987 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (8464425881 / 1000000000000) (8464425892 / 1000000000000), orderedInterval (-34498385185 / 1000000000000) (-34498385173 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1711598532049623 / 4000000000000) 0 (IntervalRat.scale (987 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (38179887529 / 1000000000000) (38179887575 / 1000000000000), orderedInterval (5439315601 / 1000000000000) (5439315647 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (1071038889288669 / 4000000000000) 0 (IntervalRat.scale (987 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-48668139882 / 1000000000000) (-48668139836 / 1000000000000), orderedInterval (-2906885735 / 1000000000000) (-2906885689 / 1000000000000)))) (orderedInterval (-5098782228 / 1000000000000) (-5098782098 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (576008276773923 / 4000000000000) 0 (IntervalRat.scale (987 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (17948649669 / 1000000000000) (17948649670 / 1000000000000), orderedInterval (63959362635 / 1000000000000) (63959362636 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1563974521010769 / 4000000000000) 0 (IntervalRat.scale (987 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (32112456975 / 1000000000000) (32112523024 / 1000000000000), orderedInterval (-24474632761 / 1000000000000) (-24474566712 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (2135473500145713 / 4000000000000) 0 (IntervalRat.scale (987 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (19004867839 / 1000000000000) (19004867840 / 1000000000000), orderedInterval (28814144763 / 1000000000000) (28814144764 / 1000000000000)))) (orderedInterval (-2516467920 / 1000000000000) (-2516466362 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (902961110711331 / 4000000000000) 0 (IntervalRat.scale (987 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (17230947732 / 1000000000000) (17230947733 / 1000000000000), orderedInterval (50193722000 / 1000000000000) (50193722001 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3670486784139651 / 4000000000000) 0 (IntervalRat.scale (987 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (23001906785 / 1000000000000) (23001906792 / 1000000000000), orderedInterval (12820382099 / 1000000000000) (12820382106 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2451715066532109 / 4000000000000) 0 (IntervalRat.scale (987 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-28771379970 / 1000000000000) (-28771379968 / 1000000000000), orderedInterval (-14497535938 / 1000000000000) (-14497535937 / 1000000000000)))) (orderedInterval (3629751749 / 1000000000000) (3629751887 / 1000000000000))) = true
  rfl'

theorem compactCertificate622_chunkChecks0 :
    compactCertificate622.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate622.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate622_chunkChecks0_0
    compactCertificate622_chunkChecks0_1 compactCertificate622_chunkChecks0_2

theorem compactCertificate622_chunkChecks1_0 :
    compactCertificate622.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (987 / 2) 1 (IntervalRat.scale (987 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-31245681998 / 1000000000000) (-31245681997 / 1000000000000), orderedInterval (-17680392008 / 1000000000000) (-17680392007 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1454039465578287 / 4000000000000) 1 (IntervalRat.scale (987 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-5417844084 / 1000000000000) (-5417844077 / 1000000000000), orderedInterval (41503984081 / 1000000000000) (41503984088 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (470206488041871 / 800000000000) 1 (IntervalRat.scale (987 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-28797631591 / 1000000000000) (-28797631590 / 1000000000000), orderedInterval (-15907497339 / 1000000000000) (-15907497338 / 1000000000000)))) (orderedInterval (-7834782160 / 1000000000000) (-7834782121 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (424285089629709 / 4000000000000) 1 (IntervalRat.scale (987 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (3201887004 / 1000000000000) (3201887007 / 1000000000000), orderedInterval (77390499847 / 1000000000000) (77390499851 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (1139689431380073 / 4000000000000) 1 (IntervalRat.scale (987 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (8351572605 / 1000000000000) (8351572629 / 1000000000000), orderedInterval (-46540097826 / 1000000000000) (-46540097801 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (3094478507364741 / 4000000000000) 1 (IntervalRat.scale (987 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (28686339366 / 1000000000000) (28686342118 / 1000000000000), orderedInterval (-83783640 / 1000000000000) (-83780888 / 1000000000000)))) (orderedInterval (-1152199486 / 1000000000000) (-1152199111 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (2279378862761133 / 4000000000000) 1 (IntervalRat.scale (987 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-30369987617 / 1000000000000) (-30369922504 / 1000000000000), orderedInterval (13985362219 / 1000000000000) (13985427332 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3905754532109409 / 4000000000000) 1 (IntervalRat.scale (987 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-4786896430 / 1000000000000) (-4786896429 / 1000000000000), orderedInterval (-25078757824 / 1000000000000) (-25078757823 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2876961110711331 / 4000000000000) 1 (IntervalRat.scale (987 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-16817988840 / 1000000000000) (-16817988839 / 1000000000000), orderedInterval (-24529771739 / 1000000000000) (-24529771738 / 1000000000000)))) (orderedInterval (666488654 / 1000000000000) (666488702 / 1000000000000))) = true
  rfl'

theorem compactCertificate622_chunkChecks1_1 :
    compactCertificate622.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (4413998187584013 / 4000000000000) 1 (IntervalRat.scale (987 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-24016248132 / 1000000000000) (-24016230718 / 1000000000000), orderedInterval (371481152 / 1000000000000) (371498566 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2548423041803877 / 4000000000000) 1 (IntervalRat.scale (987 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-4650498050 / 1000000000000) (-4650498049 / 1000000000000), orderedInterval (-31263111502 / 1000000000000) (-31263111501 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (4522221408233193 / 4000000000000) 1 (IntervalRat.scale (987 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (8520950670 / 1000000000000) (8520950671 / 1000000000000), orderedInterval (22143398970 / 1000000000000) (22143398971 / 1000000000000)))) (orderedInterval (4073318281 / 1000000000000) (4073325605 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (4225245846703917 / 4000000000000) 1 (IntervalRat.scale (987 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (24519884361 / 1000000000000) (24519891652 / 1000000000000), orderedInterval (1195409446 / 1000000000000) (1195416736 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (3015334807280061 / 4000000000000) 1 (IntervalRat.scale (987 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (17277686490 / 1000000000000) (17277686491 / 1000000000000), orderedInterval (23354994070 / 1000000000000) (23354994071 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (3419068294140219 / 4000000000000) 1 (IntervalRat.scale (987 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (23523578509 / 1000000000000) (23523578513 / 1000000000000), orderedInterval (13822013069 / 1000000000000) (13822013072 / 1000000000000)))) (orderedInterval (3206217305 / 1000000000000) (3206217682 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2850462687865611 / 4000000000000) 1 (IntervalRat.scale (987 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-7665477605 / 1000000000000) (-7665477604 / 1000000000000), orderedInterval (-28884014900 / 1000000000000) (-28884014899 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2518470230589831 / 4000000000000) 1 (IntervalRat.scale (987 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (27698193013 / 1000000000000) (27698268833 / 1000000000000), orderedInterval (-15640265023 / 1000000000000) (-15640189203 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (729950834917269 / 800000000000) 1 (IntervalRat.scale (987 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (21931914386 / 1000000000000) (21931924257 / 1000000000000), orderedInterval (-14732871144 / 1000000000000) (-14732861273 / 1000000000000)))) (orderedInterval (-37178140 / 1000000000000) (-37172069 / 1000000000000))) = true
  rfl'

theorem compactCertificate622_chunkChecks1_2 :
    compactCertificate622.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (2019082424588943 / 4000000000000) 1 (IntervalRat.scale (987 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (8464425881 / 1000000000000) (8464425892 / 1000000000000), orderedInterval (-34498385185 / 1000000000000) (-34498385173 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1711598532049623 / 4000000000000) 1 (IntervalRat.scale (987 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (38179887529 / 1000000000000) (38179887575 / 1000000000000), orderedInterval (5439315601 / 1000000000000) (5439315647 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (1071038889288669 / 4000000000000) 1 (IntervalRat.scale (987 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-48668139882 / 1000000000000) (-48668139836 / 1000000000000), orderedInterval (-2906885735 / 1000000000000) (-2906885689 / 1000000000000)))) (orderedInterval (5323719720 / 1000000000000) (5323719840 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (576008276773923 / 4000000000000) 1 (IntervalRat.scale (987 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (17948649669 / 1000000000000) (17948649670 / 1000000000000), orderedInterval (63959362635 / 1000000000000) (63959362636 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1563974521010769 / 4000000000000) 1 (IntervalRat.scale (987 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (32112456975 / 1000000000000) (32112523024 / 1000000000000), orderedInterval (-24474632761 / 1000000000000) (-24474566712 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (2135473500145713 / 4000000000000) 1 (IntervalRat.scale (987 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (19004867839 / 1000000000000) (19004867840 / 1000000000000), orderedInterval (28814144763 / 1000000000000) (28814144764 / 1000000000000)))) (orderedInterval (-2293621058 / 1000000000000) (-2293619817 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (902961110711331 / 4000000000000) 1 (IntervalRat.scale (987 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (17230947732 / 1000000000000) (17230947733 / 1000000000000), orderedInterval (50193722000 / 1000000000000) (50193722001 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3670486784139651 / 4000000000000) 1 (IntervalRat.scale (987 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (23001906785 / 1000000000000) (23001906792 / 1000000000000), orderedInterval (12820382099 / 1000000000000) (12820382106 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2451715066532109 / 4000000000000) 1 (IntervalRat.scale (987 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-28771379970 / 1000000000000) (-28771379968 / 1000000000000), orderedInterval (-14497535938 / 1000000000000) (-14497535937 / 1000000000000)))) (orderedInterval (1576321953 / 1000000000000) (1576322147 / 1000000000000))) = true
  rfl'

theorem compactCertificate622_chunkChecks1 :
    compactCertificate622.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate622.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate622_chunkChecks1_0
    compactCertificate622_chunkChecks1_1 compactCertificate622_chunkChecks1_2

theorem compactCertificate622_chunkChecks2_0 :
    compactCertificate622.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (987 / 2) 2 (IntervalRat.scale (987 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-31245681998 / 1000000000000) (-31245681997 / 1000000000000), orderedInterval (-17680392008 / 1000000000000) (-17680392007 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1454039465578287 / 4000000000000) 2 (IntervalRat.scale (987 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-5417844084 / 1000000000000) (-5417844077 / 1000000000000), orderedInterval (41503984081 / 1000000000000) (41503984088 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (470206488041871 / 800000000000) 2 (IntervalRat.scale (987 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-28797631591 / 1000000000000) (-28797631590 / 1000000000000), orderedInterval (-15907497339 / 1000000000000) (-15907497338 / 1000000000000)))) (orderedInterval (14825018038 / 1000000000000) (14825018083 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (424285089629709 / 4000000000000) 2 (IntervalRat.scale (987 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (3201887004 / 1000000000000) (3201887007 / 1000000000000), orderedInterval (77390499847 / 1000000000000) (77390499851 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (1139689431380073 / 4000000000000) 2 (IntervalRat.scale (987 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (8351572605 / 1000000000000) (8351572629 / 1000000000000), orderedInterval (-46540097826 / 1000000000000) (-46540097801 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (3094478507364741 / 4000000000000) 2 (IntervalRat.scale (987 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (28686339366 / 1000000000000) (28686342118 / 1000000000000), orderedInterval (-83783640 / 1000000000000) (-83780888 / 1000000000000)))) (orderedInterval (4913730984 / 1000000000000) (4913731559 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (2279378862761133 / 4000000000000) 2 (IntervalRat.scale (987 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-30369987617 / 1000000000000) (-30369922504 / 1000000000000), orderedInterval (13985362219 / 1000000000000) (13985427332 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3905754532109409 / 4000000000000) 2 (IntervalRat.scale (987 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-4786896430 / 1000000000000) (-4786896429 / 1000000000000), orderedInterval (-25078757824 / 1000000000000) (-25078757823 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2876961110711331 / 4000000000000) 2 (IntervalRat.scale (987 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-16817988840 / 1000000000000) (-16817988839 / 1000000000000), orderedInterval (-24529771739 / 1000000000000) (-24529771738 / 1000000000000)))) (orderedInterval (283986868 / 1000000000000) (283986954 / 1000000000000))) = true
  rfl'

theorem compactCertificate622_chunkChecks2_1 :
    compactCertificate622.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (4413998187584013 / 4000000000000) 2 (IntervalRat.scale (987 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-24016248132 / 1000000000000) (-24016230718 / 1000000000000), orderedInterval (371481152 / 1000000000000) (371498566 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2548423041803877 / 4000000000000) 2 (IntervalRat.scale (987 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-4650498050 / 1000000000000) (-4650498049 / 1000000000000), orderedInterval (-31263111502 / 1000000000000) (-31263111501 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (4522221408233193 / 4000000000000) 2 (IntervalRat.scale (987 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (8520950670 / 1000000000000) (8520950671 / 1000000000000), orderedInterval (22143398970 / 1000000000000) (22143398971 / 1000000000000)))) (orderedInterval (-27128115388 / 1000000000000) (-27128099033 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (4225245846703917 / 4000000000000) 2 (IntervalRat.scale (987 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (24519884361 / 1000000000000) (24519891652 / 1000000000000), orderedInterval (1195409446 / 1000000000000) (1195416736 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (3015334807280061 / 4000000000000) 2 (IntervalRat.scale (987 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (17277686490 / 1000000000000) (17277686491 / 1000000000000), orderedInterval (23354994070 / 1000000000000) (23354994071 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (3419068294140219 / 4000000000000) 2 (IntervalRat.scale (987 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (23523578509 / 1000000000000) (23523578513 / 1000000000000), orderedInterval (13822013069 / 1000000000000) (13822013072 / 1000000000000)))) (orderedInterval (-1433578578 / 1000000000000) (-1433577816 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2850462687865611 / 4000000000000) 2 (IntervalRat.scale (987 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-7665477605 / 1000000000000) (-7665477604 / 1000000000000), orderedInterval (-28884014900 / 1000000000000) (-28884014899 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2518470230589831 / 4000000000000) 2 (IntervalRat.scale (987 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (27698193013 / 1000000000000) (27698268833 / 1000000000000), orderedInterval (-15640265023 / 1000000000000) (-15640189203 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (729950834917269 / 800000000000) 2 (IntervalRat.scale (987 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (21931914386 / 1000000000000) (21931924257 / 1000000000000), orderedInterval (-14732871144 / 1000000000000) (-14732861273 / 1000000000000)))) (orderedInterval (845080053 / 1000000000000) (845088094 / 1000000000000))) = true
  rfl'

theorem compactCertificate622_chunkChecks2_2 :
    compactCertificate622.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (2019082424588943 / 4000000000000) 2 (IntervalRat.scale (987 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (8464425881 / 1000000000000) (8464425892 / 1000000000000), orderedInterval (-34498385185 / 1000000000000) (-34498385173 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1711598532049623 / 4000000000000) 2 (IntervalRat.scale (987 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (38179887529 / 1000000000000) (38179887575 / 1000000000000), orderedInterval (5439315601 / 1000000000000) (5439315647 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (1071038889288669 / 4000000000000) 2 (IntervalRat.scale (987 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-48668139882 / 1000000000000) (-48668139836 / 1000000000000), orderedInterval (-2906885735 / 1000000000000) (-2906885689 / 1000000000000)))) (orderedInterval (3496211074 / 1000000000000) (3496211187 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (576008276773923 / 4000000000000) 2 (IntervalRat.scale (987 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (17948649669 / 1000000000000) (17948649670 / 1000000000000), orderedInterval (63959362635 / 1000000000000) (63959362636 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1563974521010769 / 4000000000000) 2 (IntervalRat.scale (987 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (32112456975 / 1000000000000) (32112523024 / 1000000000000), orderedInterval (-24474632761 / 1000000000000) (-24474566712 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (2135473500145713 / 4000000000000) 2 (IntervalRat.scale (987 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (19004867839 / 1000000000000) (19004867840 / 1000000000000), orderedInterval (28814144763 / 1000000000000) (28814144764 / 1000000000000)))) (orderedInterval (2194722662 / 1000000000000) (2194723659 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (902961110711331 / 4000000000000) 2 (IntervalRat.scale (987 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (17230947732 / 1000000000000) (17230947733 / 1000000000000), orderedInterval (50193722000 / 1000000000000) (50193722001 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3670486784139651 / 4000000000000) 2 (IntervalRat.scale (987 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (23001906785 / 1000000000000) (23001906792 / 1000000000000), orderedInterval (12820382099 / 1000000000000) (12820382106 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2451715066532109 / 4000000000000) 2 (IntervalRat.scale (987 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-28771379970 / 1000000000000) (-28771379968 / 1000000000000), orderedInterval (-14497535938 / 1000000000000) (-14497535937 / 1000000000000)))) (orderedInterval (-1878487125 / 1000000000000) (-1878486839 / 1000000000000))) = true
  rfl'

theorem compactCertificate622_chunkChecks2 :
    compactCertificate622.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate622.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate622_chunkChecks2_0
    compactCertificate622_chunkChecks2_1 compactCertificate622_chunkChecks2_2

theorem compactCertificate622_chunkChecks3_0 :
    compactCertificate622.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (987 / 2) 3 (IntervalRat.scale (987 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-31245681998 / 1000000000000) (-31245681997 / 1000000000000), orderedInterval (-17680392008 / 1000000000000) (-17680392007 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1454039465578287 / 4000000000000) 3 (IntervalRat.scale (987 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-5417844084 / 1000000000000) (-5417844077 / 1000000000000), orderedInterval (41503984081 / 1000000000000) (41503984088 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (470206488041871 / 800000000000) 3 (IntervalRat.scale (987 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-28797631591 / 1000000000000) (-28797631590 / 1000000000000), orderedInterval (-15907497339 / 1000000000000) (-15907497338 / 1000000000000)))) (orderedInterval (8400265161 / 1000000000000) (8400265213 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (424285089629709 / 4000000000000) 3 (IntervalRat.scale (987 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (3201887004 / 1000000000000) (3201887007 / 1000000000000), orderedInterval (77390499847 / 1000000000000) (77390499851 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (1139689431380073 / 4000000000000) 3 (IntervalRat.scale (987 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (8351572605 / 1000000000000) (8351572629 / 1000000000000), orderedInterval (-46540097826 / 1000000000000) (-46540097801 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (3094478507364741 / 4000000000000) 3 (IntervalRat.scale (987 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (28686339366 / 1000000000000) (28686342118 / 1000000000000), orderedInterval (-83783640 / 1000000000000) (-83780888 / 1000000000000)))) (orderedInterval (302453375 / 1000000000000) (302454269 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (2279378862761133 / 4000000000000) 3 (IntervalRat.scale (987 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-30369987617 / 1000000000000) (-30369922504 / 1000000000000), orderedInterval (13985362219 / 1000000000000) (13985427332 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3905754532109409 / 4000000000000) 3 (IntervalRat.scale (987 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-4786896430 / 1000000000000) (-4786896429 / 1000000000000), orderedInterval (-25078757824 / 1000000000000) (-25078757823 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2876961110711331 / 4000000000000) 3 (IntervalRat.scale (987 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-16817988840 / 1000000000000) (-16817988839 / 1000000000000), orderedInterval (-24529771739 / 1000000000000) (-24529771738 / 1000000000000)))) (orderedInterval (-4157023633 / 1000000000000) (-4157023477 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate622_chunkChecks3_1 :
    compactCertificate622.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (4413998187584013 / 4000000000000) 3 (IntervalRat.scale (987 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-24016248132 / 1000000000000) (-24016230718 / 1000000000000), orderedInterval (371481152 / 1000000000000) (371498566 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2548423041803877 / 4000000000000) 3 (IntervalRat.scale (987 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-4650498050 / 1000000000000) (-4650498049 / 1000000000000), orderedInterval (-31263111502 / 1000000000000) (-31263111501 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (4522221408233193 / 4000000000000) 3 (IntervalRat.scale (987 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (8520950670 / 1000000000000) (8520950671 / 1000000000000), orderedInterval (22143398970 / 1000000000000) (22143398971 / 1000000000000)))) (orderedInterval (-32069333613 / 1000000000000) (-32069297081 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (4225245846703917 / 4000000000000) 3 (IntervalRat.scale (987 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (24519884361 / 1000000000000) (24519891652 / 1000000000000), orderedInterval (1195409446 / 1000000000000) (1195416736 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (3015334807280061 / 4000000000000) 3 (IntervalRat.scale (987 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (17277686490 / 1000000000000) (17277686491 / 1000000000000), orderedInterval (23354994070 / 1000000000000) (23354994071 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (3419068294140219 / 4000000000000) 3 (IntervalRat.scale (987 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (23523578509 / 1000000000000) (23523578513 / 1000000000000), orderedInterval (13822013069 / 1000000000000) (13822013072 / 1000000000000)))) (orderedInterval (-7293638527 / 1000000000000) (-7293636967 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2850462687865611 / 4000000000000) 3 (IntervalRat.scale (987 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-7665477605 / 1000000000000) (-7665477604 / 1000000000000), orderedInterval (-28884014900 / 1000000000000) (-28884014899 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2518470230589831 / 4000000000000) 3 (IntervalRat.scale (987 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (27698193013 / 1000000000000) (27698268833 / 1000000000000), orderedInterval (-15640265023 / 1000000000000) (-15640189203 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (729950834917269 / 800000000000) 3 (IntervalRat.scale (987 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (21931914386 / 1000000000000) (21931924257 / 1000000000000), orderedInterval (-14732871144 / 1000000000000) (-14732861273 / 1000000000000)))) (orderedInterval (1528065583 / 1000000000000) (1528076364 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate622_chunkChecks3_2 :
    compactCertificate622.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (2019082424588943 / 4000000000000) 3 (IntervalRat.scale (987 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (8464425881 / 1000000000000) (8464425892 / 1000000000000), orderedInterval (-34498385185 / 1000000000000) (-34498385173 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1711598532049623 / 4000000000000) 3 (IntervalRat.scale (987 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (38179887529 / 1000000000000) (38179887575 / 1000000000000), orderedInterval (5439315601 / 1000000000000) (5439315647 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (1071038889288669 / 4000000000000) 3 (IntervalRat.scale (987 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-48668139882 / 1000000000000) (-48668139836 / 1000000000000), orderedInterval (-2906885735 / 1000000000000) (-2906885689 / 1000000000000)))) (orderedInterval (-5693912725 / 1000000000000) (-5693912614 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (576008276773923 / 4000000000000) 3 (IntervalRat.scale (987 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (17948649669 / 1000000000000) (17948649670 / 1000000000000), orderedInterval (63959362635 / 1000000000000) (63959362636 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1563974521010769 / 4000000000000) 3 (IntervalRat.scale (987 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (32112456975 / 1000000000000) (32112523024 / 1000000000000), orderedInterval (-24474632761 / 1000000000000) (-24474566712 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (2135473500145713 / 4000000000000) 3 (IntervalRat.scale (987 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (19004867839 / 1000000000000) (19004867840 / 1000000000000), orderedInterval (28814144763 / 1000000000000) (28814144764 / 1000000000000)))) (orderedInterval (2544475008 / 1000000000000) (2544475810 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (902961110711331 / 4000000000000) 3 (IntervalRat.scale (987 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (17230947732 / 1000000000000) (17230947733 / 1000000000000), orderedInterval (50193722000 / 1000000000000) (50193722001 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3670486784139651 / 4000000000000) 3 (IntervalRat.scale (987 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (23001906785 / 1000000000000) (23001906792 / 1000000000000), orderedInterval (12820382099 / 1000000000000) (12820382106 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2451715066532109 / 4000000000000) 3 (IntervalRat.scale (987 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-28771379970 / 1000000000000) (-28771379968 / 1000000000000), orderedInterval (-14497535938 / 1000000000000) (-14497535937 / 1000000000000)))) (orderedInterval (1472523146 / 1000000000000) (1472523587 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate622_chunkChecks3 :
    compactCertificate622.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate622.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate622_chunkChecks3_0
    compactCertificate622_chunkChecks3_1 compactCertificate622_chunkChecks3_2

theorem compactCertificate622_chunkChecks4_0 :
    compactCertificate622.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (987 / 2) 4 (IntervalRat.scale (987 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-31245681998 / 1000000000000) (-31245681997 / 1000000000000), orderedInterval (-17680392008 / 1000000000000) (-17680392007 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1454039465578287 / 4000000000000) 4 (IntervalRat.scale (987 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-5417844084 / 1000000000000) (-5417844077 / 1000000000000), orderedInterval (41503984081 / 1000000000000) (41503984088 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (470206488041871 / 800000000000) 4 (IntervalRat.scale (987 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-28797631591 / 1000000000000) (-28797631590 / 1000000000000), orderedInterval (-15907497339 / 1000000000000) (-15907497338 / 1000000000000)))) (orderedInterval (-15833713446 / 1000000000000) (-15833713385 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (424285089629709 / 4000000000000) 4 (IntervalRat.scale (987 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (3201887004 / 1000000000000) (3201887007 / 1000000000000), orderedInterval (77390499847 / 1000000000000) (77390499851 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (1139689431380073 / 4000000000000) 4 (IntervalRat.scale (987 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (8351572605 / 1000000000000) (8351572629 / 1000000000000), orderedInterval (-46540097826 / 1000000000000) (-46540097801 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (3094478507364741 / 4000000000000) 4 (IntervalRat.scale (987 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (28686339366 / 1000000000000) (28686342118 / 1000000000000), orderedInterval (-83783640 / 1000000000000) (-83780888 / 1000000000000)))) (orderedInterval (-12282635928 / 1000000000000) (-12282634528 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (2279378862761133 / 4000000000000) 4 (IntervalRat.scale (987 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-30369987617 / 1000000000000) (-30369922504 / 1000000000000), orderedInterval (13985362219 / 1000000000000) (13985427332 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3905754532109409 / 4000000000000) 4 (IntervalRat.scale (987 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-4786896430 / 1000000000000) (-4786896429 / 1000000000000), orderedInterval (-25078757824 / 1000000000000) (-25078757823 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2876961110711331 / 4000000000000) 4 (IntervalRat.scale (987 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-16817988840 / 1000000000000) (-16817988839 / 1000000000000), orderedInterval (-24529771739 / 1000000000000) (-24529771738 / 1000000000000)))) (orderedInterval (445853947 / 1000000000000) (445854236 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate622_chunkChecks4_1 :
    compactCertificate622.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (4413998187584013 / 4000000000000) 4 (IntervalRat.scale (987 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-24016248132 / 1000000000000) (-24016230718 / 1000000000000), orderedInterval (371481152 / 1000000000000) (371498566 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2548423041803877 / 4000000000000) 4 (IntervalRat.scale (987 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-4650498050 / 1000000000000) (-4650498049 / 1000000000000), orderedInterval (-31263111502 / 1000000000000) (-31263111501 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (4522221408233193 / 4000000000000) 4 (IntervalRat.scale (987 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (8520950670 / 1000000000000) (8520950671 / 1000000000000), orderedInterval (22143398970 / 1000000000000) (22143398971 / 1000000000000)))) (orderedInterval (139221088056 / 1000000000000) (139221169784 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (4225245846703917 / 4000000000000) 4 (IntervalRat.scale (987 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (24519884361 / 1000000000000) (24519891652 / 1000000000000), orderedInterval (1195409446 / 1000000000000) (1195416736 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (3015334807280061 / 4000000000000) 4 (IntervalRat.scale (987 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (17277686490 / 1000000000000) (17277686491 / 1000000000000), orderedInterval (23354994070 / 1000000000000) (23354994071 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (3419068294140219 / 4000000000000) 4 (IntervalRat.scale (987 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (23523578509 / 1000000000000) (23523578513 / 1000000000000), orderedInterval (13822013069 / 1000000000000) (13822013072 / 1000000000000)))) (orderedInterval (-1438124742 / 1000000000000) (-1438121508 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2850462687865611 / 4000000000000) 4 (IntervalRat.scale (987 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-7665477605 / 1000000000000) (-7665477604 / 1000000000000), orderedInterval (-28884014900 / 1000000000000) (-28884014899 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2518470230589831 / 4000000000000) 4 (IntervalRat.scale (987 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (27698193013 / 1000000000000) (27698268833 / 1000000000000), orderedInterval (-15640265023 / 1000000000000) (-15640189203 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (729950834917269 / 800000000000) 4 (IntervalRat.scale (987 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (21931914386 / 1000000000000) (21931924257 / 1000000000000), orderedInterval (-14732871144 / 1000000000000) (-14732861273 / 1000000000000)))) (orderedInterval (1971527397 / 1000000000000) (1971542138 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate622_chunkChecks4_2 :
    compactCertificate622.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (2019082424588943 / 4000000000000) 4 (IntervalRat.scale (987 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (8464425881 / 1000000000000) (8464425892 / 1000000000000), orderedInterval (-34498385185 / 1000000000000) (-34498385173 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1711598532049623 / 4000000000000) 4 (IntervalRat.scale (987 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (38179887529 / 1000000000000) (38179887575 / 1000000000000), orderedInterval (5439315601 / 1000000000000) (5439315647 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (1071038889288669 / 4000000000000) 4 (IntervalRat.scale (987 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-48668139882 / 1000000000000) (-48668139836 / 1000000000000), orderedInterval (-2906885735 / 1000000000000) (-2906885689 / 1000000000000)))) (orderedInterval (-2816986433 / 1000000000000) (-2816986325 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (576008276773923 / 4000000000000) 4 (IntervalRat.scale (987 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (17948649669 / 1000000000000) (17948649670 / 1000000000000), orderedInterval (63959362635 / 1000000000000) (63959362636 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1563974521010769 / 4000000000000) 4 (IntervalRat.scale (987 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (32112456975 / 1000000000000) (32112523024 / 1000000000000), orderedInterval (-24474632761 / 1000000000000) (-24474566712 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (2135473500145713 / 4000000000000) 4 (IntervalRat.scale (987 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (19004867839 / 1000000000000) (19004867840 / 1000000000000), orderedInterval (28814144763 / 1000000000000) (28814144764 / 1000000000000)))) (orderedInterval (-2294582449 / 1000000000000) (-2294581798 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (902961110711331 / 4000000000000) 4 (IntervalRat.scale (987 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (17230947732 / 1000000000000) (17230947733 / 1000000000000), orderedInterval (50193722000 / 1000000000000) (50193722001 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3670486784139651 / 4000000000000) 4 (IntervalRat.scale (987 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (23001906785 / 1000000000000) (23001906792 / 1000000000000), orderedInterval (12820382099 / 1000000000000) (12820382106 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2451715066532109 / 4000000000000) 4 (IntervalRat.scale (987 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-28771379970 / 1000000000000) (-28771379968 / 1000000000000), orderedInterval (-14497535938 / 1000000000000) (-14497535937 / 1000000000000)))) (orderedInterval (-9538319250 / 1000000000000) (-9538318540 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate622_chunkChecks4 :
    compactCertificate622.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate622.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate622_chunkChecks4_0
    compactCertificate622_chunkChecks4_1 compactCertificate622_chunkChecks4_2

theorem compactCertificate622_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate622.chunkCheck r b = true :=
  compactCertificate622.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate622_chunkChecks0
    · exact compactCertificate622_chunkChecks1
    · exact compactCertificate622_chunkChecks2
    · exact compactCertificate622_chunkChecks3
    · exact compactCertificate622_chunkChecks4)

theorem compactCertificate622_coefficient0 :
    compactCertificate622.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate622_coefficient1 :
    compactCertificate622.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate622_coefficient2 :
    compactCertificate622.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate622_coefficient3 :
    compactCertificate622.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate622_coefficient4 :
    compactCertificate622.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate622_coefficients : ∀ r : Fin 5,
    compactCertificate622.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate622_coefficient0
  · exact compactCertificate622_coefficient1
  · exact compactCertificate622_coefficient2
  · exact compactCertificate622_coefficient3
  · exact compactCertificate622_coefficient4

theorem compactCertificate622_lower : (1 : ℚ) ≤ compactCertificate622.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate622, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate622_proves {t : ℝ} (ht : t ∈ compactCertificate622.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate622.proves compactCertificate622_states compactCertificate622_chunks
    compactCertificate622_coefficients compactCertificate622_lower ht

end Erdos232
