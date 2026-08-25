/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate608 : CompactCertificate where
  left := 479
  right := 480
  center := 959 / 2
  grid := fun i =>
    match i.val with
    | 0 => 153
    | 1 => 112
    | 2 => 182
    | 3 => 33
    | 4 => 88
    | 5 => 239
    | 6 => 176
    | 7 => 302
    | 8 => 223
    | 9 => 341
    | 10 => 197
    | 11 => 350
    | 12 => 327
    | 13 => 233
    | 14 => 264
    | 15 => 221
    | 16 => 195
    | 17 => 282
    | 18 => 156
    | 19 => 132
    | 20 => 83
    | 21 => 45
    | 22 => 121
    | 23 => 165
    | 24 => 70
    | 25 => 284
    | _ => 190
  point := fun i =>
    match i.val with
    | 0 => 959 / 2
    | 1 => 1412790119037059 / 4000000000000
    | 2 => 456867296891747 / 800000000000
    | 3 => 412248633186313 / 4000000000000
    | 4 => 1107357816305461 / 4000000000000
    | 5 => 3006691883042337 / 4000000000000
    | 6 => 2214715632611881 / 4000000000000
    | 7 => 3794952985099213 / 4000000000000
    | 8 => 2795345192676967 / 4000000000000
    | 9 => 4288778380844041 / 4000000000000
    | 10 => 2476127352674689 / 4000000000000
    | 11 => 4393931439205301 / 4000000000000
    | 12 => 4105380716300969 / 4000000000000
    | 13 => 2929793394307577 / 4000000000000
    | 14 => 3322073448916383 / 4000000000000
    | 15 => 2769598498138927 / 4000000000000
    | 16 => 2447024266601467 / 4000000000000
    | 17 => 709243009813233 / 800000000000
    | 18 => 1961803490558051 / 4000000000000
    | 19 => 1663042545324811 / 4000000000000
    | 20 => 1040654807323033 / 4000000000000
    | 21 => 559667616439911 / 4000000000000
    | 22 => 1519606449492733 / 4000000000000
    | 23 => 2074892691630941 / 4000000000000
    | 24 => 877345192676967 / 4000000000000
    | 25 => 3566359499483207 / 4000000000000
    | _ => 2382162866063113 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (13465855384 / 1000000000000) (13465855494 / 1000000000000), orderedInterval (-33871765211 / 1000000000000) (-33871765101 / 1000000000000))
    | 1 => (orderedInterval (36118403329 / 1000000000000) (36118476030 / 1000000000000), orderedInterval (-22364934423 / 1000000000000) (-22364861722 / 1000000000000))
    | 2 => (orderedInterval (3314545196 / 1000000000000) (3314545197 / 1000000000000), orderedInterval (33220143830 / 1000000000000) (33220143831 / 1000000000000))
    | 3 => (orderedInterval (-13589849077 / 1000000000000) (-13589849076 / 1000000000000), orderedInterval (-77344865740 / 1000000000000) (-77344865739 / 1000000000000))
    | 4 => (orderedInterval (44045401983 / 1000000000000) (44045401984 / 1000000000000), orderedInterval (18883549069 / 1000000000000) (18883549071 / 1000000000000))
    | 5 => (orderedInterval (-29070370557 / 1000000000000) (-29070366604 / 1000000000000), orderedInterval (1379718426 / 1000000000000) (1379722379 / 1000000000000))
    | 6 => (orderedInterval (33896307622 / 1000000000000) (33896308150 / 1000000000000), orderedInterval (885586385 / 1000000000000) (885586914 / 1000000000000))
    | 7 => (orderedInterval (17893291788 / 1000000000000) (17893291789 / 1000000000000), orderedInterval (18721491154 / 1000000000000) (18721491156 / 1000000000000))
    | 8 => (orderedInterval (24614554406 / 1000000000000) (24614576300 / 1000000000000), orderedInterval (-17484571440 / 1000000000000) (-17484549546 / 1000000000000))
    | 9 => (orderedInterval (-24173960123 / 1000000000000) (-24173918205 / 1000000000000), orderedInterval (3073036787 / 1000000000000) (3073078705 / 1000000000000))
    | 10 => (orderedInterval (-25577653758 / 1000000000000) (-25577653757 / 1000000000000), orderedInterval (-19323475112 / 1000000000000) (-19323475111 / 1000000000000))
    | 11 => (orderedInterval (-6867431523 / 1000000000000) (-6867431522 / 1000000000000), orderedInterval (23076552158 / 1000000000000) (23076552159 / 1000000000000))
    | 12 => (orderedInterval (4221953450 / 1000000000000) (4221953451 / 1000000000000), orderedInterval (-24546987114 / 1000000000000) (-24546987113 / 1000000000000))
    | 13 => (orderedInterval (-27906990679 / 1000000000000) (-27906990651 / 1000000000000), orderedInterval (-9487078679 / 1000000000000) (-9487078651 / 1000000000000))
    | 14 => (orderedInterval (25985320563 / 1000000000000) (25985423233 / 1000000000000), orderedInterval (-9570448808 / 1000000000000) (-9570346139 / 1000000000000))
    | 15 => (orderedInterval (27120814208 / 1000000000000) (27120902496 / 1000000000000), orderedInterval (-13580551301 / 1000000000000) (-13580463013 / 1000000000000))
    | 16 => (orderedInterval (2233983654 / 1000000000000) (2233983655 / 1000000000000), orderedInterval (-32183386298 / 1000000000000) (-32183386297 / 1000000000000))
    | 17 => (orderedInterval (26450933630 / 1000000000000) (26450934441 / 1000000000000), orderedInterval (4278290587 / 1000000000000) (4278291399 / 1000000000000))
    | 18 => (orderedInterval (32849235385 / 1000000000000) (32849235386 / 1000000000000), orderedInterval (14763704643 / 1000000000000) (14763704644 / 1000000000000))
    | 19 => (orderedInterval (37555499564 / 1000000000000) (37555507569 / 1000000000000), orderedInterval (-11036085525 / 1000000000000) (-11036077520 / 1000000000000))
    | 20 => (orderedInterval (-9654418110 / 1000000000000) (-9654418109 / 1000000000000), orderedInterval (-48497353135 / 1000000000000) (-48497353134 / 1000000000000))
    | 21 => (orderedInterval (41901350959 / 1000000000000) (41901372729 / 1000000000000), orderedInterval (-53010573284 / 1000000000000) (-53010551514 / 1000000000000))
    | 22 => (orderedInterval (-21535064390 / 1000000000000) (-21535064389 / 1000000000000), orderedInterval (-34785314140 / 1000000000000) (-34785314139 / 1000000000000))
    | 23 => (orderedInterval (-31912367237 / 1000000000000) (-31912367235 / 1000000000000), orderedInterval (-14422016024 / 1000000000000) (-14422016023 / 1000000000000))
    | 24 => (orderedInterval (11211765141 / 1000000000000) (11211765142 / 1000000000000), orderedInterval (52669657225 / 1000000000000) (52669657226 / 1000000000000))
    | 25 => (orderedInterval (4331542288 / 1000000000000) (4331542289 / 1000000000000), orderedInterval (26365457434 / 1000000000000) (26365457435 / 1000000000000))
    | _ => (orderedInterval (-17827399710 / 1000000000000) (-17827399030 / 1000000000000), orderedInterval (27422296898 / 1000000000000) (27422297579 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (5868448398 / 1000000000000) (5868449153 / 1000000000000)
      | 1 => orderedInterval (3822216654 / 1000000000000) (3822216993 / 1000000000000)
      | 2 => orderedInterval (42984492 / 1000000000000) (42985048 / 1000000000000)
      | 3 => orderedInterval (1424073775 / 1000000000000) (1424081414 / 1000000000000)
      | 4 => orderedInterval (-2846685547 / 1000000000000) (-2846684967 / 1000000000000)
      | 5 => orderedInterval (862587111 / 1000000000000) (862588197 / 1000000000000)
      | 6 => orderedInterval (-7692286798 / 1000000000000) (-7692286224 / 1000000000000)
      | 7 => orderedInterval (2160577019 / 1000000000000) (2160577479 / 1000000000000)
      | _ => orderedInterval (3059885857 / 1000000000000) (3059886118 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-11257357887 / 1000000000000) (-11257357307 / 1000000000000)
      | 1 => orderedInterval (424669559 / 1000000000000) (424670065 / 1000000000000)
      | 2 => orderedInterval (-1758394991 / 1000000000000) (-1758394172 / 1000000000000)
      | 3 => orderedInterval (4445865429 / 1000000000000) (4445882478 / 1000000000000)
      | 4 => orderedInterval (-337958451 / 1000000000000) (-337957454 / 1000000000000)
      | 5 => orderedInterval (2325818708 / 1000000000000) (2325820286 / 1000000000000)
      | 6 => orderedInterval (-2729546152 / 1000000000000) (-2729545647 / 1000000000000)
      | 7 => orderedInterval (2106573288 / 1000000000000) (2106573457 / 1000000000000)
      | _ => orderedInterval (-10235726761 / 1000000000000) (-10235726416 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-5772417622 / 1000000000000) (-5772417167 / 1000000000000)
      | 1 => orderedInterval (-5622279571 / 1000000000000) (-5622278788 / 1000000000000)
      | 2 => orderedInterval (900684813 / 1000000000000) (900686022 / 1000000000000)
      | 3 => orderedInterval (-13204365747 / 1000000000000) (-13204327625 / 1000000000000)
      | 4 => orderedInterval (6901992108 / 1000000000000) (6901993828 / 1000000000000)
      | 5 => orderedInterval (-2764949591 / 1000000000000) (-2764947292 / 1000000000000)
      | 6 => orderedInterval (7191291920 / 1000000000000) (7191292368 / 1000000000000)
      | 7 => orderedInterval (-3107409590 / 1000000000000) (-3107409504 / 1000000000000)
      | _ => orderedInterval (-3933464670 / 1000000000000) (-3933464197 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (10227534584 / 1000000000000) (10227534950 / 1000000000000)
      | 1 => orderedInterval (248554498 / 1000000000000) (248555718 / 1000000000000)
      | 2 => orderedInterval (5779111848 / 1000000000000) (5779113641 / 1000000000000)
      | 3 => orderedInterval (-30228134997 / 1000000000000) (-30228049793 / 1000000000000)
      | 4 => orderedInterval (-1414242761 / 1000000000000) (-1414239788 / 1000000000000)
      | 5 => orderedInterval (-4039105606 / 1000000000000) (-4039102248 / 1000000000000)
      | 6 => orderedInterval (2356045780 / 1000000000000) (2356046180 / 1000000000000)
      | 7 => orderedInterval (-1809627697 / 1000000000000) (-1809627634 / 1000000000000)
      | _ => orderedInterval (23632712449 / 1000000000000) (23632713120 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (5785138621 / 1000000000000) (5785138924 / 1000000000000)
      | 1 => orderedInterval (12658040986 / 1000000000000) (12658042896 / 1000000000000)
      | 2 => orderedInterval (-5798589470 / 1000000000000) (-5798586796 / 1000000000000)
      | 3 => orderedInterval (75358006805 / 1000000000000) (75358197471 / 1000000000000)
      | 4 => orderedInterval (-17145149014 / 1000000000000) (-17145143861 / 1000000000000)
      | 5 => orderedInterval (8954105986 / 1000000000000) (8954110916 / 1000000000000)
      | 6 => orderedInterval (-6987340253 / 1000000000000) (-6987339894 / 1000000000000)
      | 7 => orderedInterval (3544059589 / 1000000000000) (3544059647 / 1000000000000)
      | _ => orderedInterval (3648792599 / 1000000000000) (3648793586 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (6701800961 / 1000000000000) (6701813211 / 1000000000000)
    | 1 => orderedInterval (-17016057258 / 1000000000000) (-17016034710 / 1000000000000)
    | 2 => orderedInterval (-19410917950 / 1000000000000) (-19410872355 / 1000000000000)
    | 3 => orderedInterval (4752848098 / 1000000000000) (4752944146 / 1000000000000)
    | _ => orderedInterval (80017065849 / 1000000000000) (80017272889 / 1000000000000)

theorem compactCertificate608_stateChecks0 :
    compactCertificate608.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 153 12 (959 / 2)) (orderedInterval (13465855384 / 1000000000000) (13465855494 / 1000000000000), orderedInterval (-33871765211 / 1000000000000) (-33871765101 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 112 12 (1412790119037059 / 4000000000000)) (orderedInterval (36118403329 / 1000000000000) (36118476030 / 1000000000000), orderedInterval (-22364934423 / 1000000000000) (-22364861722 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 182 12 (456867296891747 / 800000000000)) (orderedInterval (3314545196 / 1000000000000) (3314545197 / 1000000000000), orderedInterval (33220143830 / 1000000000000) (33220143831 / 1000000000000))) = true
  rfl'

theorem compactCertificate608_stateChecks1 :
    compactCertificate608.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 33 12 (412248633186313 / 4000000000000)) (orderedInterval (-13589849077 / 1000000000000) (-13589849076 / 1000000000000), orderedInterval (-77344865740 / 1000000000000) (-77344865739 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 88 12 (1107357816305461 / 4000000000000)) (orderedInterval (44045401983 / 1000000000000) (44045401984 / 1000000000000), orderedInterval (18883549069 / 1000000000000) (18883549071 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 239 12 (3006691883042337 / 4000000000000)) (orderedInterval (-29070370557 / 1000000000000) (-29070366604 / 1000000000000), orderedInterval (1379718426 / 1000000000000) (1379722379 / 1000000000000))) = true
  rfl'

theorem compactCertificate608_stateChecks2 :
    compactCertificate608.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 176 12 (2214715632611881 / 4000000000000)) (orderedInterval (33896307622 / 1000000000000) (33896308150 / 1000000000000), orderedInterval (885586385 / 1000000000000) (885586914 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 302 12 (3794952985099213 / 4000000000000)) (orderedInterval (17893291788 / 1000000000000) (17893291789 / 1000000000000), orderedInterval (18721491154 / 1000000000000) (18721491156 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 223 12 (2795345192676967 / 4000000000000)) (orderedInterval (24614554406 / 1000000000000) (24614576300 / 1000000000000), orderedInterval (-17484571440 / 1000000000000) (-17484549546 / 1000000000000))) = true
  rfl'

theorem compactCertificate608_stateChecks3 :
    compactCertificate608.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 341 12 (4288778380844041 / 4000000000000)) (orderedInterval (-24173960123 / 1000000000000) (-24173918205 / 1000000000000), orderedInterval (3073036787 / 1000000000000) (3073078705 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 197 12 (2476127352674689 / 4000000000000)) (orderedInterval (-25577653758 / 1000000000000) (-25577653757 / 1000000000000), orderedInterval (-19323475112 / 1000000000000) (-19323475111 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 350 12 (4393931439205301 / 4000000000000)) (orderedInterval (-6867431523 / 1000000000000) (-6867431522 / 1000000000000), orderedInterval (23076552158 / 1000000000000) (23076552159 / 1000000000000))) = true
  rfl'

theorem compactCertificate608_stateChecks4 :
    compactCertificate608.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 327 12 (4105380716300969 / 4000000000000)) (orderedInterval (4221953450 / 1000000000000) (4221953451 / 1000000000000), orderedInterval (-24546987114 / 1000000000000) (-24546987113 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 233 12 (2929793394307577 / 4000000000000)) (orderedInterval (-27906990679 / 1000000000000) (-27906990651 / 1000000000000), orderedInterval (-9487078679 / 1000000000000) (-9487078651 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 264 12 (3322073448916383 / 4000000000000)) (orderedInterval (25985320563 / 1000000000000) (25985423233 / 1000000000000), orderedInterval (-9570448808 / 1000000000000) (-9570346139 / 1000000000000))) = true
  rfl'

theorem compactCertificate608_stateChecks5 :
    compactCertificate608.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 221 12 (2769598498138927 / 4000000000000)) (orderedInterval (27120814208 / 1000000000000) (27120902496 / 1000000000000), orderedInterval (-13580551301 / 1000000000000) (-13580463013 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 195 12 (2447024266601467 / 4000000000000)) (orderedInterval (2233983654 / 1000000000000) (2233983655 / 1000000000000), orderedInterval (-32183386298 / 1000000000000) (-32183386297 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 282 12 (709243009813233 / 800000000000)) (orderedInterval (26450933630 / 1000000000000) (26450934441 / 1000000000000), orderedInterval (4278290587 / 1000000000000) (4278291399 / 1000000000000))) = true
  rfl'

theorem compactCertificate608_stateChecks6 :
    compactCertificate608.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 156 12 (1961803490558051 / 4000000000000)) (orderedInterval (32849235385 / 1000000000000) (32849235386 / 1000000000000), orderedInterval (14763704643 / 1000000000000) (14763704644 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 132 12 (1663042545324811 / 4000000000000)) (orderedInterval (37555499564 / 1000000000000) (37555507569 / 1000000000000), orderedInterval (-11036085525 / 1000000000000) (-11036077520 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 83 12 (1040654807323033 / 4000000000000)) (orderedInterval (-9654418110 / 1000000000000) (-9654418109 / 1000000000000), orderedInterval (-48497353135 / 1000000000000) (-48497353134 / 1000000000000))) = true
  rfl'

theorem compactCertificate608_stateChecks7 :
    compactCertificate608.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (559667616439911 / 4000000000000)) (orderedInterval (41901350959 / 1000000000000) (41901372729 / 1000000000000), orderedInterval (-53010573284 / 1000000000000) (-53010551514 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 121 12 (1519606449492733 / 4000000000000)) (orderedInterval (-21535064390 / 1000000000000) (-21535064389 / 1000000000000), orderedInterval (-34785314140 / 1000000000000) (-34785314139 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 165 12 (2074892691630941 / 4000000000000)) (orderedInterval (-31912367237 / 1000000000000) (-31912367235 / 1000000000000), orderedInterval (-14422016024 / 1000000000000) (-14422016023 / 1000000000000))) = true
  rfl'

theorem compactCertificate608_stateChecks8 :
    compactCertificate608.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (877345192676967 / 4000000000000)) (orderedInterval (11211765141 / 1000000000000) (11211765142 / 1000000000000), orderedInterval (52669657225 / 1000000000000) (52669657226 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 284 12 (3566359499483207 / 4000000000000)) (orderedInterval (4331542288 / 1000000000000) (4331542289 / 1000000000000), orderedInterval (26365457434 / 1000000000000) (26365457435 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 190 12 (2382162866063113 / 4000000000000)) (orderedInterval (-17827399710 / 1000000000000) (-17827399030 / 1000000000000), orderedInterval (27422296898 / 1000000000000) (27422297579 / 1000000000000))) = true
  rfl'

theorem compactCertificate608_states : ∀ j,
    BesselStateValid (compactCertificate608.point j) (compactCertificate608.state j) :=
  compactCertificate608.statesValid_of_checks3 compactCertificate608_stateChecks0
    compactCertificate608_stateChecks1 compactCertificate608_stateChecks2
    compactCertificate608_stateChecks3 compactCertificate608_stateChecks4
    compactCertificate608_stateChecks5 compactCertificate608_stateChecks6
    compactCertificate608_stateChecks7 compactCertificate608_stateChecks8

theorem compactCertificate608_chunkChecks0_0 :
    compactCertificate608.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (959 / 2) 0 (IntervalRat.scale (959 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (13465855384 / 1000000000000) (13465855494 / 1000000000000), orderedInterval (-33871765211 / 1000000000000) (-33871765101 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1412790119037059 / 4000000000000) 0 (IntervalRat.scale (959 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (36118403329 / 1000000000000) (36118476030 / 1000000000000), orderedInterval (-22364934423 / 1000000000000) (-22364861722 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (456867296891747 / 800000000000) 0 (IntervalRat.scale (959 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (3314545196 / 1000000000000) (3314545197 / 1000000000000), orderedInterval (33220143830 / 1000000000000) (33220143831 / 1000000000000)))) (orderedInterval (5868448398 / 1000000000000) (5868449153 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (412248633186313 / 4000000000000) 0 (IntervalRat.scale (959 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-13589849077 / 1000000000000) (-13589849076 / 1000000000000), orderedInterval (-77344865740 / 1000000000000) (-77344865739 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (1107357816305461 / 4000000000000) 0 (IntervalRat.scale (959 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (44045401983 / 1000000000000) (44045401984 / 1000000000000), orderedInterval (18883549069 / 1000000000000) (18883549071 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (3006691883042337 / 4000000000000) 0 (IntervalRat.scale (959 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29070370557 / 1000000000000) (-29070366604 / 1000000000000), orderedInterval (1379718426 / 1000000000000) (1379722379 / 1000000000000)))) (orderedInterval (3822216654 / 1000000000000) (3822216993 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (2214715632611881 / 4000000000000) 0 (IntervalRat.scale (959 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (33896307622 / 1000000000000) (33896308150 / 1000000000000), orderedInterval (885586385 / 1000000000000) (885586914 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3794952985099213 / 4000000000000) 0 (IntervalRat.scale (959 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (17893291788 / 1000000000000) (17893291789 / 1000000000000), orderedInterval (18721491154 / 1000000000000) (18721491156 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2795345192676967 / 4000000000000) 0 (IntervalRat.scale (959 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (24614554406 / 1000000000000) (24614576300 / 1000000000000), orderedInterval (-17484571440 / 1000000000000) (-17484549546 / 1000000000000)))) (orderedInterval (42984492 / 1000000000000) (42985048 / 1000000000000))) = true
  rfl'

theorem compactCertificate608_chunkChecks0_1 :
    compactCertificate608.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (4288778380844041 / 4000000000000) 0 (IntervalRat.scale (959 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-24173960123 / 1000000000000) (-24173918205 / 1000000000000), orderedInterval (3073036787 / 1000000000000) (3073078705 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2476127352674689 / 4000000000000) 0 (IntervalRat.scale (959 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-25577653758 / 1000000000000) (-25577653757 / 1000000000000), orderedInterval (-19323475112 / 1000000000000) (-19323475111 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (4393931439205301 / 4000000000000) 0 (IntervalRat.scale (959 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-6867431523 / 1000000000000) (-6867431522 / 1000000000000), orderedInterval (23076552158 / 1000000000000) (23076552159 / 1000000000000)))) (orderedInterval (1424073775 / 1000000000000) (1424081414 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (4105380716300969 / 4000000000000) 0 (IntervalRat.scale (959 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (4221953450 / 1000000000000) (4221953451 / 1000000000000), orderedInterval (-24546987114 / 1000000000000) (-24546987113 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2929793394307577 / 4000000000000) 0 (IntervalRat.scale (959 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-27906990679 / 1000000000000) (-27906990651 / 1000000000000), orderedInterval (-9487078679 / 1000000000000) (-9487078651 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (3322073448916383 / 4000000000000) 0 (IntervalRat.scale (959 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (25985320563 / 1000000000000) (25985423233 / 1000000000000), orderedInterval (-9570448808 / 1000000000000) (-9570346139 / 1000000000000)))) (orderedInterval (-2846685547 / 1000000000000) (-2846684967 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2769598498138927 / 4000000000000) 0 (IntervalRat.scale (959 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (27120814208 / 1000000000000) (27120902496 / 1000000000000), orderedInterval (-13580551301 / 1000000000000) (-13580463013 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2447024266601467 / 4000000000000) 0 (IntervalRat.scale (959 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (2233983654 / 1000000000000) (2233983655 / 1000000000000), orderedInterval (-32183386298 / 1000000000000) (-32183386297 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (709243009813233 / 800000000000) 0 (IntervalRat.scale (959 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (26450933630 / 1000000000000) (26450934441 / 1000000000000), orderedInterval (4278290587 / 1000000000000) (4278291399 / 1000000000000)))) (orderedInterval (862587111 / 1000000000000) (862588197 / 1000000000000))) = true
  rfl'

theorem compactCertificate608_chunkChecks0_2 :
    compactCertificate608.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1961803490558051 / 4000000000000) 0 (IntervalRat.scale (959 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (32849235385 / 1000000000000) (32849235386 / 1000000000000), orderedInterval (14763704643 / 1000000000000) (14763704644 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1663042545324811 / 4000000000000) 0 (IntervalRat.scale (959 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (37555499564 / 1000000000000) (37555507569 / 1000000000000), orderedInterval (-11036085525 / 1000000000000) (-11036077520 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (1040654807323033 / 4000000000000) 0 (IntervalRat.scale (959 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-9654418110 / 1000000000000) (-9654418109 / 1000000000000), orderedInterval (-48497353135 / 1000000000000) (-48497353134 / 1000000000000)))) (orderedInterval (-7692286798 / 1000000000000) (-7692286224 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (559667616439911 / 4000000000000) 0 (IntervalRat.scale (959 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (41901350959 / 1000000000000) (41901372729 / 1000000000000), orderedInterval (-53010573284 / 1000000000000) (-53010551514 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1519606449492733 / 4000000000000) 0 (IntervalRat.scale (959 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-21535064390 / 1000000000000) (-21535064389 / 1000000000000), orderedInterval (-34785314140 / 1000000000000) (-34785314139 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (2074892691630941 / 4000000000000) 0 (IntervalRat.scale (959 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-31912367237 / 1000000000000) (-31912367235 / 1000000000000), orderedInterval (-14422016024 / 1000000000000) (-14422016023 / 1000000000000)))) (orderedInterval (2160577019 / 1000000000000) (2160577479 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (877345192676967 / 4000000000000) 0 (IntervalRat.scale (959 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (11211765141 / 1000000000000) (11211765142 / 1000000000000), orderedInterval (52669657225 / 1000000000000) (52669657226 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3566359499483207 / 4000000000000) 0 (IntervalRat.scale (959 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (4331542288 / 1000000000000) (4331542289 / 1000000000000), orderedInterval (26365457434 / 1000000000000) (26365457435 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2382162866063113 / 4000000000000) 0 (IntervalRat.scale (959 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-17827399710 / 1000000000000) (-17827399030 / 1000000000000), orderedInterval (27422296898 / 1000000000000) (27422297579 / 1000000000000)))) (orderedInterval (3059885857 / 1000000000000) (3059886118 / 1000000000000))) = true
  rfl'

theorem compactCertificate608_chunkChecks0 :
    compactCertificate608.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate608.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate608_chunkChecks0_0
    compactCertificate608_chunkChecks0_1 compactCertificate608_chunkChecks0_2

theorem compactCertificate608_chunkChecks1_0 :
    compactCertificate608.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (959 / 2) 1 (IntervalRat.scale (959 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (13465855384 / 1000000000000) (13465855494 / 1000000000000), orderedInterval (-33871765211 / 1000000000000) (-33871765101 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1412790119037059 / 4000000000000) 1 (IntervalRat.scale (959 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (36118403329 / 1000000000000) (36118476030 / 1000000000000), orderedInterval (-22364934423 / 1000000000000) (-22364861722 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (456867296891747 / 800000000000) 1 (IntervalRat.scale (959 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (3314545196 / 1000000000000) (3314545197 / 1000000000000), orderedInterval (33220143830 / 1000000000000) (33220143831 / 1000000000000)))) (orderedInterval (-11257357887 / 1000000000000) (-11257357307 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (412248633186313 / 4000000000000) 1 (IntervalRat.scale (959 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-13589849077 / 1000000000000) (-13589849076 / 1000000000000), orderedInterval (-77344865740 / 1000000000000) (-77344865739 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (1107357816305461 / 4000000000000) 1 (IntervalRat.scale (959 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (44045401983 / 1000000000000) (44045401984 / 1000000000000), orderedInterval (18883549069 / 1000000000000) (18883549071 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (3006691883042337 / 4000000000000) 1 (IntervalRat.scale (959 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29070370557 / 1000000000000) (-29070366604 / 1000000000000), orderedInterval (1379718426 / 1000000000000) (1379722379 / 1000000000000)))) (orderedInterval (424669559 / 1000000000000) (424670065 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (2214715632611881 / 4000000000000) 1 (IntervalRat.scale (959 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (33896307622 / 1000000000000) (33896308150 / 1000000000000), orderedInterval (885586385 / 1000000000000) (885586914 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3794952985099213 / 4000000000000) 1 (IntervalRat.scale (959 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (17893291788 / 1000000000000) (17893291789 / 1000000000000), orderedInterval (18721491154 / 1000000000000) (18721491156 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2795345192676967 / 4000000000000) 1 (IntervalRat.scale (959 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (24614554406 / 1000000000000) (24614576300 / 1000000000000), orderedInterval (-17484571440 / 1000000000000) (-17484549546 / 1000000000000)))) (orderedInterval (-1758394991 / 1000000000000) (-1758394172 / 1000000000000))) = true
  rfl'

theorem compactCertificate608_chunkChecks1_1 :
    compactCertificate608.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (4288778380844041 / 4000000000000) 1 (IntervalRat.scale (959 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-24173960123 / 1000000000000) (-24173918205 / 1000000000000), orderedInterval (3073036787 / 1000000000000) (3073078705 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2476127352674689 / 4000000000000) 1 (IntervalRat.scale (959 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-25577653758 / 1000000000000) (-25577653757 / 1000000000000), orderedInterval (-19323475112 / 1000000000000) (-19323475111 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (4393931439205301 / 4000000000000) 1 (IntervalRat.scale (959 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-6867431523 / 1000000000000) (-6867431522 / 1000000000000), orderedInterval (23076552158 / 1000000000000) (23076552159 / 1000000000000)))) (orderedInterval (4445865429 / 1000000000000) (4445882478 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (4105380716300969 / 4000000000000) 1 (IntervalRat.scale (959 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (4221953450 / 1000000000000) (4221953451 / 1000000000000), orderedInterval (-24546987114 / 1000000000000) (-24546987113 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2929793394307577 / 4000000000000) 1 (IntervalRat.scale (959 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-27906990679 / 1000000000000) (-27906990651 / 1000000000000), orderedInterval (-9487078679 / 1000000000000) (-9487078651 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (3322073448916383 / 4000000000000) 1 (IntervalRat.scale (959 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (25985320563 / 1000000000000) (25985423233 / 1000000000000), orderedInterval (-9570448808 / 1000000000000) (-9570346139 / 1000000000000)))) (orderedInterval (-337958451 / 1000000000000) (-337957454 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2769598498138927 / 4000000000000) 1 (IntervalRat.scale (959 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (27120814208 / 1000000000000) (27120902496 / 1000000000000), orderedInterval (-13580551301 / 1000000000000) (-13580463013 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2447024266601467 / 4000000000000) 1 (IntervalRat.scale (959 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (2233983654 / 1000000000000) (2233983655 / 1000000000000), orderedInterval (-32183386298 / 1000000000000) (-32183386297 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (709243009813233 / 800000000000) 1 (IntervalRat.scale (959 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (26450933630 / 1000000000000) (26450934441 / 1000000000000), orderedInterval (4278290587 / 1000000000000) (4278291399 / 1000000000000)))) (orderedInterval (2325818708 / 1000000000000) (2325820286 / 1000000000000))) = true
  rfl'

theorem compactCertificate608_chunkChecks1_2 :
    compactCertificate608.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1961803490558051 / 4000000000000) 1 (IntervalRat.scale (959 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (32849235385 / 1000000000000) (32849235386 / 1000000000000), orderedInterval (14763704643 / 1000000000000) (14763704644 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1663042545324811 / 4000000000000) 1 (IntervalRat.scale (959 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (37555499564 / 1000000000000) (37555507569 / 1000000000000), orderedInterval (-11036085525 / 1000000000000) (-11036077520 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (1040654807323033 / 4000000000000) 1 (IntervalRat.scale (959 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-9654418110 / 1000000000000) (-9654418109 / 1000000000000), orderedInterval (-48497353135 / 1000000000000) (-48497353134 / 1000000000000)))) (orderedInterval (-2729546152 / 1000000000000) (-2729545647 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (559667616439911 / 4000000000000) 1 (IntervalRat.scale (959 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (41901350959 / 1000000000000) (41901372729 / 1000000000000), orderedInterval (-53010573284 / 1000000000000) (-53010551514 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1519606449492733 / 4000000000000) 1 (IntervalRat.scale (959 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-21535064390 / 1000000000000) (-21535064389 / 1000000000000), orderedInterval (-34785314140 / 1000000000000) (-34785314139 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (2074892691630941 / 4000000000000) 1 (IntervalRat.scale (959 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-31912367237 / 1000000000000) (-31912367235 / 1000000000000), orderedInterval (-14422016024 / 1000000000000) (-14422016023 / 1000000000000)))) (orderedInterval (2106573288 / 1000000000000) (2106573457 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (877345192676967 / 4000000000000) 1 (IntervalRat.scale (959 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (11211765141 / 1000000000000) (11211765142 / 1000000000000), orderedInterval (52669657225 / 1000000000000) (52669657226 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3566359499483207 / 4000000000000) 1 (IntervalRat.scale (959 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (4331542288 / 1000000000000) (4331542289 / 1000000000000), orderedInterval (26365457434 / 1000000000000) (26365457435 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2382162866063113 / 4000000000000) 1 (IntervalRat.scale (959 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-17827399710 / 1000000000000) (-17827399030 / 1000000000000), orderedInterval (27422296898 / 1000000000000) (27422297579 / 1000000000000)))) (orderedInterval (-10235726761 / 1000000000000) (-10235726416 / 1000000000000))) = true
  rfl'

theorem compactCertificate608_chunkChecks1 :
    compactCertificate608.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate608.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate608_chunkChecks1_0
    compactCertificate608_chunkChecks1_1 compactCertificate608_chunkChecks1_2

theorem compactCertificate608_chunkChecks2_0 :
    compactCertificate608.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (959 / 2) 2 (IntervalRat.scale (959 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (13465855384 / 1000000000000) (13465855494 / 1000000000000), orderedInterval (-33871765211 / 1000000000000) (-33871765101 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1412790119037059 / 4000000000000) 2 (IntervalRat.scale (959 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (36118403329 / 1000000000000) (36118476030 / 1000000000000), orderedInterval (-22364934423 / 1000000000000) (-22364861722 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (456867296891747 / 800000000000) 2 (IntervalRat.scale (959 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (3314545196 / 1000000000000) (3314545197 / 1000000000000), orderedInterval (33220143830 / 1000000000000) (33220143831 / 1000000000000)))) (orderedInterval (-5772417622 / 1000000000000) (-5772417167 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (412248633186313 / 4000000000000) 2 (IntervalRat.scale (959 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-13589849077 / 1000000000000) (-13589849076 / 1000000000000), orderedInterval (-77344865740 / 1000000000000) (-77344865739 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (1107357816305461 / 4000000000000) 2 (IntervalRat.scale (959 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (44045401983 / 1000000000000) (44045401984 / 1000000000000), orderedInterval (18883549069 / 1000000000000) (18883549071 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (3006691883042337 / 4000000000000) 2 (IntervalRat.scale (959 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29070370557 / 1000000000000) (-29070366604 / 1000000000000), orderedInterval (1379718426 / 1000000000000) (1379722379 / 1000000000000)))) (orderedInterval (-5622279571 / 1000000000000) (-5622278788 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (2214715632611881 / 4000000000000) 2 (IntervalRat.scale (959 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (33896307622 / 1000000000000) (33896308150 / 1000000000000), orderedInterval (885586385 / 1000000000000) (885586914 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3794952985099213 / 4000000000000) 2 (IntervalRat.scale (959 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (17893291788 / 1000000000000) (17893291789 / 1000000000000), orderedInterval (18721491154 / 1000000000000) (18721491156 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2795345192676967 / 4000000000000) 2 (IntervalRat.scale (959 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (24614554406 / 1000000000000) (24614576300 / 1000000000000), orderedInterval (-17484571440 / 1000000000000) (-17484549546 / 1000000000000)))) (orderedInterval (900684813 / 1000000000000) (900686022 / 1000000000000))) = true
  rfl'

theorem compactCertificate608_chunkChecks2_1 :
    compactCertificate608.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (4288778380844041 / 4000000000000) 2 (IntervalRat.scale (959 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-24173960123 / 1000000000000) (-24173918205 / 1000000000000), orderedInterval (3073036787 / 1000000000000) (3073078705 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2476127352674689 / 4000000000000) 2 (IntervalRat.scale (959 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-25577653758 / 1000000000000) (-25577653757 / 1000000000000), orderedInterval (-19323475112 / 1000000000000) (-19323475111 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (4393931439205301 / 4000000000000) 2 (IntervalRat.scale (959 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-6867431523 / 1000000000000) (-6867431522 / 1000000000000), orderedInterval (23076552158 / 1000000000000) (23076552159 / 1000000000000)))) (orderedInterval (-13204365747 / 1000000000000) (-13204327625 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (4105380716300969 / 4000000000000) 2 (IntervalRat.scale (959 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (4221953450 / 1000000000000) (4221953451 / 1000000000000), orderedInterval (-24546987114 / 1000000000000) (-24546987113 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2929793394307577 / 4000000000000) 2 (IntervalRat.scale (959 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-27906990679 / 1000000000000) (-27906990651 / 1000000000000), orderedInterval (-9487078679 / 1000000000000) (-9487078651 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (3322073448916383 / 4000000000000) 2 (IntervalRat.scale (959 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (25985320563 / 1000000000000) (25985423233 / 1000000000000), orderedInterval (-9570448808 / 1000000000000) (-9570346139 / 1000000000000)))) (orderedInterval (6901992108 / 1000000000000) (6901993828 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2769598498138927 / 4000000000000) 2 (IntervalRat.scale (959 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (27120814208 / 1000000000000) (27120902496 / 1000000000000), orderedInterval (-13580551301 / 1000000000000) (-13580463013 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2447024266601467 / 4000000000000) 2 (IntervalRat.scale (959 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (2233983654 / 1000000000000) (2233983655 / 1000000000000), orderedInterval (-32183386298 / 1000000000000) (-32183386297 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (709243009813233 / 800000000000) 2 (IntervalRat.scale (959 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (26450933630 / 1000000000000) (26450934441 / 1000000000000), orderedInterval (4278290587 / 1000000000000) (4278291399 / 1000000000000)))) (orderedInterval (-2764949591 / 1000000000000) (-2764947292 / 1000000000000))) = true
  rfl'

theorem compactCertificate608_chunkChecks2_2 :
    compactCertificate608.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1961803490558051 / 4000000000000) 2 (IntervalRat.scale (959 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (32849235385 / 1000000000000) (32849235386 / 1000000000000), orderedInterval (14763704643 / 1000000000000) (14763704644 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1663042545324811 / 4000000000000) 2 (IntervalRat.scale (959 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (37555499564 / 1000000000000) (37555507569 / 1000000000000), orderedInterval (-11036085525 / 1000000000000) (-11036077520 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (1040654807323033 / 4000000000000) 2 (IntervalRat.scale (959 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-9654418110 / 1000000000000) (-9654418109 / 1000000000000), orderedInterval (-48497353135 / 1000000000000) (-48497353134 / 1000000000000)))) (orderedInterval (7191291920 / 1000000000000) (7191292368 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (559667616439911 / 4000000000000) 2 (IntervalRat.scale (959 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (41901350959 / 1000000000000) (41901372729 / 1000000000000), orderedInterval (-53010573284 / 1000000000000) (-53010551514 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1519606449492733 / 4000000000000) 2 (IntervalRat.scale (959 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-21535064390 / 1000000000000) (-21535064389 / 1000000000000), orderedInterval (-34785314140 / 1000000000000) (-34785314139 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (2074892691630941 / 4000000000000) 2 (IntervalRat.scale (959 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-31912367237 / 1000000000000) (-31912367235 / 1000000000000), orderedInterval (-14422016024 / 1000000000000) (-14422016023 / 1000000000000)))) (orderedInterval (-3107409590 / 1000000000000) (-3107409504 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (877345192676967 / 4000000000000) 2 (IntervalRat.scale (959 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (11211765141 / 1000000000000) (11211765142 / 1000000000000), orderedInterval (52669657225 / 1000000000000) (52669657226 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3566359499483207 / 4000000000000) 2 (IntervalRat.scale (959 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (4331542288 / 1000000000000) (4331542289 / 1000000000000), orderedInterval (26365457434 / 1000000000000) (26365457435 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2382162866063113 / 4000000000000) 2 (IntervalRat.scale (959 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-17827399710 / 1000000000000) (-17827399030 / 1000000000000), orderedInterval (27422296898 / 1000000000000) (27422297579 / 1000000000000)))) (orderedInterval (-3933464670 / 1000000000000) (-3933464197 / 1000000000000))) = true
  rfl'

theorem compactCertificate608_chunkChecks2 :
    compactCertificate608.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate608.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate608_chunkChecks2_0
    compactCertificate608_chunkChecks2_1 compactCertificate608_chunkChecks2_2

theorem compactCertificate608_chunkChecks3_0 :
    compactCertificate608.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (959 / 2) 3 (IntervalRat.scale (959 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (13465855384 / 1000000000000) (13465855494 / 1000000000000), orderedInterval (-33871765211 / 1000000000000) (-33871765101 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1412790119037059 / 4000000000000) 3 (IntervalRat.scale (959 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (36118403329 / 1000000000000) (36118476030 / 1000000000000), orderedInterval (-22364934423 / 1000000000000) (-22364861722 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (456867296891747 / 800000000000) 3 (IntervalRat.scale (959 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (3314545196 / 1000000000000) (3314545197 / 1000000000000), orderedInterval (33220143830 / 1000000000000) (33220143831 / 1000000000000)))) (orderedInterval (10227534584 / 1000000000000) (10227534950 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (412248633186313 / 4000000000000) 3 (IntervalRat.scale (959 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-13589849077 / 1000000000000) (-13589849076 / 1000000000000), orderedInterval (-77344865740 / 1000000000000) (-77344865739 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (1107357816305461 / 4000000000000) 3 (IntervalRat.scale (959 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (44045401983 / 1000000000000) (44045401984 / 1000000000000), orderedInterval (18883549069 / 1000000000000) (18883549071 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (3006691883042337 / 4000000000000) 3 (IntervalRat.scale (959 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29070370557 / 1000000000000) (-29070366604 / 1000000000000), orderedInterval (1379718426 / 1000000000000) (1379722379 / 1000000000000)))) (orderedInterval (248554498 / 1000000000000) (248555718 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (2214715632611881 / 4000000000000) 3 (IntervalRat.scale (959 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (33896307622 / 1000000000000) (33896308150 / 1000000000000), orderedInterval (885586385 / 1000000000000) (885586914 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3794952985099213 / 4000000000000) 3 (IntervalRat.scale (959 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (17893291788 / 1000000000000) (17893291789 / 1000000000000), orderedInterval (18721491154 / 1000000000000) (18721491156 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2795345192676967 / 4000000000000) 3 (IntervalRat.scale (959 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (24614554406 / 1000000000000) (24614576300 / 1000000000000), orderedInterval (-17484571440 / 1000000000000) (-17484549546 / 1000000000000)))) (orderedInterval (5779111848 / 1000000000000) (5779113641 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate608_chunkChecks3_1 :
    compactCertificate608.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (4288778380844041 / 4000000000000) 3 (IntervalRat.scale (959 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-24173960123 / 1000000000000) (-24173918205 / 1000000000000), orderedInterval (3073036787 / 1000000000000) (3073078705 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2476127352674689 / 4000000000000) 3 (IntervalRat.scale (959 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-25577653758 / 1000000000000) (-25577653757 / 1000000000000), orderedInterval (-19323475112 / 1000000000000) (-19323475111 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (4393931439205301 / 4000000000000) 3 (IntervalRat.scale (959 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-6867431523 / 1000000000000) (-6867431522 / 1000000000000), orderedInterval (23076552158 / 1000000000000) (23076552159 / 1000000000000)))) (orderedInterval (-30228134997 / 1000000000000) (-30228049793 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (4105380716300969 / 4000000000000) 3 (IntervalRat.scale (959 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (4221953450 / 1000000000000) (4221953451 / 1000000000000), orderedInterval (-24546987114 / 1000000000000) (-24546987113 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2929793394307577 / 4000000000000) 3 (IntervalRat.scale (959 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-27906990679 / 1000000000000) (-27906990651 / 1000000000000), orderedInterval (-9487078679 / 1000000000000) (-9487078651 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (3322073448916383 / 4000000000000) 3 (IntervalRat.scale (959 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (25985320563 / 1000000000000) (25985423233 / 1000000000000), orderedInterval (-9570448808 / 1000000000000) (-9570346139 / 1000000000000)))) (orderedInterval (-1414242761 / 1000000000000) (-1414239788 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2769598498138927 / 4000000000000) 3 (IntervalRat.scale (959 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (27120814208 / 1000000000000) (27120902496 / 1000000000000), orderedInterval (-13580551301 / 1000000000000) (-13580463013 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2447024266601467 / 4000000000000) 3 (IntervalRat.scale (959 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (2233983654 / 1000000000000) (2233983655 / 1000000000000), orderedInterval (-32183386298 / 1000000000000) (-32183386297 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (709243009813233 / 800000000000) 3 (IntervalRat.scale (959 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (26450933630 / 1000000000000) (26450934441 / 1000000000000), orderedInterval (4278290587 / 1000000000000) (4278291399 / 1000000000000)))) (orderedInterval (-4039105606 / 1000000000000) (-4039102248 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate608_chunkChecks3_2 :
    compactCertificate608.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1961803490558051 / 4000000000000) 3 (IntervalRat.scale (959 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (32849235385 / 1000000000000) (32849235386 / 1000000000000), orderedInterval (14763704643 / 1000000000000) (14763704644 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1663042545324811 / 4000000000000) 3 (IntervalRat.scale (959 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (37555499564 / 1000000000000) (37555507569 / 1000000000000), orderedInterval (-11036085525 / 1000000000000) (-11036077520 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (1040654807323033 / 4000000000000) 3 (IntervalRat.scale (959 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-9654418110 / 1000000000000) (-9654418109 / 1000000000000), orderedInterval (-48497353135 / 1000000000000) (-48497353134 / 1000000000000)))) (orderedInterval (2356045780 / 1000000000000) (2356046180 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (559667616439911 / 4000000000000) 3 (IntervalRat.scale (959 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (41901350959 / 1000000000000) (41901372729 / 1000000000000), orderedInterval (-53010573284 / 1000000000000) (-53010551514 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1519606449492733 / 4000000000000) 3 (IntervalRat.scale (959 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-21535064390 / 1000000000000) (-21535064389 / 1000000000000), orderedInterval (-34785314140 / 1000000000000) (-34785314139 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (2074892691630941 / 4000000000000) 3 (IntervalRat.scale (959 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-31912367237 / 1000000000000) (-31912367235 / 1000000000000), orderedInterval (-14422016024 / 1000000000000) (-14422016023 / 1000000000000)))) (orderedInterval (-1809627697 / 1000000000000) (-1809627634 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (877345192676967 / 4000000000000) 3 (IntervalRat.scale (959 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (11211765141 / 1000000000000) (11211765142 / 1000000000000), orderedInterval (52669657225 / 1000000000000) (52669657226 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3566359499483207 / 4000000000000) 3 (IntervalRat.scale (959 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (4331542288 / 1000000000000) (4331542289 / 1000000000000), orderedInterval (26365457434 / 1000000000000) (26365457435 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2382162866063113 / 4000000000000) 3 (IntervalRat.scale (959 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-17827399710 / 1000000000000) (-17827399030 / 1000000000000), orderedInterval (27422296898 / 1000000000000) (27422297579 / 1000000000000)))) (orderedInterval (23632712449 / 1000000000000) (23632713120 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate608_chunkChecks3 :
    compactCertificate608.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate608.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate608_chunkChecks3_0
    compactCertificate608_chunkChecks3_1 compactCertificate608_chunkChecks3_2

theorem compactCertificate608_chunkChecks4_0 :
    compactCertificate608.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (959 / 2) 4 (IntervalRat.scale (959 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (13465855384 / 1000000000000) (13465855494 / 1000000000000), orderedInterval (-33871765211 / 1000000000000) (-33871765101 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1412790119037059 / 4000000000000) 4 (IntervalRat.scale (959 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (36118403329 / 1000000000000) (36118476030 / 1000000000000), orderedInterval (-22364934423 / 1000000000000) (-22364861722 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (456867296891747 / 800000000000) 4 (IntervalRat.scale (959 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (3314545196 / 1000000000000) (3314545197 / 1000000000000), orderedInterval (33220143830 / 1000000000000) (33220143831 / 1000000000000)))) (orderedInterval (5785138621 / 1000000000000) (5785138924 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (412248633186313 / 4000000000000) 4 (IntervalRat.scale (959 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-13589849077 / 1000000000000) (-13589849076 / 1000000000000), orderedInterval (-77344865740 / 1000000000000) (-77344865739 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (1107357816305461 / 4000000000000) 4 (IntervalRat.scale (959 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (44045401983 / 1000000000000) (44045401984 / 1000000000000), orderedInterval (18883549069 / 1000000000000) (18883549071 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (3006691883042337 / 4000000000000) 4 (IntervalRat.scale (959 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29070370557 / 1000000000000) (-29070366604 / 1000000000000), orderedInterval (1379718426 / 1000000000000) (1379722379 / 1000000000000)))) (orderedInterval (12658040986 / 1000000000000) (12658042896 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (2214715632611881 / 4000000000000) 4 (IntervalRat.scale (959 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (33896307622 / 1000000000000) (33896308150 / 1000000000000), orderedInterval (885586385 / 1000000000000) (885586914 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3794952985099213 / 4000000000000) 4 (IntervalRat.scale (959 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (17893291788 / 1000000000000) (17893291789 / 1000000000000), orderedInterval (18721491154 / 1000000000000) (18721491156 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2795345192676967 / 4000000000000) 4 (IntervalRat.scale (959 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (24614554406 / 1000000000000) (24614576300 / 1000000000000), orderedInterval (-17484571440 / 1000000000000) (-17484549546 / 1000000000000)))) (orderedInterval (-5798589470 / 1000000000000) (-5798586796 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate608_chunkChecks4_1 :
    compactCertificate608.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (4288778380844041 / 4000000000000) 4 (IntervalRat.scale (959 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-24173960123 / 1000000000000) (-24173918205 / 1000000000000), orderedInterval (3073036787 / 1000000000000) (3073078705 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2476127352674689 / 4000000000000) 4 (IntervalRat.scale (959 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-25577653758 / 1000000000000) (-25577653757 / 1000000000000), orderedInterval (-19323475112 / 1000000000000) (-19323475111 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (4393931439205301 / 4000000000000) 4 (IntervalRat.scale (959 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-6867431523 / 1000000000000) (-6867431522 / 1000000000000), orderedInterval (23076552158 / 1000000000000) (23076552159 / 1000000000000)))) (orderedInterval (75358006805 / 1000000000000) (75358197471 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (4105380716300969 / 4000000000000) 4 (IntervalRat.scale (959 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (4221953450 / 1000000000000) (4221953451 / 1000000000000), orderedInterval (-24546987114 / 1000000000000) (-24546987113 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2929793394307577 / 4000000000000) 4 (IntervalRat.scale (959 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-27906990679 / 1000000000000) (-27906990651 / 1000000000000), orderedInterval (-9487078679 / 1000000000000) (-9487078651 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (3322073448916383 / 4000000000000) 4 (IntervalRat.scale (959 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (25985320563 / 1000000000000) (25985423233 / 1000000000000), orderedInterval (-9570448808 / 1000000000000) (-9570346139 / 1000000000000)))) (orderedInterval (-17145149014 / 1000000000000) (-17145143861 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2769598498138927 / 4000000000000) 4 (IntervalRat.scale (959 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (27120814208 / 1000000000000) (27120902496 / 1000000000000), orderedInterval (-13580551301 / 1000000000000) (-13580463013 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2447024266601467 / 4000000000000) 4 (IntervalRat.scale (959 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (2233983654 / 1000000000000) (2233983655 / 1000000000000), orderedInterval (-32183386298 / 1000000000000) (-32183386297 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (709243009813233 / 800000000000) 4 (IntervalRat.scale (959 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (26450933630 / 1000000000000) (26450934441 / 1000000000000), orderedInterval (4278290587 / 1000000000000) (4278291399 / 1000000000000)))) (orderedInterval (8954105986 / 1000000000000) (8954110916 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate608_chunkChecks4_2 :
    compactCertificate608.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1961803490558051 / 4000000000000) 4 (IntervalRat.scale (959 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (32849235385 / 1000000000000) (32849235386 / 1000000000000), orderedInterval (14763704643 / 1000000000000) (14763704644 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1663042545324811 / 4000000000000) 4 (IntervalRat.scale (959 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (37555499564 / 1000000000000) (37555507569 / 1000000000000), orderedInterval (-11036085525 / 1000000000000) (-11036077520 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (1040654807323033 / 4000000000000) 4 (IntervalRat.scale (959 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-9654418110 / 1000000000000) (-9654418109 / 1000000000000), orderedInterval (-48497353135 / 1000000000000) (-48497353134 / 1000000000000)))) (orderedInterval (-6987340253 / 1000000000000) (-6987339894 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (559667616439911 / 4000000000000) 4 (IntervalRat.scale (959 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (41901350959 / 1000000000000) (41901372729 / 1000000000000), orderedInterval (-53010573284 / 1000000000000) (-53010551514 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1519606449492733 / 4000000000000) 4 (IntervalRat.scale (959 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-21535064390 / 1000000000000) (-21535064389 / 1000000000000), orderedInterval (-34785314140 / 1000000000000) (-34785314139 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (2074892691630941 / 4000000000000) 4 (IntervalRat.scale (959 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-31912367237 / 1000000000000) (-31912367235 / 1000000000000), orderedInterval (-14422016024 / 1000000000000) (-14422016023 / 1000000000000)))) (orderedInterval (3544059589 / 1000000000000) (3544059647 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (877345192676967 / 4000000000000) 4 (IntervalRat.scale (959 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (11211765141 / 1000000000000) (11211765142 / 1000000000000), orderedInterval (52669657225 / 1000000000000) (52669657226 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3566359499483207 / 4000000000000) 4 (IntervalRat.scale (959 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (4331542288 / 1000000000000) (4331542289 / 1000000000000), orderedInterval (26365457434 / 1000000000000) (26365457435 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2382162866063113 / 4000000000000) 4 (IntervalRat.scale (959 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-17827399710 / 1000000000000) (-17827399030 / 1000000000000), orderedInterval (27422296898 / 1000000000000) (27422297579 / 1000000000000)))) (orderedInterval (3648792599 / 1000000000000) (3648793586 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate608_chunkChecks4 :
    compactCertificate608.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate608.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate608_chunkChecks4_0
    compactCertificate608_chunkChecks4_1 compactCertificate608_chunkChecks4_2

theorem compactCertificate608_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate608.chunkCheck r b = true :=
  compactCertificate608.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate608_chunkChecks0
    · exact compactCertificate608_chunkChecks1
    · exact compactCertificate608_chunkChecks2
    · exact compactCertificate608_chunkChecks3
    · exact compactCertificate608_chunkChecks4)

theorem compactCertificate608_coefficient0 :
    compactCertificate608.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate608_coefficient1 :
    compactCertificate608.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate608_coefficient2 :
    compactCertificate608.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate608_coefficient3 :
    compactCertificate608.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate608_coefficient4 :
    compactCertificate608.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate608_coefficients : ∀ r : Fin 5,
    compactCertificate608.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate608_coefficient0
  · exact compactCertificate608_coefficient1
  · exact compactCertificate608_coefficient2
  · exact compactCertificate608_coefficient3
  · exact compactCertificate608_coefficient4

theorem compactCertificate608_lower : (1 : ℚ) ≤ compactCertificate608.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate608, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate608_proves {t : ℝ} (ht : t ∈ compactCertificate608.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate608.proves compactCertificate608_states compactCertificate608_chunks
    compactCertificate608_coefficients compactCertificate608_lower ht

end Erdos232
