/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate399 : CompactCertificate where
  left := 270
  right := 271
  center := 541 / 2
  grid := fun i =>
    match i.val with
    | 0 => 86
    | 1 => 63
    | 2 => 103
    | 3 => 19
    | 4 => 50
    | 5 => 135
    | 6 => 99
    | 7 => 170
    | 8 => 126
    | 9 => 193
    | 10 => 111
    | 11 => 197
    | 12 => 184
    | 13 => 132
    | 14 => 149
    | 15 => 124
    | 16 => 110
    | 17 => 159
    | 18 => 88
    | 19 => 75
    | 20 => 47
    | 21 => 25
    | 22 => 68
    | 23 => 93
    | 24 => 39
    | 25 => 160
    | _ => 107
  point := fun i =>
    match i.val with
    | 0 => 541 / 2
    | 1 => 796996302814441 / 4000000000000
    | 2 => 257732229007753 / 800000000000
    | 3 => 232561533424187 / 4000000000000
    | 4 => 624692991263039 / 4000000000000
    | 5 => 1696162991372163 / 4000000000000
    | 6 => 1249385982526619 / 4000000000000
    | 7 => 2140844176161287 / 4000000000000
    | 8 => 1576936130592533 / 4000000000000
    | 9 => 2419425551654459 / 4000000000000
    | 10 => 1396855993531811 / 4000000000000
    | 11 => 2478745473003199 / 4000000000000
    | 12 => 2315965555285531 / 4000000000000
    | 13 => 1652782300646923 / 4000000000000
    | 14 => 1874078973789117 / 4000000000000
    | 15 => 1562411665790573 / 4000000000000
    | 16 => 1380438089918033 / 4000000000000
    | 17 => 400104763617267 / 800000000000
    | 18 => 1106710832525449 / 4000000000000
    | 19 => 938171029218689 / 4000000000000
    | 20 => 587063869407467 / 4000000000000
    | 21 => 315724901453589 / 4000000000000
    | 22 => 857254524687767 / 4000000000000
    | 23 => 1170507764517559 / 4000000000000
    | 24 => 494936130592533 / 4000000000000
    | 25 => 2011887892826293 / 4000000000000
    | _ => 1343847873347387 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (43408895893 / 1000000000000) (43408895894 / 1000000000000), orderedInterval (21579818083 / 1000000000000) (21579818084 / 1000000000000))
    | 1 => (orderedInterval (-48403048799 / 1000000000000) (-48403015496 / 1000000000000), orderedInterval (29314543321 / 1000000000000) (29314576624 / 1000000000000))
    | 2 => (orderedInterval (26323610996 / 1000000000000) (26323617132 / 1000000000000), orderedInterval (-35861713442 / 1000000000000) (-35861707306 / 1000000000000))
    | 3 => (orderedInterval (72589090712 / 1000000000000) (72589164723 / 1000000000000), orderedInterval (-75993560558 / 1000000000000) (-75993486546 / 1000000000000))
    | 4 => (orderedInterval (-7756445039 / 1000000000000) (-7756445011 / 1000000000000), orderedInterval (63398539614 / 1000000000000) (63398539642 / 1000000000000))
    | 5 => (orderedInterval (-25281250199 / 1000000000000) (-25281250198 / 1000000000000), orderedInterval (-29333023575 / 1000000000000) (-29333023574 / 1000000000000))
    | 6 => (orderedInterval (-38651956839 / 1000000000000) (-38651901263 / 1000000000000), orderedInterval (23390186872 / 1000000000000) (23390242447 / 1000000000000))
    | 7 => (orderedInterval (32342298779 / 1000000000000) (32342327014 / 1000000000000), orderedInterval (-12007233788 / 1000000000000) (-12007205552 / 1000000000000))
    | 8 => (orderedInterval (-29423779218 / 1000000000000) (-29423752276 / 1000000000000), orderedInterval (27406427298 / 1000000000000) (27406454241 / 1000000000000))
    | 9 => (orderedInterval (20545632291 / 1000000000000) (20545634595 / 1000000000000), orderedInterval (-25124572391 / 1000000000000) (-25124570087 / 1000000000000))
    | 10 => (orderedInterval (-40931577862 / 1000000000000) (-40931577859 / 1000000000000), orderedInterval (-12090961316 / 1000000000000) (-12090961313 / 1000000000000))
    | 11 => (orderedInterval (-32051129543 / 1000000000000) (-32051128347 / 1000000000000), orderedInterval (250722302 / 1000000000000) (250723499 / 1000000000000))
    | 12 => (orderedInterval (32773214343 / 1000000000000) (32773219151 / 1000000000000), orderedInterval (-5072928791 / 1000000000000) (-5072923983 / 1000000000000))
    | 13 => (orderedInterval (-25572683864 / 1000000000000) (-25572675546 / 1000000000000), orderedInterval (29809470636 / 1000000000000) (29809478954 / 1000000000000))
    | 14 => (orderedInterval (-34456715670 / 1000000000000) (-34456715668 / 1000000000000), orderedInterval (-13059937828 / 1000000000000) (-13059937826 / 1000000000000))
    | 15 => (orderedInterval (39017380014 / 1000000000000) (39017385441 / 1000000000000), orderedInterval (-10417273121 / 1000000000000) (-10417267694 / 1000000000000))
    | 16 => (orderedInterval (13484749279 / 1000000000000) (13484749280 / 1000000000000), orderedInterval (40758547748 / 1000000000000) (40758547749 / 1000000000000))
    | 17 => (orderedInterval (-35175943886 / 1000000000000) (-35175943832 / 1000000000000), orderedInterval (-5927930853 / 1000000000000) (-5927930799 / 1000000000000))
    | 18 => (orderedInterval (40428466788 / 1000000000000) (40428466789 / 1000000000000), orderedInterval (25743232698 / 1000000000000) (25743232699 / 1000000000000))
    | 19 => (orderedInterval (14988956503 / 1000000000000) (14988956686 / 1000000000000), orderedInterval (-49928224797 / 1000000000000) (-49928224614 / 1000000000000))
    | 20 => (orderedInterval (6859497402 / 1000000000000) (6859497425 / 1000000000000), orderedInterval (-65526227040 / 1000000000000) (-65526227017 / 1000000000000))
    | 21 => (orderedInterval (-82871957263 / 1000000000000) (-82871957262 / 1000000000000), orderedInterval (-34081771729 / 1000000000000) (-34081771728 / 1000000000000))
    | 22 => (orderedInterval (54226431490 / 1000000000000) (54226431507 / 1000000000000), orderedInterval (5349936886 / 1000000000000) (5349936903 / 1000000000000))
    | 23 => (orderedInterval (-44170987585 / 1000000000000) (-44170987584 / 1000000000000), orderedInterval (-14906350561 / 1000000000000) (-14906350559 / 1000000000000))
    | 24 => (orderedInterval (-65332624159 / 1000000000000) (-65332616675 / 1000000000000), orderedInterval (29872897733 / 1000000000000) (29872905218 / 1000000000000))
    | 25 => (orderedInterval (31743396790 / 1000000000000) (31743396792 / 1000000000000), orderedInterval (16033081927 / 1000000000000) (16033081928 / 1000000000000))
    | _ => (orderedInterval (-24456234822 / 1000000000000) (-24456234821 / 1000000000000), orderedInterval (-35974844613 / 1000000000000) (-35974844612 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (18299443696 / 1000000000000) (18299444387 / 1000000000000)
      | 1 => orderedInterval (726492661 / 1000000000000) (726493499 / 1000000000000)
      | 2 => orderedInterval (-1708681465 / 1000000000000) (-1708679927 / 1000000000000)
      | 3 => orderedInterval (-11239661257 / 1000000000000) (-11239660570 / 1000000000000)
      | 4 => orderedInterval (-2835513209 / 1000000000000) (-2835512303 / 1000000000000)
      | 5 => orderedInterval (-1221770685 / 1000000000000) (-1221770594 / 1000000000000)
      | 6 => orderedInterval (-7089267807 / 1000000000000) (-7089267728 / 1000000000000)
      | 7 => orderedInterval (3685227377 / 1000000000000) (3685227411 / 1000000000000)
      | _ => orderedInterval (1610822971 / 1000000000000) (1610823092 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (6248342775 / 1000000000000) (6248343455 / 1000000000000)
      | 1 => orderedInterval (4782569301 / 1000000000000) (4782569512 / 1000000000000)
      | 2 => orderedInterval (1698115023 / 1000000000000) (1698117722 / 1000000000000)
      | 3 => orderedInterval (8907677162 / 1000000000000) (8907678690 / 1000000000000)
      | 4 => orderedInterval (4616392533 / 1000000000000) (4616393973 / 1000000000000)
      | 5 => orderedInterval (-3430153553 / 1000000000000) (-3430153422 / 1000000000000)
      | 6 => orderedInterval (-2917295868 / 1000000000000) (-2917295796 / 1000000000000)
      | 7 => orderedInterval (1323327495 / 1000000000000) (1323327525 / 1000000000000)
      | _ => orderedInterval (6038931230 / 1000000000000) (6038931356 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-19175278043 / 1000000000000) (-19175277336 / 1000000000000)
      | 1 => orderedInterval (-4303471445 / 1000000000000) (-4303471355 / 1000000000000)
      | 2 => orderedInterval (5409520234 / 1000000000000) (5409525083 / 1000000000000)
      | 3 => orderedInterval (47187201673 / 1000000000000) (47187205094 / 1000000000000)
      | 4 => orderedInterval (7813039376 / 1000000000000) (7813041702 / 1000000000000)
      | 5 => orderedInterval (3408117337 / 1000000000000) (3408117529 / 1000000000000)
      | 6 => orderedInterval (7345701483 / 1000000000000) (7345701552 / 1000000000000)
      | 7 => orderedInterval (-3324636942 / 1000000000000) (-3324636912 / 1000000000000)
      | _ => orderedInterval (1915658039 / 1000000000000) (1915658205 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-5036479949 / 1000000000000) (-5036479185 / 1000000000000)
      | 1 => orderedInterval (-8470811383 / 1000000000000) (-8470811297 / 1000000000000)
      | 2 => orderedInterval (-4939163317 / 1000000000000) (-4939154452 / 1000000000000)
      | 3 => orderedInterval (-48588065688 / 1000000000000) (-48588058010 / 1000000000000)
      | 4 => orderedInterval (-11317426259 / 1000000000000) (-11317422449 / 1000000000000)
      | 5 => orderedInterval (6152669079 / 1000000000000) (6152669363 / 1000000000000)
      | 6 => orderedInterval (2876031208 / 1000000000000) (2876031273 / 1000000000000)
      | 7 => orderedInterval (-1389274495 / 1000000000000) (-1389274464 / 1000000000000)
      | _ => orderedInterval (-4565759808 / 1000000000000) (-4565759563 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (20218031817 / 1000000000000) (20218032672 / 1000000000000)
      | 1 => orderedInterval (10882832732 / 1000000000000) (10882832852 / 1000000000000)
      | 2 => orderedInterval (-18460588155 / 1000000000000) (-18460571647 / 1000000000000)
      | 3 => orderedInterval (-224827175026 / 1000000000000) (-224827157741 / 1000000000000)
      | 4 => orderedInterval (-23931870364 / 1000000000000) (-23931863978 / 1000000000000)
      | 5 => orderedInterval (-10655961553 / 1000000000000) (-10655961126 / 1000000000000)
      | 6 => orderedInterval (-7556597501 / 1000000000000) (-7556597437 / 1000000000000)
      | 7 => orderedInterval (4172903003 / 1000000000000) (4172903035 / 1000000000000)
      | _ => orderedInterval (-19952904762 / 1000000000000) (-19952904372 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (227092282 / 1000000000000) (227097267 / 1000000000000)
    | 1 => orderedInterval (27267906098 / 1000000000000) (27267913015 / 1000000000000)
    | 2 => orderedInterval (46275851712 / 1000000000000) (46275863562 / 1000000000000)
    | 3 => orderedInterval (-75278280612 / 1000000000000) (-75278258784 / 1000000000000)
    | _ => orderedInterval (-270111329809 / 1000000000000) (-270111287742 / 1000000000000)

theorem compactCertificate399_stateChecks0 :
    compactCertificate399.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 86 12 (541 / 2)) (orderedInterval (43408895893 / 1000000000000) (43408895894 / 1000000000000), orderedInterval (21579818083 / 1000000000000) (21579818084 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (796996302814441 / 4000000000000)) (orderedInterval (-48403048799 / 1000000000000) (-48403015496 / 1000000000000), orderedInterval (29314543321 / 1000000000000) (29314576624 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 103 12 (257732229007753 / 800000000000)) (orderedInterval (26323610996 / 1000000000000) (26323617132 / 1000000000000), orderedInterval (-35861713442 / 1000000000000) (-35861707306 / 1000000000000))) = true
  rfl'

theorem compactCertificate399_stateChecks1 :
    compactCertificate399.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 19 12 (232561533424187 / 4000000000000)) (orderedInterval (72589090712 / 1000000000000) (72589164723 / 1000000000000), orderedInterval (-75993560558 / 1000000000000) (-75993486546 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 50 12 (624692991263039 / 4000000000000)) (orderedInterval (-7756445039 / 1000000000000) (-7756445011 / 1000000000000), orderedInterval (63398539614 / 1000000000000) (63398539642 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 135 12 (1696162991372163 / 4000000000000)) (orderedInterval (-25281250199 / 1000000000000) (-25281250198 / 1000000000000), orderedInterval (-29333023575 / 1000000000000) (-29333023574 / 1000000000000))) = true
  rfl'

theorem compactCertificate399_stateChecks2 :
    compactCertificate399.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 99 12 (1249385982526619 / 4000000000000)) (orderedInterval (-38651956839 / 1000000000000) (-38651901263 / 1000000000000), orderedInterval (23390186872 / 1000000000000) (23390242447 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 170 12 (2140844176161287 / 4000000000000)) (orderedInterval (32342298779 / 1000000000000) (32342327014 / 1000000000000), orderedInterval (-12007233788 / 1000000000000) (-12007205552 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 126 12 (1576936130592533 / 4000000000000)) (orderedInterval (-29423779218 / 1000000000000) (-29423752276 / 1000000000000), orderedInterval (27406427298 / 1000000000000) (27406454241 / 1000000000000))) = true
  rfl'

theorem compactCertificate399_stateChecks3 :
    compactCertificate399.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 193 12 (2419425551654459 / 4000000000000)) (orderedInterval (20545632291 / 1000000000000) (20545634595 / 1000000000000), orderedInterval (-25124572391 / 1000000000000) (-25124570087 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 111 12 (1396855993531811 / 4000000000000)) (orderedInterval (-40931577862 / 1000000000000) (-40931577859 / 1000000000000), orderedInterval (-12090961316 / 1000000000000) (-12090961313 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 197 12 (2478745473003199 / 4000000000000)) (orderedInterval (-32051129543 / 1000000000000) (-32051128347 / 1000000000000), orderedInterval (250722302 / 1000000000000) (250723499 / 1000000000000))) = true
  rfl'

theorem compactCertificate399_stateChecks4 :
    compactCertificate399.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 184 12 (2315965555285531 / 4000000000000)) (orderedInterval (32773214343 / 1000000000000) (32773219151 / 1000000000000), orderedInterval (-5072928791 / 1000000000000) (-5072923983 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 132 12 (1652782300646923 / 4000000000000)) (orderedInterval (-25572683864 / 1000000000000) (-25572675546 / 1000000000000), orderedInterval (29809470636 / 1000000000000) (29809478954 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 149 12 (1874078973789117 / 4000000000000)) (orderedInterval (-34456715670 / 1000000000000) (-34456715668 / 1000000000000), orderedInterval (-13059937828 / 1000000000000) (-13059937826 / 1000000000000))) = true
  rfl'

theorem compactCertificate399_stateChecks5 :
    compactCertificate399.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 124 12 (1562411665790573 / 4000000000000)) (orderedInterval (39017380014 / 1000000000000) (39017385441 / 1000000000000), orderedInterval (-10417273121 / 1000000000000) (-10417267694 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 110 12 (1380438089918033 / 4000000000000)) (orderedInterval (13484749279 / 1000000000000) (13484749280 / 1000000000000), orderedInterval (40758547748 / 1000000000000) (40758547749 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 159 12 (400104763617267 / 800000000000)) (orderedInterval (-35175943886 / 1000000000000) (-35175943832 / 1000000000000), orderedInterval (-5927930853 / 1000000000000) (-5927930799 / 1000000000000))) = true
  rfl'

theorem compactCertificate399_stateChecks6 :
    compactCertificate399.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 88 12 (1106710832525449 / 4000000000000)) (orderedInterval (40428466788 / 1000000000000) (40428466789 / 1000000000000), orderedInterval (25743232698 / 1000000000000) (25743232699 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 75 12 (938171029218689 / 4000000000000)) (orderedInterval (14988956503 / 1000000000000) (14988956686 / 1000000000000), orderedInterval (-49928224797 / 1000000000000) (-49928224614 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 47 12 (587063869407467 / 4000000000000)) (orderedInterval (6859497402 / 1000000000000) (6859497425 / 1000000000000), orderedInterval (-65526227040 / 1000000000000) (-65526227017 / 1000000000000))) = true
  rfl'

theorem compactCertificate399_stateChecks7 :
    compactCertificate399.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 25 12 (315724901453589 / 4000000000000)) (orderedInterval (-82871957263 / 1000000000000) (-82871957262 / 1000000000000), orderedInterval (-34081771729 / 1000000000000) (-34081771728 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (857254524687767 / 4000000000000)) (orderedInterval (54226431490 / 1000000000000) (54226431507 / 1000000000000), orderedInterval (5349936886 / 1000000000000) (5349936903 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 93 12 (1170507764517559 / 4000000000000)) (orderedInterval (-44170987585 / 1000000000000) (-44170987584 / 1000000000000), orderedInterval (-14906350561 / 1000000000000) (-14906350559 / 1000000000000))) = true
  rfl'

theorem compactCertificate399_stateChecks8 :
    compactCertificate399.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 39 12 (494936130592533 / 4000000000000)) (orderedInterval (-65332624159 / 1000000000000) (-65332616675 / 1000000000000), orderedInterval (29872897733 / 1000000000000) (29872905218 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 160 12 (2011887892826293 / 4000000000000)) (orderedInterval (31743396790 / 1000000000000) (31743396792 / 1000000000000), orderedInterval (16033081927 / 1000000000000) (16033081928 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 107 12 (1343847873347387 / 4000000000000)) (orderedInterval (-24456234822 / 1000000000000) (-24456234821 / 1000000000000), orderedInterval (-35974844613 / 1000000000000) (-35974844612 / 1000000000000))) = true
  rfl'

theorem compactCertificate399_states : ∀ j,
    BesselStateValid (compactCertificate399.point j) (compactCertificate399.state j) :=
  compactCertificate399.statesValid_of_checks3 compactCertificate399_stateChecks0
    compactCertificate399_stateChecks1 compactCertificate399_stateChecks2
    compactCertificate399_stateChecks3 compactCertificate399_stateChecks4
    compactCertificate399_stateChecks5 compactCertificate399_stateChecks6
    compactCertificate399_stateChecks7 compactCertificate399_stateChecks8

theorem compactCertificate399_chunkChecks0_0 :
    compactCertificate399.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (541 / 2) 0 (IntervalRat.scale (541 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (43408895893 / 1000000000000) (43408895894 / 1000000000000), orderedInterval (21579818083 / 1000000000000) (21579818084 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (796996302814441 / 4000000000000) 0 (IntervalRat.scale (541 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-48403048799 / 1000000000000) (-48403015496 / 1000000000000), orderedInterval (29314543321 / 1000000000000) (29314576624 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (257732229007753 / 800000000000) 0 (IntervalRat.scale (541 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (26323610996 / 1000000000000) (26323617132 / 1000000000000), orderedInterval (-35861713442 / 1000000000000) (-35861707306 / 1000000000000)))) (orderedInterval (18299443696 / 1000000000000) (18299444387 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (232561533424187 / 4000000000000) 0 (IntervalRat.scale (541 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (72589090712 / 1000000000000) (72589164723 / 1000000000000), orderedInterval (-75993560558 / 1000000000000) (-75993486546 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (624692991263039 / 4000000000000) 0 (IntervalRat.scale (541 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-7756445039 / 1000000000000) (-7756445011 / 1000000000000), orderedInterval (63398539614 / 1000000000000) (63398539642 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1696162991372163 / 4000000000000) 0 (IntervalRat.scale (541 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-25281250199 / 1000000000000) (-25281250198 / 1000000000000), orderedInterval (-29333023575 / 1000000000000) (-29333023574 / 1000000000000)))) (orderedInterval (726492661 / 1000000000000) (726493499 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1249385982526619 / 4000000000000) 0 (IntervalRat.scale (541 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-38651956839 / 1000000000000) (-38651901263 / 1000000000000), orderedInterval (23390186872 / 1000000000000) (23390242447 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2140844176161287 / 4000000000000) 0 (IntervalRat.scale (541 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (32342298779 / 1000000000000) (32342327014 / 1000000000000), orderedInterval (-12007233788 / 1000000000000) (-12007205552 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1576936130592533 / 4000000000000) 0 (IntervalRat.scale (541 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-29423779218 / 1000000000000) (-29423752276 / 1000000000000), orderedInterval (27406427298 / 1000000000000) (27406454241 / 1000000000000)))) (orderedInterval (-1708681465 / 1000000000000) (-1708679927 / 1000000000000))) = true
  rfl'

theorem compactCertificate399_chunkChecks0_1 :
    compactCertificate399.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2419425551654459 / 4000000000000) 0 (IntervalRat.scale (541 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (20545632291 / 1000000000000) (20545634595 / 1000000000000), orderedInterval (-25124572391 / 1000000000000) (-25124570087 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1396855993531811 / 4000000000000) 0 (IntervalRat.scale (541 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-40931577862 / 1000000000000) (-40931577859 / 1000000000000), orderedInterval (-12090961316 / 1000000000000) (-12090961313 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2478745473003199 / 4000000000000) 0 (IntervalRat.scale (541 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-32051129543 / 1000000000000) (-32051128347 / 1000000000000), orderedInterval (250722302 / 1000000000000) (250723499 / 1000000000000)))) (orderedInterval (-11239661257 / 1000000000000) (-11239660570 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2315965555285531 / 4000000000000) 0 (IntervalRat.scale (541 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (32773214343 / 1000000000000) (32773219151 / 1000000000000), orderedInterval (-5072928791 / 1000000000000) (-5072923983 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1652782300646923 / 4000000000000) 0 (IntervalRat.scale (541 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-25572683864 / 1000000000000) (-25572675546 / 1000000000000), orderedInterval (29809470636 / 1000000000000) (29809478954 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1874078973789117 / 4000000000000) 0 (IntervalRat.scale (541 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-34456715670 / 1000000000000) (-34456715668 / 1000000000000), orderedInterval (-13059937828 / 1000000000000) (-13059937826 / 1000000000000)))) (orderedInterval (-2835513209 / 1000000000000) (-2835512303 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1562411665790573 / 4000000000000) 0 (IntervalRat.scale (541 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (39017380014 / 1000000000000) (39017385441 / 1000000000000), orderedInterval (-10417273121 / 1000000000000) (-10417267694 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1380438089918033 / 4000000000000) 0 (IntervalRat.scale (541 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (13484749279 / 1000000000000) (13484749280 / 1000000000000), orderedInterval (40758547748 / 1000000000000) (40758547749 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (400104763617267 / 800000000000) 0 (IntervalRat.scale (541 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-35175943886 / 1000000000000) (-35175943832 / 1000000000000), orderedInterval (-5927930853 / 1000000000000) (-5927930799 / 1000000000000)))) (orderedInterval (-1221770685 / 1000000000000) (-1221770594 / 1000000000000))) = true
  rfl'

theorem compactCertificate399_chunkChecks0_2 :
    compactCertificate399.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1106710832525449 / 4000000000000) 0 (IntervalRat.scale (541 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (40428466788 / 1000000000000) (40428466789 / 1000000000000), orderedInterval (25743232698 / 1000000000000) (25743232699 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (938171029218689 / 4000000000000) 0 (IntervalRat.scale (541 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (14988956503 / 1000000000000) (14988956686 / 1000000000000), orderedInterval (-49928224797 / 1000000000000) (-49928224614 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (587063869407467 / 4000000000000) 0 (IntervalRat.scale (541 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (6859497402 / 1000000000000) (6859497425 / 1000000000000), orderedInterval (-65526227040 / 1000000000000) (-65526227017 / 1000000000000)))) (orderedInterval (-7089267807 / 1000000000000) (-7089267728 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (315724901453589 / 4000000000000) 0 (IntervalRat.scale (541 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-82871957263 / 1000000000000) (-82871957262 / 1000000000000), orderedInterval (-34081771729 / 1000000000000) (-34081771728 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (857254524687767 / 4000000000000) 0 (IntervalRat.scale (541 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (54226431490 / 1000000000000) (54226431507 / 1000000000000), orderedInterval (5349936886 / 1000000000000) (5349936903 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1170507764517559 / 4000000000000) 0 (IntervalRat.scale (541 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-44170987585 / 1000000000000) (-44170987584 / 1000000000000), orderedInterval (-14906350561 / 1000000000000) (-14906350559 / 1000000000000)))) (orderedInterval (3685227377 / 1000000000000) (3685227411 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (494936130592533 / 4000000000000) 0 (IntervalRat.scale (541 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-65332624159 / 1000000000000) (-65332616675 / 1000000000000), orderedInterval (29872897733 / 1000000000000) (29872905218 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2011887892826293 / 4000000000000) 0 (IntervalRat.scale (541 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (31743396790 / 1000000000000) (31743396792 / 1000000000000), orderedInterval (16033081927 / 1000000000000) (16033081928 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1343847873347387 / 4000000000000) 0 (IntervalRat.scale (541 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-24456234822 / 1000000000000) (-24456234821 / 1000000000000), orderedInterval (-35974844613 / 1000000000000) (-35974844612 / 1000000000000)))) (orderedInterval (1610822971 / 1000000000000) (1610823092 / 1000000000000))) = true
  rfl'

theorem compactCertificate399_chunkChecks0 :
    compactCertificate399.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate399.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate399_chunkChecks0_0
    compactCertificate399_chunkChecks0_1 compactCertificate399_chunkChecks0_2

theorem compactCertificate399_chunkChecks1_0 :
    compactCertificate399.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (541 / 2) 1 (IntervalRat.scale (541 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (43408895893 / 1000000000000) (43408895894 / 1000000000000), orderedInterval (21579818083 / 1000000000000) (21579818084 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (796996302814441 / 4000000000000) 1 (IntervalRat.scale (541 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-48403048799 / 1000000000000) (-48403015496 / 1000000000000), orderedInterval (29314543321 / 1000000000000) (29314576624 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (257732229007753 / 800000000000) 1 (IntervalRat.scale (541 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (26323610996 / 1000000000000) (26323617132 / 1000000000000), orderedInterval (-35861713442 / 1000000000000) (-35861707306 / 1000000000000)))) (orderedInterval (6248342775 / 1000000000000) (6248343455 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (232561533424187 / 4000000000000) 1 (IntervalRat.scale (541 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (72589090712 / 1000000000000) (72589164723 / 1000000000000), orderedInterval (-75993560558 / 1000000000000) (-75993486546 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (624692991263039 / 4000000000000) 1 (IntervalRat.scale (541 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-7756445039 / 1000000000000) (-7756445011 / 1000000000000), orderedInterval (63398539614 / 1000000000000) (63398539642 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1696162991372163 / 4000000000000) 1 (IntervalRat.scale (541 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-25281250199 / 1000000000000) (-25281250198 / 1000000000000), orderedInterval (-29333023575 / 1000000000000) (-29333023574 / 1000000000000)))) (orderedInterval (4782569301 / 1000000000000) (4782569512 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1249385982526619 / 4000000000000) 1 (IntervalRat.scale (541 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-38651956839 / 1000000000000) (-38651901263 / 1000000000000), orderedInterval (23390186872 / 1000000000000) (23390242447 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2140844176161287 / 4000000000000) 1 (IntervalRat.scale (541 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (32342298779 / 1000000000000) (32342327014 / 1000000000000), orderedInterval (-12007233788 / 1000000000000) (-12007205552 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1576936130592533 / 4000000000000) 1 (IntervalRat.scale (541 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-29423779218 / 1000000000000) (-29423752276 / 1000000000000), orderedInterval (27406427298 / 1000000000000) (27406454241 / 1000000000000)))) (orderedInterval (1698115023 / 1000000000000) (1698117722 / 1000000000000))) = true
  rfl'

theorem compactCertificate399_chunkChecks1_1 :
    compactCertificate399.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2419425551654459 / 4000000000000) 1 (IntervalRat.scale (541 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (20545632291 / 1000000000000) (20545634595 / 1000000000000), orderedInterval (-25124572391 / 1000000000000) (-25124570087 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1396855993531811 / 4000000000000) 1 (IntervalRat.scale (541 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-40931577862 / 1000000000000) (-40931577859 / 1000000000000), orderedInterval (-12090961316 / 1000000000000) (-12090961313 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2478745473003199 / 4000000000000) 1 (IntervalRat.scale (541 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-32051129543 / 1000000000000) (-32051128347 / 1000000000000), orderedInterval (250722302 / 1000000000000) (250723499 / 1000000000000)))) (orderedInterval (8907677162 / 1000000000000) (8907678690 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2315965555285531 / 4000000000000) 1 (IntervalRat.scale (541 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (32773214343 / 1000000000000) (32773219151 / 1000000000000), orderedInterval (-5072928791 / 1000000000000) (-5072923983 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1652782300646923 / 4000000000000) 1 (IntervalRat.scale (541 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-25572683864 / 1000000000000) (-25572675546 / 1000000000000), orderedInterval (29809470636 / 1000000000000) (29809478954 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1874078973789117 / 4000000000000) 1 (IntervalRat.scale (541 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-34456715670 / 1000000000000) (-34456715668 / 1000000000000), orderedInterval (-13059937828 / 1000000000000) (-13059937826 / 1000000000000)))) (orderedInterval (4616392533 / 1000000000000) (4616393973 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1562411665790573 / 4000000000000) 1 (IntervalRat.scale (541 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (39017380014 / 1000000000000) (39017385441 / 1000000000000), orderedInterval (-10417273121 / 1000000000000) (-10417267694 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1380438089918033 / 4000000000000) 1 (IntervalRat.scale (541 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (13484749279 / 1000000000000) (13484749280 / 1000000000000), orderedInterval (40758547748 / 1000000000000) (40758547749 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (400104763617267 / 800000000000) 1 (IntervalRat.scale (541 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-35175943886 / 1000000000000) (-35175943832 / 1000000000000), orderedInterval (-5927930853 / 1000000000000) (-5927930799 / 1000000000000)))) (orderedInterval (-3430153553 / 1000000000000) (-3430153422 / 1000000000000))) = true
  rfl'

theorem compactCertificate399_chunkChecks1_2 :
    compactCertificate399.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1106710832525449 / 4000000000000) 1 (IntervalRat.scale (541 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (40428466788 / 1000000000000) (40428466789 / 1000000000000), orderedInterval (25743232698 / 1000000000000) (25743232699 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (938171029218689 / 4000000000000) 1 (IntervalRat.scale (541 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (14988956503 / 1000000000000) (14988956686 / 1000000000000), orderedInterval (-49928224797 / 1000000000000) (-49928224614 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (587063869407467 / 4000000000000) 1 (IntervalRat.scale (541 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (6859497402 / 1000000000000) (6859497425 / 1000000000000), orderedInterval (-65526227040 / 1000000000000) (-65526227017 / 1000000000000)))) (orderedInterval (-2917295868 / 1000000000000) (-2917295796 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (315724901453589 / 4000000000000) 1 (IntervalRat.scale (541 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-82871957263 / 1000000000000) (-82871957262 / 1000000000000), orderedInterval (-34081771729 / 1000000000000) (-34081771728 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (857254524687767 / 4000000000000) 1 (IntervalRat.scale (541 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (54226431490 / 1000000000000) (54226431507 / 1000000000000), orderedInterval (5349936886 / 1000000000000) (5349936903 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1170507764517559 / 4000000000000) 1 (IntervalRat.scale (541 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-44170987585 / 1000000000000) (-44170987584 / 1000000000000), orderedInterval (-14906350561 / 1000000000000) (-14906350559 / 1000000000000)))) (orderedInterval (1323327495 / 1000000000000) (1323327525 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (494936130592533 / 4000000000000) 1 (IntervalRat.scale (541 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-65332624159 / 1000000000000) (-65332616675 / 1000000000000), orderedInterval (29872897733 / 1000000000000) (29872905218 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2011887892826293 / 4000000000000) 1 (IntervalRat.scale (541 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (31743396790 / 1000000000000) (31743396792 / 1000000000000), orderedInterval (16033081927 / 1000000000000) (16033081928 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1343847873347387 / 4000000000000) 1 (IntervalRat.scale (541 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-24456234822 / 1000000000000) (-24456234821 / 1000000000000), orderedInterval (-35974844613 / 1000000000000) (-35974844612 / 1000000000000)))) (orderedInterval (6038931230 / 1000000000000) (6038931356 / 1000000000000))) = true
  rfl'

theorem compactCertificate399_chunkChecks1 :
    compactCertificate399.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate399.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate399_chunkChecks1_0
    compactCertificate399_chunkChecks1_1 compactCertificate399_chunkChecks1_2

theorem compactCertificate399_chunkChecks2_0 :
    compactCertificate399.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (541 / 2) 2 (IntervalRat.scale (541 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (43408895893 / 1000000000000) (43408895894 / 1000000000000), orderedInterval (21579818083 / 1000000000000) (21579818084 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (796996302814441 / 4000000000000) 2 (IntervalRat.scale (541 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-48403048799 / 1000000000000) (-48403015496 / 1000000000000), orderedInterval (29314543321 / 1000000000000) (29314576624 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (257732229007753 / 800000000000) 2 (IntervalRat.scale (541 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (26323610996 / 1000000000000) (26323617132 / 1000000000000), orderedInterval (-35861713442 / 1000000000000) (-35861707306 / 1000000000000)))) (orderedInterval (-19175278043 / 1000000000000) (-19175277336 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (232561533424187 / 4000000000000) 2 (IntervalRat.scale (541 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (72589090712 / 1000000000000) (72589164723 / 1000000000000), orderedInterval (-75993560558 / 1000000000000) (-75993486546 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (624692991263039 / 4000000000000) 2 (IntervalRat.scale (541 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-7756445039 / 1000000000000) (-7756445011 / 1000000000000), orderedInterval (63398539614 / 1000000000000) (63398539642 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1696162991372163 / 4000000000000) 2 (IntervalRat.scale (541 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-25281250199 / 1000000000000) (-25281250198 / 1000000000000), orderedInterval (-29333023575 / 1000000000000) (-29333023574 / 1000000000000)))) (orderedInterval (-4303471445 / 1000000000000) (-4303471355 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1249385982526619 / 4000000000000) 2 (IntervalRat.scale (541 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-38651956839 / 1000000000000) (-38651901263 / 1000000000000), orderedInterval (23390186872 / 1000000000000) (23390242447 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2140844176161287 / 4000000000000) 2 (IntervalRat.scale (541 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (32342298779 / 1000000000000) (32342327014 / 1000000000000), orderedInterval (-12007233788 / 1000000000000) (-12007205552 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1576936130592533 / 4000000000000) 2 (IntervalRat.scale (541 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-29423779218 / 1000000000000) (-29423752276 / 1000000000000), orderedInterval (27406427298 / 1000000000000) (27406454241 / 1000000000000)))) (orderedInterval (5409520234 / 1000000000000) (5409525083 / 1000000000000))) = true
  rfl'

theorem compactCertificate399_chunkChecks2_1 :
    compactCertificate399.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2419425551654459 / 4000000000000) 2 (IntervalRat.scale (541 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (20545632291 / 1000000000000) (20545634595 / 1000000000000), orderedInterval (-25124572391 / 1000000000000) (-25124570087 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1396855993531811 / 4000000000000) 2 (IntervalRat.scale (541 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-40931577862 / 1000000000000) (-40931577859 / 1000000000000), orderedInterval (-12090961316 / 1000000000000) (-12090961313 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2478745473003199 / 4000000000000) 2 (IntervalRat.scale (541 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-32051129543 / 1000000000000) (-32051128347 / 1000000000000), orderedInterval (250722302 / 1000000000000) (250723499 / 1000000000000)))) (orderedInterval (47187201673 / 1000000000000) (47187205094 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2315965555285531 / 4000000000000) 2 (IntervalRat.scale (541 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (32773214343 / 1000000000000) (32773219151 / 1000000000000), orderedInterval (-5072928791 / 1000000000000) (-5072923983 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1652782300646923 / 4000000000000) 2 (IntervalRat.scale (541 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-25572683864 / 1000000000000) (-25572675546 / 1000000000000), orderedInterval (29809470636 / 1000000000000) (29809478954 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1874078973789117 / 4000000000000) 2 (IntervalRat.scale (541 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-34456715670 / 1000000000000) (-34456715668 / 1000000000000), orderedInterval (-13059937828 / 1000000000000) (-13059937826 / 1000000000000)))) (orderedInterval (7813039376 / 1000000000000) (7813041702 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1562411665790573 / 4000000000000) 2 (IntervalRat.scale (541 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (39017380014 / 1000000000000) (39017385441 / 1000000000000), orderedInterval (-10417273121 / 1000000000000) (-10417267694 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1380438089918033 / 4000000000000) 2 (IntervalRat.scale (541 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (13484749279 / 1000000000000) (13484749280 / 1000000000000), orderedInterval (40758547748 / 1000000000000) (40758547749 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (400104763617267 / 800000000000) 2 (IntervalRat.scale (541 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-35175943886 / 1000000000000) (-35175943832 / 1000000000000), orderedInterval (-5927930853 / 1000000000000) (-5927930799 / 1000000000000)))) (orderedInterval (3408117337 / 1000000000000) (3408117529 / 1000000000000))) = true
  rfl'

theorem compactCertificate399_chunkChecks2_2 :
    compactCertificate399.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1106710832525449 / 4000000000000) 2 (IntervalRat.scale (541 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (40428466788 / 1000000000000) (40428466789 / 1000000000000), orderedInterval (25743232698 / 1000000000000) (25743232699 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (938171029218689 / 4000000000000) 2 (IntervalRat.scale (541 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (14988956503 / 1000000000000) (14988956686 / 1000000000000), orderedInterval (-49928224797 / 1000000000000) (-49928224614 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (587063869407467 / 4000000000000) 2 (IntervalRat.scale (541 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (6859497402 / 1000000000000) (6859497425 / 1000000000000), orderedInterval (-65526227040 / 1000000000000) (-65526227017 / 1000000000000)))) (orderedInterval (7345701483 / 1000000000000) (7345701552 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (315724901453589 / 4000000000000) 2 (IntervalRat.scale (541 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-82871957263 / 1000000000000) (-82871957262 / 1000000000000), orderedInterval (-34081771729 / 1000000000000) (-34081771728 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (857254524687767 / 4000000000000) 2 (IntervalRat.scale (541 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (54226431490 / 1000000000000) (54226431507 / 1000000000000), orderedInterval (5349936886 / 1000000000000) (5349936903 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1170507764517559 / 4000000000000) 2 (IntervalRat.scale (541 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-44170987585 / 1000000000000) (-44170987584 / 1000000000000), orderedInterval (-14906350561 / 1000000000000) (-14906350559 / 1000000000000)))) (orderedInterval (-3324636942 / 1000000000000) (-3324636912 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (494936130592533 / 4000000000000) 2 (IntervalRat.scale (541 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-65332624159 / 1000000000000) (-65332616675 / 1000000000000), orderedInterval (29872897733 / 1000000000000) (29872905218 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2011887892826293 / 4000000000000) 2 (IntervalRat.scale (541 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (31743396790 / 1000000000000) (31743396792 / 1000000000000), orderedInterval (16033081927 / 1000000000000) (16033081928 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1343847873347387 / 4000000000000) 2 (IntervalRat.scale (541 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-24456234822 / 1000000000000) (-24456234821 / 1000000000000), orderedInterval (-35974844613 / 1000000000000) (-35974844612 / 1000000000000)))) (orderedInterval (1915658039 / 1000000000000) (1915658205 / 1000000000000))) = true
  rfl'

theorem compactCertificate399_chunkChecks2 :
    compactCertificate399.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate399.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate399_chunkChecks2_0
    compactCertificate399_chunkChecks2_1 compactCertificate399_chunkChecks2_2

theorem compactCertificate399_chunkChecks3_0 :
    compactCertificate399.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (541 / 2) 3 (IntervalRat.scale (541 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (43408895893 / 1000000000000) (43408895894 / 1000000000000), orderedInterval (21579818083 / 1000000000000) (21579818084 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (796996302814441 / 4000000000000) 3 (IntervalRat.scale (541 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-48403048799 / 1000000000000) (-48403015496 / 1000000000000), orderedInterval (29314543321 / 1000000000000) (29314576624 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (257732229007753 / 800000000000) 3 (IntervalRat.scale (541 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (26323610996 / 1000000000000) (26323617132 / 1000000000000), orderedInterval (-35861713442 / 1000000000000) (-35861707306 / 1000000000000)))) (orderedInterval (-5036479949 / 1000000000000) (-5036479185 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (232561533424187 / 4000000000000) 3 (IntervalRat.scale (541 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (72589090712 / 1000000000000) (72589164723 / 1000000000000), orderedInterval (-75993560558 / 1000000000000) (-75993486546 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (624692991263039 / 4000000000000) 3 (IntervalRat.scale (541 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-7756445039 / 1000000000000) (-7756445011 / 1000000000000), orderedInterval (63398539614 / 1000000000000) (63398539642 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1696162991372163 / 4000000000000) 3 (IntervalRat.scale (541 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-25281250199 / 1000000000000) (-25281250198 / 1000000000000), orderedInterval (-29333023575 / 1000000000000) (-29333023574 / 1000000000000)))) (orderedInterval (-8470811383 / 1000000000000) (-8470811297 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1249385982526619 / 4000000000000) 3 (IntervalRat.scale (541 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-38651956839 / 1000000000000) (-38651901263 / 1000000000000), orderedInterval (23390186872 / 1000000000000) (23390242447 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2140844176161287 / 4000000000000) 3 (IntervalRat.scale (541 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (32342298779 / 1000000000000) (32342327014 / 1000000000000), orderedInterval (-12007233788 / 1000000000000) (-12007205552 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1576936130592533 / 4000000000000) 3 (IntervalRat.scale (541 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-29423779218 / 1000000000000) (-29423752276 / 1000000000000), orderedInterval (27406427298 / 1000000000000) (27406454241 / 1000000000000)))) (orderedInterval (-4939163317 / 1000000000000) (-4939154452 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate399_chunkChecks3_1 :
    compactCertificate399.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2419425551654459 / 4000000000000) 3 (IntervalRat.scale (541 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (20545632291 / 1000000000000) (20545634595 / 1000000000000), orderedInterval (-25124572391 / 1000000000000) (-25124570087 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1396855993531811 / 4000000000000) 3 (IntervalRat.scale (541 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-40931577862 / 1000000000000) (-40931577859 / 1000000000000), orderedInterval (-12090961316 / 1000000000000) (-12090961313 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2478745473003199 / 4000000000000) 3 (IntervalRat.scale (541 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-32051129543 / 1000000000000) (-32051128347 / 1000000000000), orderedInterval (250722302 / 1000000000000) (250723499 / 1000000000000)))) (orderedInterval (-48588065688 / 1000000000000) (-48588058010 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2315965555285531 / 4000000000000) 3 (IntervalRat.scale (541 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (32773214343 / 1000000000000) (32773219151 / 1000000000000), orderedInterval (-5072928791 / 1000000000000) (-5072923983 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1652782300646923 / 4000000000000) 3 (IntervalRat.scale (541 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-25572683864 / 1000000000000) (-25572675546 / 1000000000000), orderedInterval (29809470636 / 1000000000000) (29809478954 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1874078973789117 / 4000000000000) 3 (IntervalRat.scale (541 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-34456715670 / 1000000000000) (-34456715668 / 1000000000000), orderedInterval (-13059937828 / 1000000000000) (-13059937826 / 1000000000000)))) (orderedInterval (-11317426259 / 1000000000000) (-11317422449 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1562411665790573 / 4000000000000) 3 (IntervalRat.scale (541 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (39017380014 / 1000000000000) (39017385441 / 1000000000000), orderedInterval (-10417273121 / 1000000000000) (-10417267694 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1380438089918033 / 4000000000000) 3 (IntervalRat.scale (541 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (13484749279 / 1000000000000) (13484749280 / 1000000000000), orderedInterval (40758547748 / 1000000000000) (40758547749 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (400104763617267 / 800000000000) 3 (IntervalRat.scale (541 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-35175943886 / 1000000000000) (-35175943832 / 1000000000000), orderedInterval (-5927930853 / 1000000000000) (-5927930799 / 1000000000000)))) (orderedInterval (6152669079 / 1000000000000) (6152669363 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate399_chunkChecks3_2 :
    compactCertificate399.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1106710832525449 / 4000000000000) 3 (IntervalRat.scale (541 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (40428466788 / 1000000000000) (40428466789 / 1000000000000), orderedInterval (25743232698 / 1000000000000) (25743232699 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (938171029218689 / 4000000000000) 3 (IntervalRat.scale (541 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (14988956503 / 1000000000000) (14988956686 / 1000000000000), orderedInterval (-49928224797 / 1000000000000) (-49928224614 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (587063869407467 / 4000000000000) 3 (IntervalRat.scale (541 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (6859497402 / 1000000000000) (6859497425 / 1000000000000), orderedInterval (-65526227040 / 1000000000000) (-65526227017 / 1000000000000)))) (orderedInterval (2876031208 / 1000000000000) (2876031273 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (315724901453589 / 4000000000000) 3 (IntervalRat.scale (541 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-82871957263 / 1000000000000) (-82871957262 / 1000000000000), orderedInterval (-34081771729 / 1000000000000) (-34081771728 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (857254524687767 / 4000000000000) 3 (IntervalRat.scale (541 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (54226431490 / 1000000000000) (54226431507 / 1000000000000), orderedInterval (5349936886 / 1000000000000) (5349936903 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1170507764517559 / 4000000000000) 3 (IntervalRat.scale (541 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-44170987585 / 1000000000000) (-44170987584 / 1000000000000), orderedInterval (-14906350561 / 1000000000000) (-14906350559 / 1000000000000)))) (orderedInterval (-1389274495 / 1000000000000) (-1389274464 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (494936130592533 / 4000000000000) 3 (IntervalRat.scale (541 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-65332624159 / 1000000000000) (-65332616675 / 1000000000000), orderedInterval (29872897733 / 1000000000000) (29872905218 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2011887892826293 / 4000000000000) 3 (IntervalRat.scale (541 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (31743396790 / 1000000000000) (31743396792 / 1000000000000), orderedInterval (16033081927 / 1000000000000) (16033081928 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1343847873347387 / 4000000000000) 3 (IntervalRat.scale (541 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-24456234822 / 1000000000000) (-24456234821 / 1000000000000), orderedInterval (-35974844613 / 1000000000000) (-35974844612 / 1000000000000)))) (orderedInterval (-4565759808 / 1000000000000) (-4565759563 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate399_chunkChecks3 :
    compactCertificate399.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate399.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate399_chunkChecks3_0
    compactCertificate399_chunkChecks3_1 compactCertificate399_chunkChecks3_2

theorem compactCertificate399_chunkChecks4_0 :
    compactCertificate399.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (541 / 2) 4 (IntervalRat.scale (541 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (43408895893 / 1000000000000) (43408895894 / 1000000000000), orderedInterval (21579818083 / 1000000000000) (21579818084 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (796996302814441 / 4000000000000) 4 (IntervalRat.scale (541 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-48403048799 / 1000000000000) (-48403015496 / 1000000000000), orderedInterval (29314543321 / 1000000000000) (29314576624 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (257732229007753 / 800000000000) 4 (IntervalRat.scale (541 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (26323610996 / 1000000000000) (26323617132 / 1000000000000), orderedInterval (-35861713442 / 1000000000000) (-35861707306 / 1000000000000)))) (orderedInterval (20218031817 / 1000000000000) (20218032672 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (232561533424187 / 4000000000000) 4 (IntervalRat.scale (541 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (72589090712 / 1000000000000) (72589164723 / 1000000000000), orderedInterval (-75993560558 / 1000000000000) (-75993486546 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (624692991263039 / 4000000000000) 4 (IntervalRat.scale (541 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-7756445039 / 1000000000000) (-7756445011 / 1000000000000), orderedInterval (63398539614 / 1000000000000) (63398539642 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1696162991372163 / 4000000000000) 4 (IntervalRat.scale (541 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-25281250199 / 1000000000000) (-25281250198 / 1000000000000), orderedInterval (-29333023575 / 1000000000000) (-29333023574 / 1000000000000)))) (orderedInterval (10882832732 / 1000000000000) (10882832852 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1249385982526619 / 4000000000000) 4 (IntervalRat.scale (541 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-38651956839 / 1000000000000) (-38651901263 / 1000000000000), orderedInterval (23390186872 / 1000000000000) (23390242447 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2140844176161287 / 4000000000000) 4 (IntervalRat.scale (541 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (32342298779 / 1000000000000) (32342327014 / 1000000000000), orderedInterval (-12007233788 / 1000000000000) (-12007205552 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1576936130592533 / 4000000000000) 4 (IntervalRat.scale (541 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-29423779218 / 1000000000000) (-29423752276 / 1000000000000), orderedInterval (27406427298 / 1000000000000) (27406454241 / 1000000000000)))) (orderedInterval (-18460588155 / 1000000000000) (-18460571647 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate399_chunkChecks4_1 :
    compactCertificate399.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2419425551654459 / 4000000000000) 4 (IntervalRat.scale (541 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (20545632291 / 1000000000000) (20545634595 / 1000000000000), orderedInterval (-25124572391 / 1000000000000) (-25124570087 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1396855993531811 / 4000000000000) 4 (IntervalRat.scale (541 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-40931577862 / 1000000000000) (-40931577859 / 1000000000000), orderedInterval (-12090961316 / 1000000000000) (-12090961313 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2478745473003199 / 4000000000000) 4 (IntervalRat.scale (541 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-32051129543 / 1000000000000) (-32051128347 / 1000000000000), orderedInterval (250722302 / 1000000000000) (250723499 / 1000000000000)))) (orderedInterval (-224827175026 / 1000000000000) (-224827157741 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2315965555285531 / 4000000000000) 4 (IntervalRat.scale (541 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (32773214343 / 1000000000000) (32773219151 / 1000000000000), orderedInterval (-5072928791 / 1000000000000) (-5072923983 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1652782300646923 / 4000000000000) 4 (IntervalRat.scale (541 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-25572683864 / 1000000000000) (-25572675546 / 1000000000000), orderedInterval (29809470636 / 1000000000000) (29809478954 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1874078973789117 / 4000000000000) 4 (IntervalRat.scale (541 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-34456715670 / 1000000000000) (-34456715668 / 1000000000000), orderedInterval (-13059937828 / 1000000000000) (-13059937826 / 1000000000000)))) (orderedInterval (-23931870364 / 1000000000000) (-23931863978 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1562411665790573 / 4000000000000) 4 (IntervalRat.scale (541 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (39017380014 / 1000000000000) (39017385441 / 1000000000000), orderedInterval (-10417273121 / 1000000000000) (-10417267694 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1380438089918033 / 4000000000000) 4 (IntervalRat.scale (541 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (13484749279 / 1000000000000) (13484749280 / 1000000000000), orderedInterval (40758547748 / 1000000000000) (40758547749 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (400104763617267 / 800000000000) 4 (IntervalRat.scale (541 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-35175943886 / 1000000000000) (-35175943832 / 1000000000000), orderedInterval (-5927930853 / 1000000000000) (-5927930799 / 1000000000000)))) (orderedInterval (-10655961553 / 1000000000000) (-10655961126 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate399_chunkChecks4_2 :
    compactCertificate399.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1106710832525449 / 4000000000000) 4 (IntervalRat.scale (541 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (40428466788 / 1000000000000) (40428466789 / 1000000000000), orderedInterval (25743232698 / 1000000000000) (25743232699 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (938171029218689 / 4000000000000) 4 (IntervalRat.scale (541 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (14988956503 / 1000000000000) (14988956686 / 1000000000000), orderedInterval (-49928224797 / 1000000000000) (-49928224614 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (587063869407467 / 4000000000000) 4 (IntervalRat.scale (541 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (6859497402 / 1000000000000) (6859497425 / 1000000000000), orderedInterval (-65526227040 / 1000000000000) (-65526227017 / 1000000000000)))) (orderedInterval (-7556597501 / 1000000000000) (-7556597437 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (315724901453589 / 4000000000000) 4 (IntervalRat.scale (541 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-82871957263 / 1000000000000) (-82871957262 / 1000000000000), orderedInterval (-34081771729 / 1000000000000) (-34081771728 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (857254524687767 / 4000000000000) 4 (IntervalRat.scale (541 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (54226431490 / 1000000000000) (54226431507 / 1000000000000), orderedInterval (5349936886 / 1000000000000) (5349936903 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1170507764517559 / 4000000000000) 4 (IntervalRat.scale (541 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-44170987585 / 1000000000000) (-44170987584 / 1000000000000), orderedInterval (-14906350561 / 1000000000000) (-14906350559 / 1000000000000)))) (orderedInterval (4172903003 / 1000000000000) (4172903035 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (494936130592533 / 4000000000000) 4 (IntervalRat.scale (541 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-65332624159 / 1000000000000) (-65332616675 / 1000000000000), orderedInterval (29872897733 / 1000000000000) (29872905218 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2011887892826293 / 4000000000000) 4 (IntervalRat.scale (541 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (31743396790 / 1000000000000) (31743396792 / 1000000000000), orderedInterval (16033081927 / 1000000000000) (16033081928 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1343847873347387 / 4000000000000) 4 (IntervalRat.scale (541 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-24456234822 / 1000000000000) (-24456234821 / 1000000000000), orderedInterval (-35974844613 / 1000000000000) (-35974844612 / 1000000000000)))) (orderedInterval (-19952904762 / 1000000000000) (-19952904372 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate399_chunkChecks4 :
    compactCertificate399.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate399.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate399_chunkChecks4_0
    compactCertificate399_chunkChecks4_1 compactCertificate399_chunkChecks4_2

theorem compactCertificate399_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate399.chunkCheck r b = true :=
  compactCertificate399.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate399_chunkChecks0
    · exact compactCertificate399_chunkChecks1
    · exact compactCertificate399_chunkChecks2
    · exact compactCertificate399_chunkChecks3
    · exact compactCertificate399_chunkChecks4)

theorem compactCertificate399_coefficient0 :
    compactCertificate399.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate399_coefficient1 :
    compactCertificate399.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate399_coefficient2 :
    compactCertificate399.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate399_coefficient3 :
    compactCertificate399.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate399_coefficient4 :
    compactCertificate399.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate399_coefficients : ∀ r : Fin 5,
    compactCertificate399.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate399_coefficient0
  · exact compactCertificate399_coefficient1
  · exact compactCertificate399_coefficient2
  · exact compactCertificate399_coefficient3
  · exact compactCertificate399_coefficient4

theorem compactCertificate399_lower : (1 : ℚ) ≤ compactCertificate399.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate399, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate399_proves {t : ℝ} (ht : t ∈ compactCertificate399.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate399.proves compactCertificate399_states compactCertificate399_chunks
    compactCertificate399_coefficients compactCertificate399_lower ht

end Erdos232
