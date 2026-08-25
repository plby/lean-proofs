/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate358 : CompactCertificate where
  left := 229
  right := 230
  center := 459 / 2
  grid := fun i =>
    match i.val with
    | 0 => 73
    | 1 => 54
    | 2 => 87
    | 3 => 16
    | 4 => 42
    | 5 => 115
    | 6 => 84
    | 7 => 145
    | 8 => 107
    | 9 => 163
    | 10 => 94
    | 11 => 167
    | 12 => 156
    | 13 => 112
    | 14 => 127
    | 15 => 106
    | 16 => 93
    | 17 => 135
    | 18 => 75
    | 19 => 63
    | 20 => 40
    | 21 => 21
    | 22 => 58
    | 23 => 79
    | 24 => 33
    | 25 => 136
    | _ => 91
  point := fun i =>
    match i.val with
    | 0 => 459 / 2
    | 1 => 676194645086559 / 4000000000000
    | 2 => 218667454925247 / 800000000000
    | 3 => 197311910982813 / 4000000000000
    | 4 => 530007547115961 / 4000000000000
    | 5 => 1439073591570837 / 4000000000000
    | 6 => 1060015094232381 / 4000000000000
    | 7 => 1816353931345713 / 4000000000000
    | 8 => 1337918084920467 / 4000000000000
    | 9 => 2052710403344541 / 4000000000000
    | 10 => 1185132903939189 / 4000000000000
    | 11 => 2103039135135801 / 4000000000000
    | 12 => 1964931959105469 / 4000000000000
    | 13 => 1402268162656077 / 4000000000000
    | 14 => 1590022641347883 / 4000000000000
    | 15 => 1325595110162427 / 4000000000000
    | 16 => 1171203481094967 / 4000000000000
    | 17 => 339460418669733 / 800000000000
    | 18 => 938965382863551 / 4000000000000
    | 19 => 795971353810311 / 4000000000000
    | 20 => 498081915079533 / 4000000000000
    | 21 => 267870110475411 / 4000000000000
    | 22 => 727319458099233 / 4000000000000
    | 23 => 993092539581441 / 4000000000000
    | 24 => 419918084920467 / 4000000000000
    | 25 => 1706943702046707 / 4000000000000
    | _ => 1140159286259613 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-42797857478 / 1000000000000) (-42797857477 / 1000000000000), orderedInterval (-30603397956 / 1000000000000) (-30603397955 / 1000000000000))
    | 1 => (orderedInterval (11427917470 / 1000000000000) (11427917471 / 1000000000000), orderedInterval (60259769707 / 1000000000000) (60259769708 / 1000000000000))
    | 2 => (orderedInterval (-34643509794 / 1000000000000) (-34643509793 / 1000000000000), orderedInterval (-33535965098 / 1000000000000) (-33535965097 / 1000000000000))
    | 3 => (orderedInterval (-17497338023 / 1000000000000) (-17497337925 / 1000000000000), orderedInterval (112428531275 / 1000000000000) (112428531373 / 1000000000000))
    | 4 => (orderedInterval (67468392063 / 1000000000000) (67468392065 / 1000000000000), orderedInterval (15638633722 / 1000000000000) (15638633724 / 1000000000000))
    | 5 => (orderedInterval (28043145933 / 1000000000000) (28043159227 / 1000000000000), orderedInterval (-31393540320 / 1000000000000) (-31393527026 / 1000000000000))
    | 6 => (orderedInterval (46461196403 / 1000000000000) (46461201879 / 1000000000000), orderedInterval (-15697215677 / 1000000000000) (-15697210201 / 1000000000000))
    | 7 => (orderedInterval (22877794420 / 1000000000000) (22877798312 / 1000000000000), orderedInterval (-29666036249 / 1000000000000) (-29666032357 / 1000000000000))
    | 8 => (orderedInterval (33787509283 / 1000000000000) (33787572052 / 1000000000000), orderedInterval (-27649745465 / 1000000000000) (-27649682697 / 1000000000000))
    | 9 => (orderedInterval (-33517077784 / 1000000000000) (-33517060691 / 1000000000000), orderedInterval (10856247508 / 1000000000000) (10856264600 / 1000000000000))
    | 10 => (orderedInterval (45539764028 / 1000000000000) (45539765484 / 1000000000000), orderedInterval (-8726331543 / 1000000000000) (-8726330088 / 1000000000000))
    | 11 => (orderedInterval (-32940311873 / 1000000000000) (-32940290771 / 1000000000000), orderedInterval (11247055649 / 1000000000000) (11247076751 / 1000000000000))
    | 12 => (orderedInterval (33705925513 / 1000000000000) (33705949396 / 1000000000000), orderedInterval (-12678378522 / 1000000000000) (-12678354638 / 1000000000000))
    | 13 => (orderedInterval (-20665342965 / 1000000000000) (-20665341673 / 1000000000000), orderedInterval (37297638877 / 1000000000000) (37297640169 / 1000000000000))
    | 14 => (orderedInterval (25520671068 / 1000000000000) (25520678576 / 1000000000000), orderedInterval (-30857934025 / 1000000000000) (-30857926517 / 1000000000000))
    | 15 => (orderedInterval (-32195397310 / 1000000000000) (-32195360134 / 1000000000000), orderedInterval (29788521924 / 1000000000000) (29788559100 / 1000000000000))
    | 16 => (orderedInterval (-46083516534 / 1000000000000) (-46083516520 / 1000000000000), orderedInterval (-7031008883 / 1000000000000) (-7031008869 / 1000000000000))
    | 17 => (orderedInterval (-32501381237 / 1000000000000) (-32501381236 / 1000000000000), orderedInterval (-21032290065 / 1000000000000) (-21032290064 / 1000000000000))
    | 18 => (orderedInterval (4848491129 / 1000000000000) (4848491139 / 1000000000000), orderedInterval (-51861108099 / 1000000000000) (-51861108089 / 1000000000000))
    | 19 => (orderedInterval (-54256355764 / 1000000000000) (-54256353211 / 1000000000000), orderedInterval (16119096317 / 1000000000000) (16119098869 / 1000000000000))
    | 20 => (orderedInterval (-25110187880 / 1000000000000) (-25110187010 / 1000000000000), orderedInterval (67049166750 / 1000000000000) (67049167619 / 1000000000000))
    | 21 => (orderedInterval (-95421616359 / 1000000000000) (-95421615900 / 1000000000000), orderedInterval (20734087209 / 1000000000000) (20734087667 / 1000000000000))
    | 22 => (orderedInterval (23162068396 / 1000000000000) (23162068397 / 1000000000000), orderedInterval (54385473686 / 1000000000000) (54385473687 / 1000000000000))
    | 23 => (orderedInterval (-38775995509 / 1000000000000) (-38775995508 / 1000000000000), orderedInterval (-32488953794 / 1000000000000) (-32488953793 / 1000000000000))
    | 24 => (orderedInterval (-67564933329 / 1000000000000) (-67564915919 / 1000000000000), orderedInterval (39040956578 / 1000000000000) (39040973988 / 1000000000000))
    | 25 => (orderedInterval (10094800933 / 1000000000000) (10094800934 / 1000000000000), orderedInterval (37269954598 / 1000000000000) (37269954599 / 1000000000000))
    | _ => (orderedInterval (2840944189 / 1000000000000) (2840944193 / 1000000000000), orderedInterval (-47178852944 / 1000000000000) (-47178852940 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-18890007116 / 1000000000000) (-18890007099 / 1000000000000)
      | 1 => orderedInterval (659644369 / 1000000000000) (659645343 / 1000000000000)
      | 2 => orderedInterval (110934596 / 1000000000000) (110936246 / 1000000000000)
      | 3 => orderedInterval (4647039305 / 1000000000000) (4647045541 / 1000000000000)
      | 4 => orderedInterval (-2691819808 / 1000000000000) (-2691819189 / 1000000000000)
      | 5 => orderedInterval (1433260940 / 1000000000000) (1433261393 / 1000000000000)
      | 6 => orderedInterval (1478201116 / 1000000000000) (1478201348 / 1000000000000)
      | 7 => orderedInterval (4208245117 / 1000000000000) (4208245154 / 1000000000000)
      | _ => orderedInterval (-1762074838 / 1000000000000) (-1762074668 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-14060315693 / 1000000000000) (-14060315674 / 1000000000000)
      | 1 => orderedInterval (3566029367 / 1000000000000) (3566030880 / 1000000000000)
      | 2 => orderedInterval (836545185 / 1000000000000) (836547656 / 1000000000000)
      | 3 => orderedInterval (-1485368225 / 1000000000000) (-1485354233 / 1000000000000)
      | 4 => orderedInterval (6147926494 / 1000000000000) (6147927714 / 1000000000000)
      | 5 => orderedInterval (14403160 / 1000000000000) (14403814 / 1000000000000)
      | 6 => orderedInterval (8874843517 / 1000000000000) (8874843713 / 1000000000000)
      | 7 => orderedInterval (1604323434 / 1000000000000) (1604323462 / 1000000000000)
      | _ => orderedInterval (5460706245 / 1000000000000) (5460706384 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (19850716520 / 1000000000000) (19850716542 / 1000000000000)
      | 1 => orderedInterval (4053632816 / 1000000000000) (4053635189 / 1000000000000)
      | 2 => orderedInterval (1024352974 / 1000000000000) (1024356717 / 1000000000000)
      | 3 => orderedInterval (-10819505610 / 1000000000000) (-10819474036 / 1000000000000)
      | 4 => orderedInterval (7708235679 / 1000000000000) (7708238132 / 1000000000000)
      | 5 => orderedInterval (-672740310 / 1000000000000) (-672739363 / 1000000000000)
      | 6 => orderedInterval (-1295714544 / 1000000000000) (-1295714373 / 1000000000000)
      | 7 => orderedInterval (-3304976897 / 1000000000000) (-3304976871 / 1000000000000)
      | _ => orderedInterval (3724765594 / 1000000000000) (3724765750 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (15143577700 / 1000000000000) (15143577725 / 1000000000000)
      | 1 => orderedInterval (-8712780113 / 1000000000000) (-8712776397 / 1000000000000)
      | 2 => orderedInterval (-5023446615 / 1000000000000) (-5023440900 / 1000000000000)
      | 3 => orderedInterval (3782528734 / 1000000000000) (3782600008 / 1000000000000)
      | 4 => orderedInterval (-15660370770 / 1000000000000) (-15660365773 / 1000000000000)
      | 5 => orderedInterval (1535257000 / 1000000000000) (1535258372 / 1000000000000)
      | 6 => orderedInterval (-8621511031 / 1000000000000) (-8621510880 / 1000000000000)
      | 7 => orderedInterval (-2514717242 / 1000000000000) (-2514717216 / 1000000000000)
      | _ => orderedInterval (2505897908 / 1000000000000) (2505898123 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-21154221789 / 1000000000000) (-21154221760 / 1000000000000)
      | 1 => orderedInterval (-11688994624 / 1000000000000) (-11688988785 / 1000000000000)
      | 2 => orderedInterval (-7086731297 / 1000000000000) (-7086722429 / 1000000000000)
      | 3 => orderedInterval (29252114247 / 1000000000000) (29252275679 / 1000000000000)
      | 4 => orderedInterval (-24437659078 / 1000000000000) (-24437648761 / 1000000000000)
      | 5 => orderedInterval (-4367307774 / 1000000000000) (-4367305778 / 1000000000000)
      | 6 => orderedInterval (891487620 / 1000000000000) (891487756 / 1000000000000)
      | 7 => orderedInterval (3897626921 / 1000000000000) (3897626948 / 1000000000000)
      | _ => orderedInterval (-11130831432 / 1000000000000) (-11130831097 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-10806576319 / 1000000000000) (-10806565931 / 1000000000000)
    | 1 => orderedInterval (10959093484 / 1000000000000) (10959113716 / 1000000000000)
    | 2 => orderedInterval (20268766222 / 1000000000000) (20268807687 / 1000000000000)
    | 3 => orderedInterval (-17565564429 / 1000000000000) (-17565476938 / 1000000000000)
    | _ => orderedInterval (-45824517206 / 1000000000000) (-45824328227 / 1000000000000)

theorem compactCertificate358_stateChecks0 :
    compactCertificate358.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 73 12 (459 / 2)) (orderedInterval (-42797857478 / 1000000000000) (-42797857477 / 1000000000000), orderedInterval (-30603397956 / 1000000000000) (-30603397955 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (676194645086559 / 4000000000000)) (orderedInterval (11427917470 / 1000000000000) (11427917471 / 1000000000000), orderedInterval (60259769707 / 1000000000000) (60259769708 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 87 12 (218667454925247 / 800000000000)) (orderedInterval (-34643509794 / 1000000000000) (-34643509793 / 1000000000000), orderedInterval (-33535965098 / 1000000000000) (-33535965097 / 1000000000000))) = true
  rfl'

theorem compactCertificate358_stateChecks1 :
    compactCertificate358.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 16 12 (197311910982813 / 4000000000000)) (orderedInterval (-17497338023 / 1000000000000) (-17497337925 / 1000000000000), orderedInterval (112428531275 / 1000000000000) (112428531373 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 42 12 (530007547115961 / 4000000000000)) (orderedInterval (67468392063 / 1000000000000) (67468392065 / 1000000000000), orderedInterval (15638633722 / 1000000000000) (15638633724 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 115 12 (1439073591570837 / 4000000000000)) (orderedInterval (28043145933 / 1000000000000) (28043159227 / 1000000000000), orderedInterval (-31393540320 / 1000000000000) (-31393527026 / 1000000000000))) = true
  rfl'

theorem compactCertificate358_stateChecks2 :
    compactCertificate358.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 84 12 (1060015094232381 / 4000000000000)) (orderedInterval (46461196403 / 1000000000000) (46461201879 / 1000000000000), orderedInterval (-15697215677 / 1000000000000) (-15697210201 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 145 12 (1816353931345713 / 4000000000000)) (orderedInterval (22877794420 / 1000000000000) (22877798312 / 1000000000000), orderedInterval (-29666036249 / 1000000000000) (-29666032357 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 107 12 (1337918084920467 / 4000000000000)) (orderedInterval (33787509283 / 1000000000000) (33787572052 / 1000000000000), orderedInterval (-27649745465 / 1000000000000) (-27649682697 / 1000000000000))) = true
  rfl'

theorem compactCertificate358_stateChecks3 :
    compactCertificate358.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 163 12 (2052710403344541 / 4000000000000)) (orderedInterval (-33517077784 / 1000000000000) (-33517060691 / 1000000000000), orderedInterval (10856247508 / 1000000000000) (10856264600 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 94 12 (1185132903939189 / 4000000000000)) (orderedInterval (45539764028 / 1000000000000) (45539765484 / 1000000000000), orderedInterval (-8726331543 / 1000000000000) (-8726330088 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 167 12 (2103039135135801 / 4000000000000)) (orderedInterval (-32940311873 / 1000000000000) (-32940290771 / 1000000000000), orderedInterval (11247055649 / 1000000000000) (11247076751 / 1000000000000))) = true
  rfl'

theorem compactCertificate358_stateChecks4 :
    compactCertificate358.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 156 12 (1964931959105469 / 4000000000000)) (orderedInterval (33705925513 / 1000000000000) (33705949396 / 1000000000000), orderedInterval (-12678378522 / 1000000000000) (-12678354638 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 112 12 (1402268162656077 / 4000000000000)) (orderedInterval (-20665342965 / 1000000000000) (-20665341673 / 1000000000000), orderedInterval (37297638877 / 1000000000000) (37297640169 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 127 12 (1590022641347883 / 4000000000000)) (orderedInterval (25520671068 / 1000000000000) (25520678576 / 1000000000000), orderedInterval (-30857934025 / 1000000000000) (-30857926517 / 1000000000000))) = true
  rfl'

theorem compactCertificate358_stateChecks5 :
    compactCertificate358.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 106 12 (1325595110162427 / 4000000000000)) (orderedInterval (-32195397310 / 1000000000000) (-32195360134 / 1000000000000), orderedInterval (29788521924 / 1000000000000) (29788559100 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 93 12 (1171203481094967 / 4000000000000)) (orderedInterval (-46083516534 / 1000000000000) (-46083516520 / 1000000000000), orderedInterval (-7031008883 / 1000000000000) (-7031008869 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 135 12 (339460418669733 / 800000000000)) (orderedInterval (-32501381237 / 1000000000000) (-32501381236 / 1000000000000), orderedInterval (-21032290065 / 1000000000000) (-21032290064 / 1000000000000))) = true
  rfl'

theorem compactCertificate358_stateChecks6 :
    compactCertificate358.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 75 12 (938965382863551 / 4000000000000)) (orderedInterval (4848491129 / 1000000000000) (4848491139 / 1000000000000), orderedInterval (-51861108099 / 1000000000000) (-51861108089 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (795971353810311 / 4000000000000)) (orderedInterval (-54256355764 / 1000000000000) (-54256353211 / 1000000000000), orderedInterval (16119096317 / 1000000000000) (16119098869 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 40 12 (498081915079533 / 4000000000000)) (orderedInterval (-25110187880 / 1000000000000) (-25110187010 / 1000000000000), orderedInterval (67049166750 / 1000000000000) (67049167619 / 1000000000000))) = true
  rfl'

theorem compactCertificate358_stateChecks7 :
    compactCertificate358.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 21 12 (267870110475411 / 4000000000000)) (orderedInterval (-95421616359 / 1000000000000) (-95421615900 / 1000000000000), orderedInterval (20734087209 / 1000000000000) (20734087667 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (727319458099233 / 4000000000000)) (orderedInterval (23162068396 / 1000000000000) (23162068397 / 1000000000000), orderedInterval (54385473686 / 1000000000000) (54385473687 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 79 12 (993092539581441 / 4000000000000)) (orderedInterval (-38775995509 / 1000000000000) (-38775995508 / 1000000000000), orderedInterval (-32488953794 / 1000000000000) (-32488953793 / 1000000000000))) = true
  rfl'

theorem compactCertificate358_stateChecks8 :
    compactCertificate358.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 33 12 (419918084920467 / 4000000000000)) (orderedInterval (-67564933329 / 1000000000000) (-67564915919 / 1000000000000), orderedInterval (39040956578 / 1000000000000) (39040973988 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 136 12 (1706943702046707 / 4000000000000)) (orderedInterval (10094800933 / 1000000000000) (10094800934 / 1000000000000), orderedInterval (37269954598 / 1000000000000) (37269954599 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 91 12 (1140159286259613 / 4000000000000)) (orderedInterval (2840944189 / 1000000000000) (2840944193 / 1000000000000), orderedInterval (-47178852944 / 1000000000000) (-47178852940 / 1000000000000))) = true
  rfl'

theorem compactCertificate358_states : ∀ j,
    BesselStateValid (compactCertificate358.point j) (compactCertificate358.state j) :=
  compactCertificate358.statesValid_of_checks3 compactCertificate358_stateChecks0
    compactCertificate358_stateChecks1 compactCertificate358_stateChecks2
    compactCertificate358_stateChecks3 compactCertificate358_stateChecks4
    compactCertificate358_stateChecks5 compactCertificate358_stateChecks6
    compactCertificate358_stateChecks7 compactCertificate358_stateChecks8

theorem compactCertificate358_chunkChecks0_0 :
    compactCertificate358.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (459 / 2) 0 (IntervalRat.scale (459 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-42797857478 / 1000000000000) (-42797857477 / 1000000000000), orderedInterval (-30603397956 / 1000000000000) (-30603397955 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (676194645086559 / 4000000000000) 0 (IntervalRat.scale (459 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (11427917470 / 1000000000000) (11427917471 / 1000000000000), orderedInterval (60259769707 / 1000000000000) (60259769708 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (218667454925247 / 800000000000) 0 (IntervalRat.scale (459 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-34643509794 / 1000000000000) (-34643509793 / 1000000000000), orderedInterval (-33535965098 / 1000000000000) (-33535965097 / 1000000000000)))) (orderedInterval (-18890007116 / 1000000000000) (-18890007099 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (197311910982813 / 4000000000000) 0 (IntervalRat.scale (459 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-17497338023 / 1000000000000) (-17497337925 / 1000000000000), orderedInterval (112428531275 / 1000000000000) (112428531373 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (530007547115961 / 4000000000000) 0 (IntervalRat.scale (459 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (67468392063 / 1000000000000) (67468392065 / 1000000000000), orderedInterval (15638633722 / 1000000000000) (15638633724 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1439073591570837 / 4000000000000) 0 (IntervalRat.scale (459 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (28043145933 / 1000000000000) (28043159227 / 1000000000000), orderedInterval (-31393540320 / 1000000000000) (-31393527026 / 1000000000000)))) (orderedInterval (659644369 / 1000000000000) (659645343 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1060015094232381 / 4000000000000) 0 (IntervalRat.scale (459 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (46461196403 / 1000000000000) (46461201879 / 1000000000000), orderedInterval (-15697215677 / 1000000000000) (-15697210201 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1816353931345713 / 4000000000000) 0 (IntervalRat.scale (459 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (22877794420 / 1000000000000) (22877798312 / 1000000000000), orderedInterval (-29666036249 / 1000000000000) (-29666032357 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1337918084920467 / 4000000000000) 0 (IntervalRat.scale (459 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (33787509283 / 1000000000000) (33787572052 / 1000000000000), orderedInterval (-27649745465 / 1000000000000) (-27649682697 / 1000000000000)))) (orderedInterval (110934596 / 1000000000000) (110936246 / 1000000000000))) = true
  rfl'

theorem compactCertificate358_chunkChecks0_1 :
    compactCertificate358.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2052710403344541 / 4000000000000) 0 (IntervalRat.scale (459 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-33517077784 / 1000000000000) (-33517060691 / 1000000000000), orderedInterval (10856247508 / 1000000000000) (10856264600 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1185132903939189 / 4000000000000) 0 (IntervalRat.scale (459 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (45539764028 / 1000000000000) (45539765484 / 1000000000000), orderedInterval (-8726331543 / 1000000000000) (-8726330088 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2103039135135801 / 4000000000000) 0 (IntervalRat.scale (459 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-32940311873 / 1000000000000) (-32940290771 / 1000000000000), orderedInterval (11247055649 / 1000000000000) (11247076751 / 1000000000000)))) (orderedInterval (4647039305 / 1000000000000) (4647045541 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1964931959105469 / 4000000000000) 0 (IntervalRat.scale (459 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (33705925513 / 1000000000000) (33705949396 / 1000000000000), orderedInterval (-12678378522 / 1000000000000) (-12678354638 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1402268162656077 / 4000000000000) 0 (IntervalRat.scale (459 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-20665342965 / 1000000000000) (-20665341673 / 1000000000000), orderedInterval (37297638877 / 1000000000000) (37297640169 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1590022641347883 / 4000000000000) 0 (IntervalRat.scale (459 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (25520671068 / 1000000000000) (25520678576 / 1000000000000), orderedInterval (-30857934025 / 1000000000000) (-30857926517 / 1000000000000)))) (orderedInterval (-2691819808 / 1000000000000) (-2691819189 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1325595110162427 / 4000000000000) 0 (IntervalRat.scale (459 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-32195397310 / 1000000000000) (-32195360134 / 1000000000000), orderedInterval (29788521924 / 1000000000000) (29788559100 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1171203481094967 / 4000000000000) 0 (IntervalRat.scale (459 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-46083516534 / 1000000000000) (-46083516520 / 1000000000000), orderedInterval (-7031008883 / 1000000000000) (-7031008869 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (339460418669733 / 800000000000) 0 (IntervalRat.scale (459 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-32501381237 / 1000000000000) (-32501381236 / 1000000000000), orderedInterval (-21032290065 / 1000000000000) (-21032290064 / 1000000000000)))) (orderedInterval (1433260940 / 1000000000000) (1433261393 / 1000000000000))) = true
  rfl'

theorem compactCertificate358_chunkChecks0_2 :
    compactCertificate358.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (938965382863551 / 4000000000000) 0 (IntervalRat.scale (459 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (4848491129 / 1000000000000) (4848491139 / 1000000000000), orderedInterval (-51861108099 / 1000000000000) (-51861108089 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (795971353810311 / 4000000000000) 0 (IntervalRat.scale (459 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-54256355764 / 1000000000000) (-54256353211 / 1000000000000), orderedInterval (16119096317 / 1000000000000) (16119098869 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (498081915079533 / 4000000000000) 0 (IntervalRat.scale (459 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-25110187880 / 1000000000000) (-25110187010 / 1000000000000), orderedInterval (67049166750 / 1000000000000) (67049167619 / 1000000000000)))) (orderedInterval (1478201116 / 1000000000000) (1478201348 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (267870110475411 / 4000000000000) 0 (IntervalRat.scale (459 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-95421616359 / 1000000000000) (-95421615900 / 1000000000000), orderedInterval (20734087209 / 1000000000000) (20734087667 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (727319458099233 / 4000000000000) 0 (IntervalRat.scale (459 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (23162068396 / 1000000000000) (23162068397 / 1000000000000), orderedInterval (54385473686 / 1000000000000) (54385473687 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (993092539581441 / 4000000000000) 0 (IntervalRat.scale (459 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-38775995509 / 1000000000000) (-38775995508 / 1000000000000), orderedInterval (-32488953794 / 1000000000000) (-32488953793 / 1000000000000)))) (orderedInterval (4208245117 / 1000000000000) (4208245154 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (419918084920467 / 4000000000000) 0 (IntervalRat.scale (459 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-67564933329 / 1000000000000) (-67564915919 / 1000000000000), orderedInterval (39040956578 / 1000000000000) (39040973988 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1706943702046707 / 4000000000000) 0 (IntervalRat.scale (459 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (10094800933 / 1000000000000) (10094800934 / 1000000000000), orderedInterval (37269954598 / 1000000000000) (37269954599 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1140159286259613 / 4000000000000) 0 (IntervalRat.scale (459 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (2840944189 / 1000000000000) (2840944193 / 1000000000000), orderedInterval (-47178852944 / 1000000000000) (-47178852940 / 1000000000000)))) (orderedInterval (-1762074838 / 1000000000000) (-1762074668 / 1000000000000))) = true
  rfl'

theorem compactCertificate358_chunkChecks0 :
    compactCertificate358.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate358.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate358_chunkChecks0_0
    compactCertificate358_chunkChecks0_1 compactCertificate358_chunkChecks0_2

theorem compactCertificate358_chunkChecks1_0 :
    compactCertificate358.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (459 / 2) 1 (IntervalRat.scale (459 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-42797857478 / 1000000000000) (-42797857477 / 1000000000000), orderedInterval (-30603397956 / 1000000000000) (-30603397955 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (676194645086559 / 4000000000000) 1 (IntervalRat.scale (459 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (11427917470 / 1000000000000) (11427917471 / 1000000000000), orderedInterval (60259769707 / 1000000000000) (60259769708 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (218667454925247 / 800000000000) 1 (IntervalRat.scale (459 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-34643509794 / 1000000000000) (-34643509793 / 1000000000000), orderedInterval (-33535965098 / 1000000000000) (-33535965097 / 1000000000000)))) (orderedInterval (-14060315693 / 1000000000000) (-14060315674 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (197311910982813 / 4000000000000) 1 (IntervalRat.scale (459 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-17497338023 / 1000000000000) (-17497337925 / 1000000000000), orderedInterval (112428531275 / 1000000000000) (112428531373 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (530007547115961 / 4000000000000) 1 (IntervalRat.scale (459 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (67468392063 / 1000000000000) (67468392065 / 1000000000000), orderedInterval (15638633722 / 1000000000000) (15638633724 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1439073591570837 / 4000000000000) 1 (IntervalRat.scale (459 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (28043145933 / 1000000000000) (28043159227 / 1000000000000), orderedInterval (-31393540320 / 1000000000000) (-31393527026 / 1000000000000)))) (orderedInterval (3566029367 / 1000000000000) (3566030880 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1060015094232381 / 4000000000000) 1 (IntervalRat.scale (459 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (46461196403 / 1000000000000) (46461201879 / 1000000000000), orderedInterval (-15697215677 / 1000000000000) (-15697210201 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1816353931345713 / 4000000000000) 1 (IntervalRat.scale (459 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (22877794420 / 1000000000000) (22877798312 / 1000000000000), orderedInterval (-29666036249 / 1000000000000) (-29666032357 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1337918084920467 / 4000000000000) 1 (IntervalRat.scale (459 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (33787509283 / 1000000000000) (33787572052 / 1000000000000), orderedInterval (-27649745465 / 1000000000000) (-27649682697 / 1000000000000)))) (orderedInterval (836545185 / 1000000000000) (836547656 / 1000000000000))) = true
  rfl'

theorem compactCertificate358_chunkChecks1_1 :
    compactCertificate358.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2052710403344541 / 4000000000000) 1 (IntervalRat.scale (459 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-33517077784 / 1000000000000) (-33517060691 / 1000000000000), orderedInterval (10856247508 / 1000000000000) (10856264600 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1185132903939189 / 4000000000000) 1 (IntervalRat.scale (459 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (45539764028 / 1000000000000) (45539765484 / 1000000000000), orderedInterval (-8726331543 / 1000000000000) (-8726330088 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2103039135135801 / 4000000000000) 1 (IntervalRat.scale (459 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-32940311873 / 1000000000000) (-32940290771 / 1000000000000), orderedInterval (11247055649 / 1000000000000) (11247076751 / 1000000000000)))) (orderedInterval (-1485368225 / 1000000000000) (-1485354233 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1964931959105469 / 4000000000000) 1 (IntervalRat.scale (459 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (33705925513 / 1000000000000) (33705949396 / 1000000000000), orderedInterval (-12678378522 / 1000000000000) (-12678354638 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1402268162656077 / 4000000000000) 1 (IntervalRat.scale (459 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-20665342965 / 1000000000000) (-20665341673 / 1000000000000), orderedInterval (37297638877 / 1000000000000) (37297640169 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1590022641347883 / 4000000000000) 1 (IntervalRat.scale (459 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (25520671068 / 1000000000000) (25520678576 / 1000000000000), orderedInterval (-30857934025 / 1000000000000) (-30857926517 / 1000000000000)))) (orderedInterval (6147926494 / 1000000000000) (6147927714 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1325595110162427 / 4000000000000) 1 (IntervalRat.scale (459 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-32195397310 / 1000000000000) (-32195360134 / 1000000000000), orderedInterval (29788521924 / 1000000000000) (29788559100 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1171203481094967 / 4000000000000) 1 (IntervalRat.scale (459 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-46083516534 / 1000000000000) (-46083516520 / 1000000000000), orderedInterval (-7031008883 / 1000000000000) (-7031008869 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (339460418669733 / 800000000000) 1 (IntervalRat.scale (459 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-32501381237 / 1000000000000) (-32501381236 / 1000000000000), orderedInterval (-21032290065 / 1000000000000) (-21032290064 / 1000000000000)))) (orderedInterval (14403160 / 1000000000000) (14403814 / 1000000000000))) = true
  rfl'

theorem compactCertificate358_chunkChecks1_2 :
    compactCertificate358.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (938965382863551 / 4000000000000) 1 (IntervalRat.scale (459 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (4848491129 / 1000000000000) (4848491139 / 1000000000000), orderedInterval (-51861108099 / 1000000000000) (-51861108089 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (795971353810311 / 4000000000000) 1 (IntervalRat.scale (459 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-54256355764 / 1000000000000) (-54256353211 / 1000000000000), orderedInterval (16119096317 / 1000000000000) (16119098869 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (498081915079533 / 4000000000000) 1 (IntervalRat.scale (459 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-25110187880 / 1000000000000) (-25110187010 / 1000000000000), orderedInterval (67049166750 / 1000000000000) (67049167619 / 1000000000000)))) (orderedInterval (8874843517 / 1000000000000) (8874843713 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (267870110475411 / 4000000000000) 1 (IntervalRat.scale (459 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-95421616359 / 1000000000000) (-95421615900 / 1000000000000), orderedInterval (20734087209 / 1000000000000) (20734087667 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (727319458099233 / 4000000000000) 1 (IntervalRat.scale (459 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (23162068396 / 1000000000000) (23162068397 / 1000000000000), orderedInterval (54385473686 / 1000000000000) (54385473687 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (993092539581441 / 4000000000000) 1 (IntervalRat.scale (459 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-38775995509 / 1000000000000) (-38775995508 / 1000000000000), orderedInterval (-32488953794 / 1000000000000) (-32488953793 / 1000000000000)))) (orderedInterval (1604323434 / 1000000000000) (1604323462 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (419918084920467 / 4000000000000) 1 (IntervalRat.scale (459 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-67564933329 / 1000000000000) (-67564915919 / 1000000000000), orderedInterval (39040956578 / 1000000000000) (39040973988 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1706943702046707 / 4000000000000) 1 (IntervalRat.scale (459 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (10094800933 / 1000000000000) (10094800934 / 1000000000000), orderedInterval (37269954598 / 1000000000000) (37269954599 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1140159286259613 / 4000000000000) 1 (IntervalRat.scale (459 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (2840944189 / 1000000000000) (2840944193 / 1000000000000), orderedInterval (-47178852944 / 1000000000000) (-47178852940 / 1000000000000)))) (orderedInterval (5460706245 / 1000000000000) (5460706384 / 1000000000000))) = true
  rfl'

theorem compactCertificate358_chunkChecks1 :
    compactCertificate358.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate358.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate358_chunkChecks1_0
    compactCertificate358_chunkChecks1_1 compactCertificate358_chunkChecks1_2

theorem compactCertificate358_chunkChecks2_0 :
    compactCertificate358.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (459 / 2) 2 (IntervalRat.scale (459 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-42797857478 / 1000000000000) (-42797857477 / 1000000000000), orderedInterval (-30603397956 / 1000000000000) (-30603397955 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (676194645086559 / 4000000000000) 2 (IntervalRat.scale (459 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (11427917470 / 1000000000000) (11427917471 / 1000000000000), orderedInterval (60259769707 / 1000000000000) (60259769708 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (218667454925247 / 800000000000) 2 (IntervalRat.scale (459 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-34643509794 / 1000000000000) (-34643509793 / 1000000000000), orderedInterval (-33535965098 / 1000000000000) (-33535965097 / 1000000000000)))) (orderedInterval (19850716520 / 1000000000000) (19850716542 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (197311910982813 / 4000000000000) 2 (IntervalRat.scale (459 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-17497338023 / 1000000000000) (-17497337925 / 1000000000000), orderedInterval (112428531275 / 1000000000000) (112428531373 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (530007547115961 / 4000000000000) 2 (IntervalRat.scale (459 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (67468392063 / 1000000000000) (67468392065 / 1000000000000), orderedInterval (15638633722 / 1000000000000) (15638633724 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1439073591570837 / 4000000000000) 2 (IntervalRat.scale (459 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (28043145933 / 1000000000000) (28043159227 / 1000000000000), orderedInterval (-31393540320 / 1000000000000) (-31393527026 / 1000000000000)))) (orderedInterval (4053632816 / 1000000000000) (4053635189 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1060015094232381 / 4000000000000) 2 (IntervalRat.scale (459 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (46461196403 / 1000000000000) (46461201879 / 1000000000000), orderedInterval (-15697215677 / 1000000000000) (-15697210201 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1816353931345713 / 4000000000000) 2 (IntervalRat.scale (459 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (22877794420 / 1000000000000) (22877798312 / 1000000000000), orderedInterval (-29666036249 / 1000000000000) (-29666032357 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1337918084920467 / 4000000000000) 2 (IntervalRat.scale (459 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (33787509283 / 1000000000000) (33787572052 / 1000000000000), orderedInterval (-27649745465 / 1000000000000) (-27649682697 / 1000000000000)))) (orderedInterval (1024352974 / 1000000000000) (1024356717 / 1000000000000))) = true
  rfl'

theorem compactCertificate358_chunkChecks2_1 :
    compactCertificate358.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2052710403344541 / 4000000000000) 2 (IntervalRat.scale (459 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-33517077784 / 1000000000000) (-33517060691 / 1000000000000), orderedInterval (10856247508 / 1000000000000) (10856264600 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1185132903939189 / 4000000000000) 2 (IntervalRat.scale (459 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (45539764028 / 1000000000000) (45539765484 / 1000000000000), orderedInterval (-8726331543 / 1000000000000) (-8726330088 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2103039135135801 / 4000000000000) 2 (IntervalRat.scale (459 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-32940311873 / 1000000000000) (-32940290771 / 1000000000000), orderedInterval (11247055649 / 1000000000000) (11247076751 / 1000000000000)))) (orderedInterval (-10819505610 / 1000000000000) (-10819474036 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1964931959105469 / 4000000000000) 2 (IntervalRat.scale (459 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (33705925513 / 1000000000000) (33705949396 / 1000000000000), orderedInterval (-12678378522 / 1000000000000) (-12678354638 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1402268162656077 / 4000000000000) 2 (IntervalRat.scale (459 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-20665342965 / 1000000000000) (-20665341673 / 1000000000000), orderedInterval (37297638877 / 1000000000000) (37297640169 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1590022641347883 / 4000000000000) 2 (IntervalRat.scale (459 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (25520671068 / 1000000000000) (25520678576 / 1000000000000), orderedInterval (-30857934025 / 1000000000000) (-30857926517 / 1000000000000)))) (orderedInterval (7708235679 / 1000000000000) (7708238132 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1325595110162427 / 4000000000000) 2 (IntervalRat.scale (459 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-32195397310 / 1000000000000) (-32195360134 / 1000000000000), orderedInterval (29788521924 / 1000000000000) (29788559100 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1171203481094967 / 4000000000000) 2 (IntervalRat.scale (459 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-46083516534 / 1000000000000) (-46083516520 / 1000000000000), orderedInterval (-7031008883 / 1000000000000) (-7031008869 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (339460418669733 / 800000000000) 2 (IntervalRat.scale (459 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-32501381237 / 1000000000000) (-32501381236 / 1000000000000), orderedInterval (-21032290065 / 1000000000000) (-21032290064 / 1000000000000)))) (orderedInterval (-672740310 / 1000000000000) (-672739363 / 1000000000000))) = true
  rfl'

theorem compactCertificate358_chunkChecks2_2 :
    compactCertificate358.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (938965382863551 / 4000000000000) 2 (IntervalRat.scale (459 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (4848491129 / 1000000000000) (4848491139 / 1000000000000), orderedInterval (-51861108099 / 1000000000000) (-51861108089 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (795971353810311 / 4000000000000) 2 (IntervalRat.scale (459 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-54256355764 / 1000000000000) (-54256353211 / 1000000000000), orderedInterval (16119096317 / 1000000000000) (16119098869 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (498081915079533 / 4000000000000) 2 (IntervalRat.scale (459 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-25110187880 / 1000000000000) (-25110187010 / 1000000000000), orderedInterval (67049166750 / 1000000000000) (67049167619 / 1000000000000)))) (orderedInterval (-1295714544 / 1000000000000) (-1295714373 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (267870110475411 / 4000000000000) 2 (IntervalRat.scale (459 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-95421616359 / 1000000000000) (-95421615900 / 1000000000000), orderedInterval (20734087209 / 1000000000000) (20734087667 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (727319458099233 / 4000000000000) 2 (IntervalRat.scale (459 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (23162068396 / 1000000000000) (23162068397 / 1000000000000), orderedInterval (54385473686 / 1000000000000) (54385473687 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (993092539581441 / 4000000000000) 2 (IntervalRat.scale (459 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-38775995509 / 1000000000000) (-38775995508 / 1000000000000), orderedInterval (-32488953794 / 1000000000000) (-32488953793 / 1000000000000)))) (orderedInterval (-3304976897 / 1000000000000) (-3304976871 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (419918084920467 / 4000000000000) 2 (IntervalRat.scale (459 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-67564933329 / 1000000000000) (-67564915919 / 1000000000000), orderedInterval (39040956578 / 1000000000000) (39040973988 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1706943702046707 / 4000000000000) 2 (IntervalRat.scale (459 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (10094800933 / 1000000000000) (10094800934 / 1000000000000), orderedInterval (37269954598 / 1000000000000) (37269954599 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1140159286259613 / 4000000000000) 2 (IntervalRat.scale (459 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (2840944189 / 1000000000000) (2840944193 / 1000000000000), orderedInterval (-47178852944 / 1000000000000) (-47178852940 / 1000000000000)))) (orderedInterval (3724765594 / 1000000000000) (3724765750 / 1000000000000))) = true
  rfl'

theorem compactCertificate358_chunkChecks2 :
    compactCertificate358.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate358.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate358_chunkChecks2_0
    compactCertificate358_chunkChecks2_1 compactCertificate358_chunkChecks2_2

theorem compactCertificate358_chunkChecks3_0 :
    compactCertificate358.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (459 / 2) 3 (IntervalRat.scale (459 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-42797857478 / 1000000000000) (-42797857477 / 1000000000000), orderedInterval (-30603397956 / 1000000000000) (-30603397955 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (676194645086559 / 4000000000000) 3 (IntervalRat.scale (459 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (11427917470 / 1000000000000) (11427917471 / 1000000000000), orderedInterval (60259769707 / 1000000000000) (60259769708 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (218667454925247 / 800000000000) 3 (IntervalRat.scale (459 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-34643509794 / 1000000000000) (-34643509793 / 1000000000000), orderedInterval (-33535965098 / 1000000000000) (-33535965097 / 1000000000000)))) (orderedInterval (15143577700 / 1000000000000) (15143577725 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (197311910982813 / 4000000000000) 3 (IntervalRat.scale (459 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-17497338023 / 1000000000000) (-17497337925 / 1000000000000), orderedInterval (112428531275 / 1000000000000) (112428531373 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (530007547115961 / 4000000000000) 3 (IntervalRat.scale (459 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (67468392063 / 1000000000000) (67468392065 / 1000000000000), orderedInterval (15638633722 / 1000000000000) (15638633724 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1439073591570837 / 4000000000000) 3 (IntervalRat.scale (459 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (28043145933 / 1000000000000) (28043159227 / 1000000000000), orderedInterval (-31393540320 / 1000000000000) (-31393527026 / 1000000000000)))) (orderedInterval (-8712780113 / 1000000000000) (-8712776397 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1060015094232381 / 4000000000000) 3 (IntervalRat.scale (459 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (46461196403 / 1000000000000) (46461201879 / 1000000000000), orderedInterval (-15697215677 / 1000000000000) (-15697210201 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1816353931345713 / 4000000000000) 3 (IntervalRat.scale (459 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (22877794420 / 1000000000000) (22877798312 / 1000000000000), orderedInterval (-29666036249 / 1000000000000) (-29666032357 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1337918084920467 / 4000000000000) 3 (IntervalRat.scale (459 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (33787509283 / 1000000000000) (33787572052 / 1000000000000), orderedInterval (-27649745465 / 1000000000000) (-27649682697 / 1000000000000)))) (orderedInterval (-5023446615 / 1000000000000) (-5023440900 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate358_chunkChecks3_1 :
    compactCertificate358.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2052710403344541 / 4000000000000) 3 (IntervalRat.scale (459 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-33517077784 / 1000000000000) (-33517060691 / 1000000000000), orderedInterval (10856247508 / 1000000000000) (10856264600 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1185132903939189 / 4000000000000) 3 (IntervalRat.scale (459 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (45539764028 / 1000000000000) (45539765484 / 1000000000000), orderedInterval (-8726331543 / 1000000000000) (-8726330088 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2103039135135801 / 4000000000000) 3 (IntervalRat.scale (459 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-32940311873 / 1000000000000) (-32940290771 / 1000000000000), orderedInterval (11247055649 / 1000000000000) (11247076751 / 1000000000000)))) (orderedInterval (3782528734 / 1000000000000) (3782600008 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1964931959105469 / 4000000000000) 3 (IntervalRat.scale (459 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (33705925513 / 1000000000000) (33705949396 / 1000000000000), orderedInterval (-12678378522 / 1000000000000) (-12678354638 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1402268162656077 / 4000000000000) 3 (IntervalRat.scale (459 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-20665342965 / 1000000000000) (-20665341673 / 1000000000000), orderedInterval (37297638877 / 1000000000000) (37297640169 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1590022641347883 / 4000000000000) 3 (IntervalRat.scale (459 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (25520671068 / 1000000000000) (25520678576 / 1000000000000), orderedInterval (-30857934025 / 1000000000000) (-30857926517 / 1000000000000)))) (orderedInterval (-15660370770 / 1000000000000) (-15660365773 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1325595110162427 / 4000000000000) 3 (IntervalRat.scale (459 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-32195397310 / 1000000000000) (-32195360134 / 1000000000000), orderedInterval (29788521924 / 1000000000000) (29788559100 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1171203481094967 / 4000000000000) 3 (IntervalRat.scale (459 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-46083516534 / 1000000000000) (-46083516520 / 1000000000000), orderedInterval (-7031008883 / 1000000000000) (-7031008869 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (339460418669733 / 800000000000) 3 (IntervalRat.scale (459 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-32501381237 / 1000000000000) (-32501381236 / 1000000000000), orderedInterval (-21032290065 / 1000000000000) (-21032290064 / 1000000000000)))) (orderedInterval (1535257000 / 1000000000000) (1535258372 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate358_chunkChecks3_2 :
    compactCertificate358.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (938965382863551 / 4000000000000) 3 (IntervalRat.scale (459 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (4848491129 / 1000000000000) (4848491139 / 1000000000000), orderedInterval (-51861108099 / 1000000000000) (-51861108089 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (795971353810311 / 4000000000000) 3 (IntervalRat.scale (459 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-54256355764 / 1000000000000) (-54256353211 / 1000000000000), orderedInterval (16119096317 / 1000000000000) (16119098869 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (498081915079533 / 4000000000000) 3 (IntervalRat.scale (459 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-25110187880 / 1000000000000) (-25110187010 / 1000000000000), orderedInterval (67049166750 / 1000000000000) (67049167619 / 1000000000000)))) (orderedInterval (-8621511031 / 1000000000000) (-8621510880 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (267870110475411 / 4000000000000) 3 (IntervalRat.scale (459 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-95421616359 / 1000000000000) (-95421615900 / 1000000000000), orderedInterval (20734087209 / 1000000000000) (20734087667 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (727319458099233 / 4000000000000) 3 (IntervalRat.scale (459 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (23162068396 / 1000000000000) (23162068397 / 1000000000000), orderedInterval (54385473686 / 1000000000000) (54385473687 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (993092539581441 / 4000000000000) 3 (IntervalRat.scale (459 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-38775995509 / 1000000000000) (-38775995508 / 1000000000000), orderedInterval (-32488953794 / 1000000000000) (-32488953793 / 1000000000000)))) (orderedInterval (-2514717242 / 1000000000000) (-2514717216 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (419918084920467 / 4000000000000) 3 (IntervalRat.scale (459 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-67564933329 / 1000000000000) (-67564915919 / 1000000000000), orderedInterval (39040956578 / 1000000000000) (39040973988 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1706943702046707 / 4000000000000) 3 (IntervalRat.scale (459 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (10094800933 / 1000000000000) (10094800934 / 1000000000000), orderedInterval (37269954598 / 1000000000000) (37269954599 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1140159286259613 / 4000000000000) 3 (IntervalRat.scale (459 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (2840944189 / 1000000000000) (2840944193 / 1000000000000), orderedInterval (-47178852944 / 1000000000000) (-47178852940 / 1000000000000)))) (orderedInterval (2505897908 / 1000000000000) (2505898123 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate358_chunkChecks3 :
    compactCertificate358.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate358.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate358_chunkChecks3_0
    compactCertificate358_chunkChecks3_1 compactCertificate358_chunkChecks3_2

theorem compactCertificate358_chunkChecks4_0 :
    compactCertificate358.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (459 / 2) 4 (IntervalRat.scale (459 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-42797857478 / 1000000000000) (-42797857477 / 1000000000000), orderedInterval (-30603397956 / 1000000000000) (-30603397955 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (676194645086559 / 4000000000000) 4 (IntervalRat.scale (459 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (11427917470 / 1000000000000) (11427917471 / 1000000000000), orderedInterval (60259769707 / 1000000000000) (60259769708 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (218667454925247 / 800000000000) 4 (IntervalRat.scale (459 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-34643509794 / 1000000000000) (-34643509793 / 1000000000000), orderedInterval (-33535965098 / 1000000000000) (-33535965097 / 1000000000000)))) (orderedInterval (-21154221789 / 1000000000000) (-21154221760 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (197311910982813 / 4000000000000) 4 (IntervalRat.scale (459 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-17497338023 / 1000000000000) (-17497337925 / 1000000000000), orderedInterval (112428531275 / 1000000000000) (112428531373 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (530007547115961 / 4000000000000) 4 (IntervalRat.scale (459 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (67468392063 / 1000000000000) (67468392065 / 1000000000000), orderedInterval (15638633722 / 1000000000000) (15638633724 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1439073591570837 / 4000000000000) 4 (IntervalRat.scale (459 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (28043145933 / 1000000000000) (28043159227 / 1000000000000), orderedInterval (-31393540320 / 1000000000000) (-31393527026 / 1000000000000)))) (orderedInterval (-11688994624 / 1000000000000) (-11688988785 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1060015094232381 / 4000000000000) 4 (IntervalRat.scale (459 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (46461196403 / 1000000000000) (46461201879 / 1000000000000), orderedInterval (-15697215677 / 1000000000000) (-15697210201 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1816353931345713 / 4000000000000) 4 (IntervalRat.scale (459 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (22877794420 / 1000000000000) (22877798312 / 1000000000000), orderedInterval (-29666036249 / 1000000000000) (-29666032357 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1337918084920467 / 4000000000000) 4 (IntervalRat.scale (459 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (33787509283 / 1000000000000) (33787572052 / 1000000000000), orderedInterval (-27649745465 / 1000000000000) (-27649682697 / 1000000000000)))) (orderedInterval (-7086731297 / 1000000000000) (-7086722429 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate358_chunkChecks4_1 :
    compactCertificate358.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2052710403344541 / 4000000000000) 4 (IntervalRat.scale (459 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-33517077784 / 1000000000000) (-33517060691 / 1000000000000), orderedInterval (10856247508 / 1000000000000) (10856264600 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1185132903939189 / 4000000000000) 4 (IntervalRat.scale (459 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (45539764028 / 1000000000000) (45539765484 / 1000000000000), orderedInterval (-8726331543 / 1000000000000) (-8726330088 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2103039135135801 / 4000000000000) 4 (IntervalRat.scale (459 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-32940311873 / 1000000000000) (-32940290771 / 1000000000000), orderedInterval (11247055649 / 1000000000000) (11247076751 / 1000000000000)))) (orderedInterval (29252114247 / 1000000000000) (29252275679 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1964931959105469 / 4000000000000) 4 (IntervalRat.scale (459 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (33705925513 / 1000000000000) (33705949396 / 1000000000000), orderedInterval (-12678378522 / 1000000000000) (-12678354638 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1402268162656077 / 4000000000000) 4 (IntervalRat.scale (459 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-20665342965 / 1000000000000) (-20665341673 / 1000000000000), orderedInterval (37297638877 / 1000000000000) (37297640169 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1590022641347883 / 4000000000000) 4 (IntervalRat.scale (459 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (25520671068 / 1000000000000) (25520678576 / 1000000000000), orderedInterval (-30857934025 / 1000000000000) (-30857926517 / 1000000000000)))) (orderedInterval (-24437659078 / 1000000000000) (-24437648761 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1325595110162427 / 4000000000000) 4 (IntervalRat.scale (459 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-32195397310 / 1000000000000) (-32195360134 / 1000000000000), orderedInterval (29788521924 / 1000000000000) (29788559100 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1171203481094967 / 4000000000000) 4 (IntervalRat.scale (459 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-46083516534 / 1000000000000) (-46083516520 / 1000000000000), orderedInterval (-7031008883 / 1000000000000) (-7031008869 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (339460418669733 / 800000000000) 4 (IntervalRat.scale (459 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-32501381237 / 1000000000000) (-32501381236 / 1000000000000), orderedInterval (-21032290065 / 1000000000000) (-21032290064 / 1000000000000)))) (orderedInterval (-4367307774 / 1000000000000) (-4367305778 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate358_chunkChecks4_2 :
    compactCertificate358.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (938965382863551 / 4000000000000) 4 (IntervalRat.scale (459 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (4848491129 / 1000000000000) (4848491139 / 1000000000000), orderedInterval (-51861108099 / 1000000000000) (-51861108089 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (795971353810311 / 4000000000000) 4 (IntervalRat.scale (459 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-54256355764 / 1000000000000) (-54256353211 / 1000000000000), orderedInterval (16119096317 / 1000000000000) (16119098869 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (498081915079533 / 4000000000000) 4 (IntervalRat.scale (459 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-25110187880 / 1000000000000) (-25110187010 / 1000000000000), orderedInterval (67049166750 / 1000000000000) (67049167619 / 1000000000000)))) (orderedInterval (891487620 / 1000000000000) (891487756 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (267870110475411 / 4000000000000) 4 (IntervalRat.scale (459 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-95421616359 / 1000000000000) (-95421615900 / 1000000000000), orderedInterval (20734087209 / 1000000000000) (20734087667 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (727319458099233 / 4000000000000) 4 (IntervalRat.scale (459 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (23162068396 / 1000000000000) (23162068397 / 1000000000000), orderedInterval (54385473686 / 1000000000000) (54385473687 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (993092539581441 / 4000000000000) 4 (IntervalRat.scale (459 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-38775995509 / 1000000000000) (-38775995508 / 1000000000000), orderedInterval (-32488953794 / 1000000000000) (-32488953793 / 1000000000000)))) (orderedInterval (3897626921 / 1000000000000) (3897626948 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (419918084920467 / 4000000000000) 4 (IntervalRat.scale (459 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-67564933329 / 1000000000000) (-67564915919 / 1000000000000), orderedInterval (39040956578 / 1000000000000) (39040973988 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1706943702046707 / 4000000000000) 4 (IntervalRat.scale (459 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (10094800933 / 1000000000000) (10094800934 / 1000000000000), orderedInterval (37269954598 / 1000000000000) (37269954599 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1140159286259613 / 4000000000000) 4 (IntervalRat.scale (459 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (2840944189 / 1000000000000) (2840944193 / 1000000000000), orderedInterval (-47178852944 / 1000000000000) (-47178852940 / 1000000000000)))) (orderedInterval (-11130831432 / 1000000000000) (-11130831097 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate358_chunkChecks4 :
    compactCertificate358.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate358.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate358_chunkChecks4_0
    compactCertificate358_chunkChecks4_1 compactCertificate358_chunkChecks4_2

theorem compactCertificate358_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate358.chunkCheck r b = true :=
  compactCertificate358.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate358_chunkChecks0
    · exact compactCertificate358_chunkChecks1
    · exact compactCertificate358_chunkChecks2
    · exact compactCertificate358_chunkChecks3
    · exact compactCertificate358_chunkChecks4)

theorem compactCertificate358_coefficient0 :
    compactCertificate358.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate358_coefficient1 :
    compactCertificate358.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate358_coefficient2 :
    compactCertificate358.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate358_coefficient3 :
    compactCertificate358.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate358_coefficient4 :
    compactCertificate358.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate358_coefficients : ∀ r : Fin 5,
    compactCertificate358.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate358_coefficient0
  · exact compactCertificate358_coefficient1
  · exact compactCertificate358_coefficient2
  · exact compactCertificate358_coefficient3
  · exact compactCertificate358_coefficient4

theorem compactCertificate358_lower : (1 : ℚ) ≤ compactCertificate358.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate358, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate358_proves {t : ℝ} (ht : t ∈ compactCertificate358.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate358.proves compactCertificate358_states compactCertificate358_chunks
    compactCertificate358_coefficients compactCertificate358_lower ht

end Erdos232
