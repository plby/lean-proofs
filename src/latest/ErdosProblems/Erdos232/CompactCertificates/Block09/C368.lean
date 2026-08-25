/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate368 : CompactCertificate where
  left := 239
  right := 240
  center := 479 / 2
  grid := fun i =>
    match i.val with
    | 0 => 76
    | 1 => 56
    | 2 => 91
    | 3 => 16
    | 4 => 44
    | 5 => 120
    | 6 => 88
    | 7 => 151
    | 8 => 111
    | 9 => 171
    | 10 => 98
    | 11 => 175
    | 12 => 163
    | 13 => 117
    | 14 => 132
    | 15 => 110
    | 16 => 97
    | 17 => 141
    | 18 => 78
    | 19 => 66
    | 20 => 41
    | 21 => 22
    | 22 => 60
    | 23 => 83
    | 24 => 35
    | 25 => 142
    | _ => 95
  point := fun i =>
    match i.val with
    | 0 => 479 / 2
    | 1 => 705658464044579 / 4000000000000
    | 2 => 228195448603907 / 800000000000
    | 3 => 205909379870953 / 4000000000000
    | 4 => 553101557883541 / 4000000000000
    | 5 => 1501778323229697 / 4000000000000
    | 6 => 1106203115767561 / 4000000000000
    | 7 => 1895497893495853 / 4000000000000
    | 8 => 1396215169230727 / 4000000000000
    | 9 => 2142153122444521 / 4000000000000
    | 10 => 1236772681888609 / 4000000000000
    | 11 => 2194674827298581 / 4000000000000
    | 12 => 2050549909393289 / 4000000000000
    | 13 => 1463369171922137 / 4000000000000
    | 14 => 1659304673650623 / 4000000000000
    | 15 => 1383355245681487 / 4000000000000
    | 16 => 1222236312515227 / 4000000000000
    | 17 => 354251722315473 / 800000000000
    | 18 => 979878907171331 / 4000000000000
    | 19 => 830654201470891 / 4000000000000
    | 20 => 519784830769273 / 4000000000000
    | 21 => 279542010713991 / 4000000000000
    | 22 => 759010937754973 / 4000000000000
    | 23 => 1036364545663421 / 4000000000000
    | 24 => 438215169230727 / 4000000000000
    | 25 => 1781320333944167 / 4000000000000
    | _ => 1189839429451753 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (51500062396 / 1000000000000) (51500062442 / 1000000000000), orderedInterval (2312802619 / 1000000000000) (2312802665 / 1000000000000))
    | 1 => (orderedInterval (57376876792 / 1000000000000) (57376876793 / 1000000000000), orderedInterval (17628915890 / 1000000000000) (17628915891 / 1000000000000))
    | 2 => (orderedInterval (-6795267333 / 1000000000000) (-6795267332 / 1000000000000), orderedInterval (-46739217203 / 1000000000000) (-46739217202 / 1000000000000))
    | 3 => (orderedInterval (101355590503 / 1000000000000) (101355595622 / 1000000000000), orderedInterval (-46740769169 / 1000000000000) (-46740764050 / 1000000000000))
    | 4 => (orderedInterval (50061684893 / 1000000000000) (50061684894 / 1000000000000), orderedInterval (45620991159 / 1000000000000) (45620991160 / 1000000000000))
    | 5 => (orderedInterval (-28412442845 / 1000000000000) (-28412426106 / 1000000000000), orderedInterval (29843468201 / 1000000000000) (29843484940 / 1000000000000))
    | 6 => (orderedInterval (36843633668 / 1000000000000) (36843633669 / 1000000000000), orderedInterval (30666847159 / 1000000000000) (30666847160 / 1000000000000))
    | 7 => (orderedInterval (-10098128770 / 1000000000000) (-10098128769 / 1000000000000), orderedInterval (-35223758622 / 1000000000000) (-35223758621 / 1000000000000))
    | 8 => (orderedInterval (-38478132951 / 1000000000000) (-38478132950 / 1000000000000), orderedInterval (-18472602822 / 1000000000000) (-18472602821 / 1000000000000))
    | 9 => (orderedInterval (26768107218 / 1000000000000) (26768133122 / 1000000000000), orderedInterval (-21755514824 / 1000000000000) (-21755488920 / 1000000000000))
    | 10 => (orderedInterval (39121006411 / 1000000000000) (39121055847 / 1000000000000), orderedInterval (-23052731254 / 1000000000000) (-23052681818 / 1000000000000))
    | 11 => (orderedInterval (10871409904 / 1000000000000) (10871409934 / 1000000000000), orderedInterval (-32291664588 / 1000000000000) (-32291664558 / 1000000000000))
    | 12 => (orderedInterval (-34329768111 / 1000000000000) (-34329768087 / 1000000000000), orderedInterval (-7923795540 / 1000000000000) (-7923795516 / 1000000000000))
    | 13 => (orderedInterval (33662450721 / 1000000000000) (33662537041 / 1000000000000), orderedInterval (-24683094581 / 1000000000000) (-24683008261 / 1000000000000))
    | 14 => (orderedInterval (31192083626 / 1000000000000) (31192083627 / 1000000000000), orderedInterval (23663036299 / 1000000000000) (23663036300 / 1000000000000))
    | 15 => (orderedInterval (37187650428 / 1000000000000) (37187650429 / 1000000000000), orderedInterval (21344291383 / 1000000000000) (21344291384 / 1000000000000))
    | 16 => (orderedInterval (-45610566939 / 1000000000000) (-45610566694 / 1000000000000), orderedInterval (1844460766 / 1000000000000) (1844461011 / 1000000000000))
    | 17 => (orderedInterval (-22497496525 / 1000000000000) (-22497496524 / 1000000000000), orderedInterval (-30495563377 / 1000000000000) (-30495563376 / 1000000000000))
    | 18 => (orderedInterval (33244214885 / 1000000000000) (33244214886 / 1000000000000), orderedInterval (38579166508 / 1000000000000) (38579166509 / 1000000000000))
    | 19 => (orderedInterval (49425320849 / 1000000000000) (49425320850 / 1000000000000), orderedInterval (24836220541 / 1000000000000) (24836220542 / 1000000000000))
    | 20 => (orderedInterval (-65639970826 / 1000000000000) (-65639967150 / 1000000000000), orderedInterval (24552134237 / 1000000000000) (24552137913 / 1000000000000))
    | 21 => (orderedInterval (95428969485 / 1000000000000) (95428969506 / 1000000000000), orderedInterval (913265369 / 1000000000000) (913265389 / 1000000000000))
    | 22 => (orderedInterval (51612248243 / 1000000000000) (51612264556 / 1000000000000), orderedInterval (-26426016495 / 1000000000000) (-26426000181 / 1000000000000))
    | 23 => (orderedInterval (38082742172 / 1000000000000) (38082822256 / 1000000000000), orderedInterval (-31804077534 / 1000000000000) (-31803997449 / 1000000000000))
    | 24 => (orderedInterval (-28438365175 / 1000000000000) (-28438365174 / 1000000000000), orderedInterval (-70597345501 / 1000000000000) (-70597345500 / 1000000000000))
    | 25 => (orderedInterval (341948522 / 1000000000000) (341948523 / 1000000000000), orderedInterval (37807417137 / 1000000000000) (37807417138 / 1000000000000))
    | _ => (orderedInterval (9483874932 / 1000000000000) (9483874966 / 1000000000000), orderedInterval (-45295584319 / 1000000000000) (-45295584285 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (20548709009 / 1000000000000) (20548709045 / 1000000000000)
      | 1 => orderedInterval (2748032329 / 1000000000000) (2748033604 / 1000000000000)
      | 2 => orderedInterval (-618473869 / 1000000000000) (-618473855 / 1000000000000)
      | 3 => orderedInterval (-312394485 / 1000000000000) (-312386119 / 1000000000000)
      | 4 => orderedInterval (3645126148 / 1000000000000) (3645134340 / 1000000000000)
      | 5 => orderedInterval (2463547095 / 1000000000000) (2463547133 / 1000000000000)
      | 6 => orderedInterval (-10249896755 / 1000000000000) (-10249896574 / 1000000000000)
      | 7 => orderedInterval (-5851651889 / 1000000000000) (-5851645352 / 1000000000000)
      | _ => orderedInterval (-1978697566 / 1000000000000) (-1978697493 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-2228853565 / 1000000000000) (-2228853527 / 1000000000000)
      | 1 => orderedInterval (-2255111577 / 1000000000000) (-2255109666 / 1000000000000)
      | 2 => orderedInterval (1498969368 / 1000000000000) (1498969392 / 1000000000000)
      | 3 => orderedInterval (-4077328416 / 1000000000000) (-4077313188 / 1000000000000)
      | 4 => orderedInterval (-3466624705 / 1000000000000) (-3466612188 / 1000000000000)
      | 5 => orderedInterval (-1222396504 / 1000000000000) (-1222396452 / 1000000000000)
      | 6 => orderedInterval (-7094582277 / 1000000000000) (-7094582156 / 1000000000000)
      | 7 => orderedInterval (3106877485 / 1000000000000) (3106884444 / 1000000000000)
      | _ => orderedInterval (4638162764 / 1000000000000) (4638162866 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-20127973164 / 1000000000000) (-20127973124 / 1000000000000)
      | 1 => orderedInterval (-5512649070 / 1000000000000) (-5512646089 / 1000000000000)
      | 2 => orderedInterval (749675480 / 1000000000000) (749675523 / 1000000000000)
      | 3 => orderedInterval (10857224881 / 1000000000000) (10857254507 / 1000000000000)
      | 4 => orderedInterval (-9778938614 / 1000000000000) (-9778919437 / 1000000000000)
      | 5 => orderedInterval (-3169768601 / 1000000000000) (-3169768528 / 1000000000000)
      | 6 => orderedInterval (8322938946 / 1000000000000) (8322939036 / 1000000000000)
      | 7 => orderedInterval (4287706344 / 1000000000000) (4287713814 / 1000000000000)
      | _ => orderedInterval (2857638399 / 1000000000000) (2857638547 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (3735194022 / 1000000000000) (3735194066 / 1000000000000)
      | 1 => orderedInterval (7870285552 / 1000000000000) (7870290217 / 1000000000000)
      | 2 => orderedInterval (-7036532292 / 1000000000000) (-7036532215 / 1000000000000)
      | 3 => orderedInterval (15601036527 / 1000000000000) (15601096966 / 1000000000000)
      | 4 => orderedInterval (7579435415 / 1000000000000) (7579464723 / 1000000000000)
      | 5 => orderedInterval (4425347215 / 1000000000000) (4425347321 / 1000000000000)
      | 6 => orderedInterval (7354690118 / 1000000000000) (7354690190 / 1000000000000)
      | 7 => orderedInterval (-3401429814 / 1000000000000) (-3401421802 / 1000000000000)
      | _ => orderedInterval (3531673846 / 1000000000000) (3531674072 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (19736343826 / 1000000000000) (19736343875 / 1000000000000)
      | 1 => orderedInterval (12332571046 / 1000000000000) (12332578375 / 1000000000000)
      | 2 => orderedInterval (636655683 / 1000000000000) (636655824 / 1000000000000)
      | 3 => orderedInterval (-68421284792 / 1000000000000) (-68421156883 / 1000000000000)
      | 4 => orderedInterval (28855671492 / 1000000000000) (28855716411 / 1000000000000)
      | 5 => orderedInterval (2014143397 / 1000000000000) (2014143556 / 1000000000000)
      | 6 => orderedInterval (-7645627281 / 1000000000000) (-7645627219 / 1000000000000)
      | 7 => orderedInterval (-4442971233 / 1000000000000) (-4442962587 / 1000000000000)
      | _ => orderedInterval (-4603885894 / 1000000000000) (-4603885537 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (10394300017 / 1000000000000) (10394324729 / 1000000000000)
    | 1 => orderedInterval (-11100887427 / 1000000000000) (-11100850475 / 1000000000000)
    | 2 => orderedInterval (-11514145399 / 1000000000000) (-11514085751 / 1000000000000)
    | 3 => orderedInterval (39659700589 / 1000000000000) (39659803538 / 1000000000000)
    | _ => orderedInterval (-21538383756 / 1000000000000) (-21538194185 / 1000000000000)

theorem compactCertificate368_stateChecks0 :
    compactCertificate368.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 76 12 (479 / 2)) (orderedInterval (51500062396 / 1000000000000) (51500062442 / 1000000000000), orderedInterval (2312802619 / 1000000000000) (2312802665 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 56 12 (705658464044579 / 4000000000000)) (orderedInterval (57376876792 / 1000000000000) (57376876793 / 1000000000000), orderedInterval (17628915890 / 1000000000000) (17628915891 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 91 12 (228195448603907 / 800000000000)) (orderedInterval (-6795267333 / 1000000000000) (-6795267332 / 1000000000000), orderedInterval (-46739217203 / 1000000000000) (-46739217202 / 1000000000000))) = true
  rfl'

theorem compactCertificate368_stateChecks1 :
    compactCertificate368.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 16 12 (205909379870953 / 4000000000000)) (orderedInterval (101355590503 / 1000000000000) (101355595622 / 1000000000000), orderedInterval (-46740769169 / 1000000000000) (-46740764050 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 44 12 (553101557883541 / 4000000000000)) (orderedInterval (50061684893 / 1000000000000) (50061684894 / 1000000000000), orderedInterval (45620991159 / 1000000000000) (45620991160 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 120 12 (1501778323229697 / 4000000000000)) (orderedInterval (-28412442845 / 1000000000000) (-28412426106 / 1000000000000), orderedInterval (29843468201 / 1000000000000) (29843484940 / 1000000000000))) = true
  rfl'

theorem compactCertificate368_stateChecks2 :
    compactCertificate368.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 88 12 (1106203115767561 / 4000000000000)) (orderedInterval (36843633668 / 1000000000000) (36843633669 / 1000000000000), orderedInterval (30666847159 / 1000000000000) (30666847160 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 151 12 (1895497893495853 / 4000000000000)) (orderedInterval (-10098128770 / 1000000000000) (-10098128769 / 1000000000000), orderedInterval (-35223758622 / 1000000000000) (-35223758621 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 111 12 (1396215169230727 / 4000000000000)) (orderedInterval (-38478132951 / 1000000000000) (-38478132950 / 1000000000000), orderedInterval (-18472602822 / 1000000000000) (-18472602821 / 1000000000000))) = true
  rfl'

theorem compactCertificate368_stateChecks3 :
    compactCertificate368.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 171 12 (2142153122444521 / 4000000000000)) (orderedInterval (26768107218 / 1000000000000) (26768133122 / 1000000000000), orderedInterval (-21755514824 / 1000000000000) (-21755488920 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 98 12 (1236772681888609 / 4000000000000)) (orderedInterval (39121006411 / 1000000000000) (39121055847 / 1000000000000), orderedInterval (-23052731254 / 1000000000000) (-23052681818 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 175 12 (2194674827298581 / 4000000000000)) (orderedInterval (10871409904 / 1000000000000) (10871409934 / 1000000000000), orderedInterval (-32291664588 / 1000000000000) (-32291664558 / 1000000000000))) = true
  rfl'

theorem compactCertificate368_stateChecks4 :
    compactCertificate368.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 163 12 (2050549909393289 / 4000000000000)) (orderedInterval (-34329768111 / 1000000000000) (-34329768087 / 1000000000000), orderedInterval (-7923795540 / 1000000000000) (-7923795516 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 117 12 (1463369171922137 / 4000000000000)) (orderedInterval (33662450721 / 1000000000000) (33662537041 / 1000000000000), orderedInterval (-24683094581 / 1000000000000) (-24683008261 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 132 12 (1659304673650623 / 4000000000000)) (orderedInterval (31192083626 / 1000000000000) (31192083627 / 1000000000000), orderedInterval (23663036299 / 1000000000000) (23663036300 / 1000000000000))) = true
  rfl'

theorem compactCertificate368_stateChecks5 :
    compactCertificate368.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 110 12 (1383355245681487 / 4000000000000)) (orderedInterval (37187650428 / 1000000000000) (37187650429 / 1000000000000), orderedInterval (21344291383 / 1000000000000) (21344291384 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 97 12 (1222236312515227 / 4000000000000)) (orderedInterval (-45610566939 / 1000000000000) (-45610566694 / 1000000000000), orderedInterval (1844460766 / 1000000000000) (1844461011 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 141 12 (354251722315473 / 800000000000)) (orderedInterval (-22497496525 / 1000000000000) (-22497496524 / 1000000000000), orderedInterval (-30495563377 / 1000000000000) (-30495563376 / 1000000000000))) = true
  rfl'

theorem compactCertificate368_stateChecks6 :
    compactCertificate368.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 78 12 (979878907171331 / 4000000000000)) (orderedInterval (33244214885 / 1000000000000) (33244214886 / 1000000000000), orderedInterval (38579166508 / 1000000000000) (38579166509 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (830654201470891 / 4000000000000)) (orderedInterval (49425320849 / 1000000000000) (49425320850 / 1000000000000), orderedInterval (24836220541 / 1000000000000) (24836220542 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 41 12 (519784830769273 / 4000000000000)) (orderedInterval (-65639970826 / 1000000000000) (-65639967150 / 1000000000000), orderedInterval (24552134237 / 1000000000000) (24552137913 / 1000000000000))) = true
  rfl'

theorem compactCertificate368_stateChecks7 :
    compactCertificate368.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 22 12 (279542010713991 / 4000000000000)) (orderedInterval (95428969485 / 1000000000000) (95428969506 / 1000000000000), orderedInterval (913265369 / 1000000000000) (913265389 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 60 12 (759010937754973 / 4000000000000)) (orderedInterval (51612248243 / 1000000000000) (51612264556 / 1000000000000), orderedInterval (-26426016495 / 1000000000000) (-26426000181 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 83 12 (1036364545663421 / 4000000000000)) (orderedInterval (38082742172 / 1000000000000) (38082822256 / 1000000000000), orderedInterval (-31804077534 / 1000000000000) (-31803997449 / 1000000000000))) = true
  rfl'

theorem compactCertificate368_stateChecks8 :
    compactCertificate368.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 35 12 (438215169230727 / 4000000000000)) (orderedInterval (-28438365175 / 1000000000000) (-28438365174 / 1000000000000), orderedInterval (-70597345501 / 1000000000000) (-70597345500 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 142 12 (1781320333944167 / 4000000000000)) (orderedInterval (341948522 / 1000000000000) (341948523 / 1000000000000), orderedInterval (37807417137 / 1000000000000) (37807417138 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 95 12 (1189839429451753 / 4000000000000)) (orderedInterval (9483874932 / 1000000000000) (9483874966 / 1000000000000), orderedInterval (-45295584319 / 1000000000000) (-45295584285 / 1000000000000))) = true
  rfl'

theorem compactCertificate368_states : ∀ j,
    BesselStateValid (compactCertificate368.point j) (compactCertificate368.state j) :=
  compactCertificate368.statesValid_of_checks3 compactCertificate368_stateChecks0
    compactCertificate368_stateChecks1 compactCertificate368_stateChecks2
    compactCertificate368_stateChecks3 compactCertificate368_stateChecks4
    compactCertificate368_stateChecks5 compactCertificate368_stateChecks6
    compactCertificate368_stateChecks7 compactCertificate368_stateChecks8

theorem compactCertificate368_chunkChecks0_0 :
    compactCertificate368.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (479 / 2) 0 (IntervalRat.scale (479 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (51500062396 / 1000000000000) (51500062442 / 1000000000000), orderedInterval (2312802619 / 1000000000000) (2312802665 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (705658464044579 / 4000000000000) 0 (IntervalRat.scale (479 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (57376876792 / 1000000000000) (57376876793 / 1000000000000), orderedInterval (17628915890 / 1000000000000) (17628915891 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (228195448603907 / 800000000000) 0 (IntervalRat.scale (479 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-6795267333 / 1000000000000) (-6795267332 / 1000000000000), orderedInterval (-46739217203 / 1000000000000) (-46739217202 / 1000000000000)))) (orderedInterval (20548709009 / 1000000000000) (20548709045 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (205909379870953 / 4000000000000) 0 (IntervalRat.scale (479 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (101355590503 / 1000000000000) (101355595622 / 1000000000000), orderedInterval (-46740769169 / 1000000000000) (-46740764050 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (553101557883541 / 4000000000000) 0 (IntervalRat.scale (479 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (50061684893 / 1000000000000) (50061684894 / 1000000000000), orderedInterval (45620991159 / 1000000000000) (45620991160 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1501778323229697 / 4000000000000) 0 (IntervalRat.scale (479 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-28412442845 / 1000000000000) (-28412426106 / 1000000000000), orderedInterval (29843468201 / 1000000000000) (29843484940 / 1000000000000)))) (orderedInterval (2748032329 / 1000000000000) (2748033604 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1106203115767561 / 4000000000000) 0 (IntervalRat.scale (479 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (36843633668 / 1000000000000) (36843633669 / 1000000000000), orderedInterval (30666847159 / 1000000000000) (30666847160 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1895497893495853 / 4000000000000) 0 (IntervalRat.scale (479 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-10098128770 / 1000000000000) (-10098128769 / 1000000000000), orderedInterval (-35223758622 / 1000000000000) (-35223758621 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1396215169230727 / 4000000000000) 0 (IntervalRat.scale (479 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-38478132951 / 1000000000000) (-38478132950 / 1000000000000), orderedInterval (-18472602822 / 1000000000000) (-18472602821 / 1000000000000)))) (orderedInterval (-618473869 / 1000000000000) (-618473855 / 1000000000000))) = true
  rfl'

theorem compactCertificate368_chunkChecks0_1 :
    compactCertificate368.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2142153122444521 / 4000000000000) 0 (IntervalRat.scale (479 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (26768107218 / 1000000000000) (26768133122 / 1000000000000), orderedInterval (-21755514824 / 1000000000000) (-21755488920 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1236772681888609 / 4000000000000) 0 (IntervalRat.scale (479 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (39121006411 / 1000000000000) (39121055847 / 1000000000000), orderedInterval (-23052731254 / 1000000000000) (-23052681818 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2194674827298581 / 4000000000000) 0 (IntervalRat.scale (479 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (10871409904 / 1000000000000) (10871409934 / 1000000000000), orderedInterval (-32291664588 / 1000000000000) (-32291664558 / 1000000000000)))) (orderedInterval (-312394485 / 1000000000000) (-312386119 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2050549909393289 / 4000000000000) 0 (IntervalRat.scale (479 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-34329768111 / 1000000000000) (-34329768087 / 1000000000000), orderedInterval (-7923795540 / 1000000000000) (-7923795516 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1463369171922137 / 4000000000000) 0 (IntervalRat.scale (479 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (33662450721 / 1000000000000) (33662537041 / 1000000000000), orderedInterval (-24683094581 / 1000000000000) (-24683008261 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1659304673650623 / 4000000000000) 0 (IntervalRat.scale (479 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (31192083626 / 1000000000000) (31192083627 / 1000000000000), orderedInterval (23663036299 / 1000000000000) (23663036300 / 1000000000000)))) (orderedInterval (3645126148 / 1000000000000) (3645134340 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1383355245681487 / 4000000000000) 0 (IntervalRat.scale (479 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (37187650428 / 1000000000000) (37187650429 / 1000000000000), orderedInterval (21344291383 / 1000000000000) (21344291384 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1222236312515227 / 4000000000000) 0 (IntervalRat.scale (479 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-45610566939 / 1000000000000) (-45610566694 / 1000000000000), orderedInterval (1844460766 / 1000000000000) (1844461011 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (354251722315473 / 800000000000) 0 (IntervalRat.scale (479 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-22497496525 / 1000000000000) (-22497496524 / 1000000000000), orderedInterval (-30495563377 / 1000000000000) (-30495563376 / 1000000000000)))) (orderedInterval (2463547095 / 1000000000000) (2463547133 / 1000000000000))) = true
  rfl'

theorem compactCertificate368_chunkChecks0_2 :
    compactCertificate368.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (979878907171331 / 4000000000000) 0 (IntervalRat.scale (479 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (33244214885 / 1000000000000) (33244214886 / 1000000000000), orderedInterval (38579166508 / 1000000000000) (38579166509 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (830654201470891 / 4000000000000) 0 (IntervalRat.scale (479 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (49425320849 / 1000000000000) (49425320850 / 1000000000000), orderedInterval (24836220541 / 1000000000000) (24836220542 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (519784830769273 / 4000000000000) 0 (IntervalRat.scale (479 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-65639970826 / 1000000000000) (-65639967150 / 1000000000000), orderedInterval (24552134237 / 1000000000000) (24552137913 / 1000000000000)))) (orderedInterval (-10249896755 / 1000000000000) (-10249896574 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (279542010713991 / 4000000000000) 0 (IntervalRat.scale (479 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (95428969485 / 1000000000000) (95428969506 / 1000000000000), orderedInterval (913265369 / 1000000000000) (913265389 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (759010937754973 / 4000000000000) 0 (IntervalRat.scale (479 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (51612248243 / 1000000000000) (51612264556 / 1000000000000), orderedInterval (-26426016495 / 1000000000000) (-26426000181 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1036364545663421 / 4000000000000) 0 (IntervalRat.scale (479 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (38082742172 / 1000000000000) (38082822256 / 1000000000000), orderedInterval (-31804077534 / 1000000000000) (-31803997449 / 1000000000000)))) (orderedInterval (-5851651889 / 1000000000000) (-5851645352 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (438215169230727 / 4000000000000) 0 (IntervalRat.scale (479 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-28438365175 / 1000000000000) (-28438365174 / 1000000000000), orderedInterval (-70597345501 / 1000000000000) (-70597345500 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1781320333944167 / 4000000000000) 0 (IntervalRat.scale (479 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (341948522 / 1000000000000) (341948523 / 1000000000000), orderedInterval (37807417137 / 1000000000000) (37807417138 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1189839429451753 / 4000000000000) 0 (IntervalRat.scale (479 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (9483874932 / 1000000000000) (9483874966 / 1000000000000), orderedInterval (-45295584319 / 1000000000000) (-45295584285 / 1000000000000)))) (orderedInterval (-1978697566 / 1000000000000) (-1978697493 / 1000000000000))) = true
  rfl'

theorem compactCertificate368_chunkChecks0 :
    compactCertificate368.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate368.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate368_chunkChecks0_0
    compactCertificate368_chunkChecks0_1 compactCertificate368_chunkChecks0_2

theorem compactCertificate368_chunkChecks1_0 :
    compactCertificate368.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (479 / 2) 1 (IntervalRat.scale (479 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (51500062396 / 1000000000000) (51500062442 / 1000000000000), orderedInterval (2312802619 / 1000000000000) (2312802665 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (705658464044579 / 4000000000000) 1 (IntervalRat.scale (479 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (57376876792 / 1000000000000) (57376876793 / 1000000000000), orderedInterval (17628915890 / 1000000000000) (17628915891 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (228195448603907 / 800000000000) 1 (IntervalRat.scale (479 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-6795267333 / 1000000000000) (-6795267332 / 1000000000000), orderedInterval (-46739217203 / 1000000000000) (-46739217202 / 1000000000000)))) (orderedInterval (-2228853565 / 1000000000000) (-2228853527 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (205909379870953 / 4000000000000) 1 (IntervalRat.scale (479 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (101355590503 / 1000000000000) (101355595622 / 1000000000000), orderedInterval (-46740769169 / 1000000000000) (-46740764050 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (553101557883541 / 4000000000000) 1 (IntervalRat.scale (479 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (50061684893 / 1000000000000) (50061684894 / 1000000000000), orderedInterval (45620991159 / 1000000000000) (45620991160 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1501778323229697 / 4000000000000) 1 (IntervalRat.scale (479 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-28412442845 / 1000000000000) (-28412426106 / 1000000000000), orderedInterval (29843468201 / 1000000000000) (29843484940 / 1000000000000)))) (orderedInterval (-2255111577 / 1000000000000) (-2255109666 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1106203115767561 / 4000000000000) 1 (IntervalRat.scale (479 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (36843633668 / 1000000000000) (36843633669 / 1000000000000), orderedInterval (30666847159 / 1000000000000) (30666847160 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1895497893495853 / 4000000000000) 1 (IntervalRat.scale (479 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-10098128770 / 1000000000000) (-10098128769 / 1000000000000), orderedInterval (-35223758622 / 1000000000000) (-35223758621 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1396215169230727 / 4000000000000) 1 (IntervalRat.scale (479 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-38478132951 / 1000000000000) (-38478132950 / 1000000000000), orderedInterval (-18472602822 / 1000000000000) (-18472602821 / 1000000000000)))) (orderedInterval (1498969368 / 1000000000000) (1498969392 / 1000000000000))) = true
  rfl'

theorem compactCertificate368_chunkChecks1_1 :
    compactCertificate368.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2142153122444521 / 4000000000000) 1 (IntervalRat.scale (479 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (26768107218 / 1000000000000) (26768133122 / 1000000000000), orderedInterval (-21755514824 / 1000000000000) (-21755488920 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1236772681888609 / 4000000000000) 1 (IntervalRat.scale (479 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (39121006411 / 1000000000000) (39121055847 / 1000000000000), orderedInterval (-23052731254 / 1000000000000) (-23052681818 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2194674827298581 / 4000000000000) 1 (IntervalRat.scale (479 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (10871409904 / 1000000000000) (10871409934 / 1000000000000), orderedInterval (-32291664588 / 1000000000000) (-32291664558 / 1000000000000)))) (orderedInterval (-4077328416 / 1000000000000) (-4077313188 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2050549909393289 / 4000000000000) 1 (IntervalRat.scale (479 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-34329768111 / 1000000000000) (-34329768087 / 1000000000000), orderedInterval (-7923795540 / 1000000000000) (-7923795516 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1463369171922137 / 4000000000000) 1 (IntervalRat.scale (479 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (33662450721 / 1000000000000) (33662537041 / 1000000000000), orderedInterval (-24683094581 / 1000000000000) (-24683008261 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1659304673650623 / 4000000000000) 1 (IntervalRat.scale (479 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (31192083626 / 1000000000000) (31192083627 / 1000000000000), orderedInterval (23663036299 / 1000000000000) (23663036300 / 1000000000000)))) (orderedInterval (-3466624705 / 1000000000000) (-3466612188 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1383355245681487 / 4000000000000) 1 (IntervalRat.scale (479 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (37187650428 / 1000000000000) (37187650429 / 1000000000000), orderedInterval (21344291383 / 1000000000000) (21344291384 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1222236312515227 / 4000000000000) 1 (IntervalRat.scale (479 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-45610566939 / 1000000000000) (-45610566694 / 1000000000000), orderedInterval (1844460766 / 1000000000000) (1844461011 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (354251722315473 / 800000000000) 1 (IntervalRat.scale (479 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-22497496525 / 1000000000000) (-22497496524 / 1000000000000), orderedInterval (-30495563377 / 1000000000000) (-30495563376 / 1000000000000)))) (orderedInterval (-1222396504 / 1000000000000) (-1222396452 / 1000000000000))) = true
  rfl'

theorem compactCertificate368_chunkChecks1_2 :
    compactCertificate368.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (979878907171331 / 4000000000000) 1 (IntervalRat.scale (479 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (33244214885 / 1000000000000) (33244214886 / 1000000000000), orderedInterval (38579166508 / 1000000000000) (38579166509 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (830654201470891 / 4000000000000) 1 (IntervalRat.scale (479 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (49425320849 / 1000000000000) (49425320850 / 1000000000000), orderedInterval (24836220541 / 1000000000000) (24836220542 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (519784830769273 / 4000000000000) 1 (IntervalRat.scale (479 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-65639970826 / 1000000000000) (-65639967150 / 1000000000000), orderedInterval (24552134237 / 1000000000000) (24552137913 / 1000000000000)))) (orderedInterval (-7094582277 / 1000000000000) (-7094582156 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (279542010713991 / 4000000000000) 1 (IntervalRat.scale (479 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (95428969485 / 1000000000000) (95428969506 / 1000000000000), orderedInterval (913265369 / 1000000000000) (913265389 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (759010937754973 / 4000000000000) 1 (IntervalRat.scale (479 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (51612248243 / 1000000000000) (51612264556 / 1000000000000), orderedInterval (-26426016495 / 1000000000000) (-26426000181 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1036364545663421 / 4000000000000) 1 (IntervalRat.scale (479 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (38082742172 / 1000000000000) (38082822256 / 1000000000000), orderedInterval (-31804077534 / 1000000000000) (-31803997449 / 1000000000000)))) (orderedInterval (3106877485 / 1000000000000) (3106884444 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (438215169230727 / 4000000000000) 1 (IntervalRat.scale (479 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-28438365175 / 1000000000000) (-28438365174 / 1000000000000), orderedInterval (-70597345501 / 1000000000000) (-70597345500 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1781320333944167 / 4000000000000) 1 (IntervalRat.scale (479 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (341948522 / 1000000000000) (341948523 / 1000000000000), orderedInterval (37807417137 / 1000000000000) (37807417138 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1189839429451753 / 4000000000000) 1 (IntervalRat.scale (479 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (9483874932 / 1000000000000) (9483874966 / 1000000000000), orderedInterval (-45295584319 / 1000000000000) (-45295584285 / 1000000000000)))) (orderedInterval (4638162764 / 1000000000000) (4638162866 / 1000000000000))) = true
  rfl'

theorem compactCertificate368_chunkChecks1 :
    compactCertificate368.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate368.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate368_chunkChecks1_0
    compactCertificate368_chunkChecks1_1 compactCertificate368_chunkChecks1_2

theorem compactCertificate368_chunkChecks2_0 :
    compactCertificate368.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (479 / 2) 2 (IntervalRat.scale (479 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (51500062396 / 1000000000000) (51500062442 / 1000000000000), orderedInterval (2312802619 / 1000000000000) (2312802665 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (705658464044579 / 4000000000000) 2 (IntervalRat.scale (479 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (57376876792 / 1000000000000) (57376876793 / 1000000000000), orderedInterval (17628915890 / 1000000000000) (17628915891 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (228195448603907 / 800000000000) 2 (IntervalRat.scale (479 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-6795267333 / 1000000000000) (-6795267332 / 1000000000000), orderedInterval (-46739217203 / 1000000000000) (-46739217202 / 1000000000000)))) (orderedInterval (-20127973164 / 1000000000000) (-20127973124 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (205909379870953 / 4000000000000) 2 (IntervalRat.scale (479 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (101355590503 / 1000000000000) (101355595622 / 1000000000000), orderedInterval (-46740769169 / 1000000000000) (-46740764050 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (553101557883541 / 4000000000000) 2 (IntervalRat.scale (479 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (50061684893 / 1000000000000) (50061684894 / 1000000000000), orderedInterval (45620991159 / 1000000000000) (45620991160 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1501778323229697 / 4000000000000) 2 (IntervalRat.scale (479 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-28412442845 / 1000000000000) (-28412426106 / 1000000000000), orderedInterval (29843468201 / 1000000000000) (29843484940 / 1000000000000)))) (orderedInterval (-5512649070 / 1000000000000) (-5512646089 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1106203115767561 / 4000000000000) 2 (IntervalRat.scale (479 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (36843633668 / 1000000000000) (36843633669 / 1000000000000), orderedInterval (30666847159 / 1000000000000) (30666847160 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1895497893495853 / 4000000000000) 2 (IntervalRat.scale (479 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-10098128770 / 1000000000000) (-10098128769 / 1000000000000), orderedInterval (-35223758622 / 1000000000000) (-35223758621 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1396215169230727 / 4000000000000) 2 (IntervalRat.scale (479 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-38478132951 / 1000000000000) (-38478132950 / 1000000000000), orderedInterval (-18472602822 / 1000000000000) (-18472602821 / 1000000000000)))) (orderedInterval (749675480 / 1000000000000) (749675523 / 1000000000000))) = true
  rfl'

theorem compactCertificate368_chunkChecks2_1 :
    compactCertificate368.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2142153122444521 / 4000000000000) 2 (IntervalRat.scale (479 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (26768107218 / 1000000000000) (26768133122 / 1000000000000), orderedInterval (-21755514824 / 1000000000000) (-21755488920 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1236772681888609 / 4000000000000) 2 (IntervalRat.scale (479 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (39121006411 / 1000000000000) (39121055847 / 1000000000000), orderedInterval (-23052731254 / 1000000000000) (-23052681818 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2194674827298581 / 4000000000000) 2 (IntervalRat.scale (479 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (10871409904 / 1000000000000) (10871409934 / 1000000000000), orderedInterval (-32291664588 / 1000000000000) (-32291664558 / 1000000000000)))) (orderedInterval (10857224881 / 1000000000000) (10857254507 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2050549909393289 / 4000000000000) 2 (IntervalRat.scale (479 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-34329768111 / 1000000000000) (-34329768087 / 1000000000000), orderedInterval (-7923795540 / 1000000000000) (-7923795516 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1463369171922137 / 4000000000000) 2 (IntervalRat.scale (479 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (33662450721 / 1000000000000) (33662537041 / 1000000000000), orderedInterval (-24683094581 / 1000000000000) (-24683008261 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1659304673650623 / 4000000000000) 2 (IntervalRat.scale (479 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (31192083626 / 1000000000000) (31192083627 / 1000000000000), orderedInterval (23663036299 / 1000000000000) (23663036300 / 1000000000000)))) (orderedInterval (-9778938614 / 1000000000000) (-9778919437 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1383355245681487 / 4000000000000) 2 (IntervalRat.scale (479 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (37187650428 / 1000000000000) (37187650429 / 1000000000000), orderedInterval (21344291383 / 1000000000000) (21344291384 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1222236312515227 / 4000000000000) 2 (IntervalRat.scale (479 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-45610566939 / 1000000000000) (-45610566694 / 1000000000000), orderedInterval (1844460766 / 1000000000000) (1844461011 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (354251722315473 / 800000000000) 2 (IntervalRat.scale (479 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-22497496525 / 1000000000000) (-22497496524 / 1000000000000), orderedInterval (-30495563377 / 1000000000000) (-30495563376 / 1000000000000)))) (orderedInterval (-3169768601 / 1000000000000) (-3169768528 / 1000000000000))) = true
  rfl'

theorem compactCertificate368_chunkChecks2_2 :
    compactCertificate368.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (979878907171331 / 4000000000000) 2 (IntervalRat.scale (479 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (33244214885 / 1000000000000) (33244214886 / 1000000000000), orderedInterval (38579166508 / 1000000000000) (38579166509 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (830654201470891 / 4000000000000) 2 (IntervalRat.scale (479 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (49425320849 / 1000000000000) (49425320850 / 1000000000000), orderedInterval (24836220541 / 1000000000000) (24836220542 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (519784830769273 / 4000000000000) 2 (IntervalRat.scale (479 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-65639970826 / 1000000000000) (-65639967150 / 1000000000000), orderedInterval (24552134237 / 1000000000000) (24552137913 / 1000000000000)))) (orderedInterval (8322938946 / 1000000000000) (8322939036 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (279542010713991 / 4000000000000) 2 (IntervalRat.scale (479 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (95428969485 / 1000000000000) (95428969506 / 1000000000000), orderedInterval (913265369 / 1000000000000) (913265389 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (759010937754973 / 4000000000000) 2 (IntervalRat.scale (479 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (51612248243 / 1000000000000) (51612264556 / 1000000000000), orderedInterval (-26426016495 / 1000000000000) (-26426000181 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1036364545663421 / 4000000000000) 2 (IntervalRat.scale (479 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (38082742172 / 1000000000000) (38082822256 / 1000000000000), orderedInterval (-31804077534 / 1000000000000) (-31803997449 / 1000000000000)))) (orderedInterval (4287706344 / 1000000000000) (4287713814 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (438215169230727 / 4000000000000) 2 (IntervalRat.scale (479 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-28438365175 / 1000000000000) (-28438365174 / 1000000000000), orderedInterval (-70597345501 / 1000000000000) (-70597345500 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1781320333944167 / 4000000000000) 2 (IntervalRat.scale (479 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (341948522 / 1000000000000) (341948523 / 1000000000000), orderedInterval (37807417137 / 1000000000000) (37807417138 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1189839429451753 / 4000000000000) 2 (IntervalRat.scale (479 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (9483874932 / 1000000000000) (9483874966 / 1000000000000), orderedInterval (-45295584319 / 1000000000000) (-45295584285 / 1000000000000)))) (orderedInterval (2857638399 / 1000000000000) (2857638547 / 1000000000000))) = true
  rfl'

theorem compactCertificate368_chunkChecks2 :
    compactCertificate368.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate368.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate368_chunkChecks2_0
    compactCertificate368_chunkChecks2_1 compactCertificate368_chunkChecks2_2

theorem compactCertificate368_chunkChecks3_0 :
    compactCertificate368.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (479 / 2) 3 (IntervalRat.scale (479 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (51500062396 / 1000000000000) (51500062442 / 1000000000000), orderedInterval (2312802619 / 1000000000000) (2312802665 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (705658464044579 / 4000000000000) 3 (IntervalRat.scale (479 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (57376876792 / 1000000000000) (57376876793 / 1000000000000), orderedInterval (17628915890 / 1000000000000) (17628915891 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (228195448603907 / 800000000000) 3 (IntervalRat.scale (479 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-6795267333 / 1000000000000) (-6795267332 / 1000000000000), orderedInterval (-46739217203 / 1000000000000) (-46739217202 / 1000000000000)))) (orderedInterval (3735194022 / 1000000000000) (3735194066 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (205909379870953 / 4000000000000) 3 (IntervalRat.scale (479 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (101355590503 / 1000000000000) (101355595622 / 1000000000000), orderedInterval (-46740769169 / 1000000000000) (-46740764050 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (553101557883541 / 4000000000000) 3 (IntervalRat.scale (479 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (50061684893 / 1000000000000) (50061684894 / 1000000000000), orderedInterval (45620991159 / 1000000000000) (45620991160 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1501778323229697 / 4000000000000) 3 (IntervalRat.scale (479 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-28412442845 / 1000000000000) (-28412426106 / 1000000000000), orderedInterval (29843468201 / 1000000000000) (29843484940 / 1000000000000)))) (orderedInterval (7870285552 / 1000000000000) (7870290217 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1106203115767561 / 4000000000000) 3 (IntervalRat.scale (479 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (36843633668 / 1000000000000) (36843633669 / 1000000000000), orderedInterval (30666847159 / 1000000000000) (30666847160 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1895497893495853 / 4000000000000) 3 (IntervalRat.scale (479 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-10098128770 / 1000000000000) (-10098128769 / 1000000000000), orderedInterval (-35223758622 / 1000000000000) (-35223758621 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1396215169230727 / 4000000000000) 3 (IntervalRat.scale (479 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-38478132951 / 1000000000000) (-38478132950 / 1000000000000), orderedInterval (-18472602822 / 1000000000000) (-18472602821 / 1000000000000)))) (orderedInterval (-7036532292 / 1000000000000) (-7036532215 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate368_chunkChecks3_1 :
    compactCertificate368.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2142153122444521 / 4000000000000) 3 (IntervalRat.scale (479 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (26768107218 / 1000000000000) (26768133122 / 1000000000000), orderedInterval (-21755514824 / 1000000000000) (-21755488920 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1236772681888609 / 4000000000000) 3 (IntervalRat.scale (479 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (39121006411 / 1000000000000) (39121055847 / 1000000000000), orderedInterval (-23052731254 / 1000000000000) (-23052681818 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2194674827298581 / 4000000000000) 3 (IntervalRat.scale (479 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (10871409904 / 1000000000000) (10871409934 / 1000000000000), orderedInterval (-32291664588 / 1000000000000) (-32291664558 / 1000000000000)))) (orderedInterval (15601036527 / 1000000000000) (15601096966 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2050549909393289 / 4000000000000) 3 (IntervalRat.scale (479 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-34329768111 / 1000000000000) (-34329768087 / 1000000000000), orderedInterval (-7923795540 / 1000000000000) (-7923795516 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1463369171922137 / 4000000000000) 3 (IntervalRat.scale (479 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (33662450721 / 1000000000000) (33662537041 / 1000000000000), orderedInterval (-24683094581 / 1000000000000) (-24683008261 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1659304673650623 / 4000000000000) 3 (IntervalRat.scale (479 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (31192083626 / 1000000000000) (31192083627 / 1000000000000), orderedInterval (23663036299 / 1000000000000) (23663036300 / 1000000000000)))) (orderedInterval (7579435415 / 1000000000000) (7579464723 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1383355245681487 / 4000000000000) 3 (IntervalRat.scale (479 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (37187650428 / 1000000000000) (37187650429 / 1000000000000), orderedInterval (21344291383 / 1000000000000) (21344291384 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1222236312515227 / 4000000000000) 3 (IntervalRat.scale (479 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-45610566939 / 1000000000000) (-45610566694 / 1000000000000), orderedInterval (1844460766 / 1000000000000) (1844461011 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (354251722315473 / 800000000000) 3 (IntervalRat.scale (479 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-22497496525 / 1000000000000) (-22497496524 / 1000000000000), orderedInterval (-30495563377 / 1000000000000) (-30495563376 / 1000000000000)))) (orderedInterval (4425347215 / 1000000000000) (4425347321 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate368_chunkChecks3_2 :
    compactCertificate368.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (979878907171331 / 4000000000000) 3 (IntervalRat.scale (479 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (33244214885 / 1000000000000) (33244214886 / 1000000000000), orderedInterval (38579166508 / 1000000000000) (38579166509 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (830654201470891 / 4000000000000) 3 (IntervalRat.scale (479 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (49425320849 / 1000000000000) (49425320850 / 1000000000000), orderedInterval (24836220541 / 1000000000000) (24836220542 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (519784830769273 / 4000000000000) 3 (IntervalRat.scale (479 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-65639970826 / 1000000000000) (-65639967150 / 1000000000000), orderedInterval (24552134237 / 1000000000000) (24552137913 / 1000000000000)))) (orderedInterval (7354690118 / 1000000000000) (7354690190 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (279542010713991 / 4000000000000) 3 (IntervalRat.scale (479 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (95428969485 / 1000000000000) (95428969506 / 1000000000000), orderedInterval (913265369 / 1000000000000) (913265389 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (759010937754973 / 4000000000000) 3 (IntervalRat.scale (479 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (51612248243 / 1000000000000) (51612264556 / 1000000000000), orderedInterval (-26426016495 / 1000000000000) (-26426000181 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1036364545663421 / 4000000000000) 3 (IntervalRat.scale (479 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (38082742172 / 1000000000000) (38082822256 / 1000000000000), orderedInterval (-31804077534 / 1000000000000) (-31803997449 / 1000000000000)))) (orderedInterval (-3401429814 / 1000000000000) (-3401421802 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (438215169230727 / 4000000000000) 3 (IntervalRat.scale (479 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-28438365175 / 1000000000000) (-28438365174 / 1000000000000), orderedInterval (-70597345501 / 1000000000000) (-70597345500 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1781320333944167 / 4000000000000) 3 (IntervalRat.scale (479 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (341948522 / 1000000000000) (341948523 / 1000000000000), orderedInterval (37807417137 / 1000000000000) (37807417138 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1189839429451753 / 4000000000000) 3 (IntervalRat.scale (479 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (9483874932 / 1000000000000) (9483874966 / 1000000000000), orderedInterval (-45295584319 / 1000000000000) (-45295584285 / 1000000000000)))) (orderedInterval (3531673846 / 1000000000000) (3531674072 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate368_chunkChecks3 :
    compactCertificate368.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate368.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate368_chunkChecks3_0
    compactCertificate368_chunkChecks3_1 compactCertificate368_chunkChecks3_2

theorem compactCertificate368_chunkChecks4_0 :
    compactCertificate368.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (479 / 2) 4 (IntervalRat.scale (479 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (51500062396 / 1000000000000) (51500062442 / 1000000000000), orderedInterval (2312802619 / 1000000000000) (2312802665 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (705658464044579 / 4000000000000) 4 (IntervalRat.scale (479 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (57376876792 / 1000000000000) (57376876793 / 1000000000000), orderedInterval (17628915890 / 1000000000000) (17628915891 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (228195448603907 / 800000000000) 4 (IntervalRat.scale (479 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-6795267333 / 1000000000000) (-6795267332 / 1000000000000), orderedInterval (-46739217203 / 1000000000000) (-46739217202 / 1000000000000)))) (orderedInterval (19736343826 / 1000000000000) (19736343875 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (205909379870953 / 4000000000000) 4 (IntervalRat.scale (479 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (101355590503 / 1000000000000) (101355595622 / 1000000000000), orderedInterval (-46740769169 / 1000000000000) (-46740764050 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (553101557883541 / 4000000000000) 4 (IntervalRat.scale (479 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (50061684893 / 1000000000000) (50061684894 / 1000000000000), orderedInterval (45620991159 / 1000000000000) (45620991160 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1501778323229697 / 4000000000000) 4 (IntervalRat.scale (479 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-28412442845 / 1000000000000) (-28412426106 / 1000000000000), orderedInterval (29843468201 / 1000000000000) (29843484940 / 1000000000000)))) (orderedInterval (12332571046 / 1000000000000) (12332578375 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1106203115767561 / 4000000000000) 4 (IntervalRat.scale (479 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (36843633668 / 1000000000000) (36843633669 / 1000000000000), orderedInterval (30666847159 / 1000000000000) (30666847160 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1895497893495853 / 4000000000000) 4 (IntervalRat.scale (479 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-10098128770 / 1000000000000) (-10098128769 / 1000000000000), orderedInterval (-35223758622 / 1000000000000) (-35223758621 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1396215169230727 / 4000000000000) 4 (IntervalRat.scale (479 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-38478132951 / 1000000000000) (-38478132950 / 1000000000000), orderedInterval (-18472602822 / 1000000000000) (-18472602821 / 1000000000000)))) (orderedInterval (636655683 / 1000000000000) (636655824 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate368_chunkChecks4_1 :
    compactCertificate368.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2142153122444521 / 4000000000000) 4 (IntervalRat.scale (479 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (26768107218 / 1000000000000) (26768133122 / 1000000000000), orderedInterval (-21755514824 / 1000000000000) (-21755488920 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1236772681888609 / 4000000000000) 4 (IntervalRat.scale (479 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (39121006411 / 1000000000000) (39121055847 / 1000000000000), orderedInterval (-23052731254 / 1000000000000) (-23052681818 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2194674827298581 / 4000000000000) 4 (IntervalRat.scale (479 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (10871409904 / 1000000000000) (10871409934 / 1000000000000), orderedInterval (-32291664588 / 1000000000000) (-32291664558 / 1000000000000)))) (orderedInterval (-68421284792 / 1000000000000) (-68421156883 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2050549909393289 / 4000000000000) 4 (IntervalRat.scale (479 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-34329768111 / 1000000000000) (-34329768087 / 1000000000000), orderedInterval (-7923795540 / 1000000000000) (-7923795516 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1463369171922137 / 4000000000000) 4 (IntervalRat.scale (479 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (33662450721 / 1000000000000) (33662537041 / 1000000000000), orderedInterval (-24683094581 / 1000000000000) (-24683008261 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1659304673650623 / 4000000000000) 4 (IntervalRat.scale (479 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (31192083626 / 1000000000000) (31192083627 / 1000000000000), orderedInterval (23663036299 / 1000000000000) (23663036300 / 1000000000000)))) (orderedInterval (28855671492 / 1000000000000) (28855716411 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1383355245681487 / 4000000000000) 4 (IntervalRat.scale (479 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (37187650428 / 1000000000000) (37187650429 / 1000000000000), orderedInterval (21344291383 / 1000000000000) (21344291384 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1222236312515227 / 4000000000000) 4 (IntervalRat.scale (479 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-45610566939 / 1000000000000) (-45610566694 / 1000000000000), orderedInterval (1844460766 / 1000000000000) (1844461011 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (354251722315473 / 800000000000) 4 (IntervalRat.scale (479 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-22497496525 / 1000000000000) (-22497496524 / 1000000000000), orderedInterval (-30495563377 / 1000000000000) (-30495563376 / 1000000000000)))) (orderedInterval (2014143397 / 1000000000000) (2014143556 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate368_chunkChecks4_2 :
    compactCertificate368.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (979878907171331 / 4000000000000) 4 (IntervalRat.scale (479 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (33244214885 / 1000000000000) (33244214886 / 1000000000000), orderedInterval (38579166508 / 1000000000000) (38579166509 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (830654201470891 / 4000000000000) 4 (IntervalRat.scale (479 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (49425320849 / 1000000000000) (49425320850 / 1000000000000), orderedInterval (24836220541 / 1000000000000) (24836220542 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (519784830769273 / 4000000000000) 4 (IntervalRat.scale (479 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-65639970826 / 1000000000000) (-65639967150 / 1000000000000), orderedInterval (24552134237 / 1000000000000) (24552137913 / 1000000000000)))) (orderedInterval (-7645627281 / 1000000000000) (-7645627219 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (279542010713991 / 4000000000000) 4 (IntervalRat.scale (479 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (95428969485 / 1000000000000) (95428969506 / 1000000000000), orderedInterval (913265369 / 1000000000000) (913265389 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (759010937754973 / 4000000000000) 4 (IntervalRat.scale (479 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (51612248243 / 1000000000000) (51612264556 / 1000000000000), orderedInterval (-26426016495 / 1000000000000) (-26426000181 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1036364545663421 / 4000000000000) 4 (IntervalRat.scale (479 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (38082742172 / 1000000000000) (38082822256 / 1000000000000), orderedInterval (-31804077534 / 1000000000000) (-31803997449 / 1000000000000)))) (orderedInterval (-4442971233 / 1000000000000) (-4442962587 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (438215169230727 / 4000000000000) 4 (IntervalRat.scale (479 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-28438365175 / 1000000000000) (-28438365174 / 1000000000000), orderedInterval (-70597345501 / 1000000000000) (-70597345500 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1781320333944167 / 4000000000000) 4 (IntervalRat.scale (479 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (341948522 / 1000000000000) (341948523 / 1000000000000), orderedInterval (37807417137 / 1000000000000) (37807417138 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1189839429451753 / 4000000000000) 4 (IntervalRat.scale (479 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (9483874932 / 1000000000000) (9483874966 / 1000000000000), orderedInterval (-45295584319 / 1000000000000) (-45295584285 / 1000000000000)))) (orderedInterval (-4603885894 / 1000000000000) (-4603885537 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate368_chunkChecks4 :
    compactCertificate368.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate368.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate368_chunkChecks4_0
    compactCertificate368_chunkChecks4_1 compactCertificate368_chunkChecks4_2

theorem compactCertificate368_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate368.chunkCheck r b = true :=
  compactCertificate368.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate368_chunkChecks0
    · exact compactCertificate368_chunkChecks1
    · exact compactCertificate368_chunkChecks2
    · exact compactCertificate368_chunkChecks3
    · exact compactCertificate368_chunkChecks4)

theorem compactCertificate368_coefficient0 :
    compactCertificate368.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate368_coefficient1 :
    compactCertificate368.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate368_coefficient2 :
    compactCertificate368.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate368_coefficient3 :
    compactCertificate368.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate368_coefficient4 :
    compactCertificate368.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate368_coefficients : ∀ r : Fin 5,
    compactCertificate368.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate368_coefficient0
  · exact compactCertificate368_coefficient1
  · exact compactCertificate368_coefficient2
  · exact compactCertificate368_coefficient3
  · exact compactCertificate368_coefficient4

theorem compactCertificate368_lower : (1 : ℚ) ≤ compactCertificate368.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate368, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate368_proves {t : ℝ} (ht : t ∈ compactCertificate368.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate368.proves compactCertificate368_states compactCertificate368_chunks
    compactCertificate368_coefficients compactCertificate368_lower ht

end Erdos232
