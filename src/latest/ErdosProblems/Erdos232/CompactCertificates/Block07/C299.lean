/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate299 : CompactCertificate where
  left := 172
  right := 173
  center := 345 / 2
  grid := fun i =>
    match i.val with
    | 0 => 55
    | 1 => 40
    | 2 => 65
    | 3 => 12
    | 4 => 32
    | 5 => 86
    | 6 => 63
    | 7 => 109
    | 8 => 80
    | 9 => 123
    | 10 => 71
    | 11 => 126
    | 12 => 118
    | 13 => 84
    | 14 => 95
    | 15 => 79
    | 16 => 70
    | 17 => 102
    | 18 => 56
    | 19 => 48
    | 20 => 30
    | 21 => 16
    | 22 => 44
    | 23 => 59
    | 24 => 25
    | 25 => 102
    | _ => 68
  point := fun i =>
    match i.val with
    | 0 => 345 / 2
    | 1 => 101650175405169 / 800000000000
    | 2 => 32871578191377 / 160000000000
    | 3 => 29661267664083 / 800000000000
    | 4 => 79674337148151 / 800000000000
    | 5 => 216331324223067 / 800000000000
    | 6 => 159348674296371 / 800000000000
    | 7 => 273046669417983 / 800000000000
    | 8 => 201124940870397 / 800000000000
    | 9 => 308577380894931 / 800000000000
    | 10 => 178157233925499 / 800000000000
    | 11 => 316143137961591 / 800000000000
    | 12 => 295381928492979 / 800000000000
    | 13 => 210798481967907 / 800000000000
    | 14 => 239023011444453 / 800000000000
    | 15 => 199272467540757 / 800000000000
    | 16 => 176063268399897 / 800000000000
    | 17 => 51029997577803 / 160000000000
    | 18 => 141151658861841 / 800000000000
    | 19 => 119655824429001 / 800000000000
    | 20 => 74875059129603 / 800000000000
    | 21 => 40268055823101 / 800000000000
    | 22 => 109335604812303 / 800000000000
    | 23 => 149288420982831 / 800000000000
    | 24 => 63124940870397 / 800000000000
    | 25 => 256599380046237 / 800000000000
    | _ => 171396494012883 / 800000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-28969062279 / 1000000000000) (-28969062278 / 1000000000000), orderedInterval (-53314078140 / 1000000000000) (-53314078139 / 1000000000000))
    | 1 => (orderedInterval (57910273158 / 1000000000000) (57910318224 / 1000000000000), orderedInterval (-40930038184 / 1000000000000) (-40929993118 / 1000000000000))
    | 2 => (orderedInterval (-49932959673 / 1000000000000) (-49932944182 / 1000000000000), orderedInterval (24726286023 / 1000000000000) (24726301514 / 1000000000000))
    | 3 => (orderedInterval (20810871472 / 1000000000000) (20810871474 / 1000000000000), orderedInterval (129097872210 / 1000000000000) (129097872211 / 1000000000000))
    | 4 => (orderedInterval (-12255949676 / 1000000000000) (-12255949608 / 1000000000000), orderedInterval (79068411470 / 1000000000000) (79068411539 / 1000000000000))
    | 5 => (orderedInterval (41398497578 / 1000000000000) (41398497579 / 1000000000000), orderedInterval (25229626631 / 1000000000000) (25229626632 / 1000000000000))
    | 6 => (orderedInterval (-50158998254 / 1000000000000) (-50158979762 / 1000000000000), orderedInterval (26206151542 / 1000000000000) (26206170034 / 1000000000000))
    | 7 => (orderedInterval (14412135819 / 1000000000000) (14412135989 / 1000000000000), orderedInterval (-40733831991 / 1000000000000) (-40733831822 / 1000000000000))
    | 8 => (orderedInterval (38255669484 / 1000000000000) (38255669485 / 1000000000000), orderedInterval (32615490473 / 1000000000000) (32615490474 / 1000000000000))
    | 9 => (orderedInterval (-3687964085 / 1000000000000) (-3687964084 / 1000000000000), orderedInterval (-40453397239 / 1000000000000) (-40453397238 / 1000000000000))
    | 10 => (orderedInterval (-22206066443 / 1000000000000) (-22206066442 / 1000000000000), orderedInterval (-48587398384 / 1000000000000) (-48587398383 / 1000000000000))
    | 11 => (orderedInterval (4937533411 / 1000000000000) (4937533412 / 1000000000000), orderedInterval (39825749032 / 1000000000000) (39825749033 / 1000000000000))
    | 12 => (orderedInterval (-26605744034 / 1000000000000) (-26605735002 / 1000000000000), orderedInterval (31915941648 / 1000000000000) (31915950680 / 1000000000000))
    | 13 => (orderedInterval (18653034873 / 1000000000000) (18653034874 / 1000000000000), orderedInterval (45440962732 / 1000000000000) (45440962733 / 1000000000000))
    | 14 => (orderedInterval (-41395365308 / 1000000000000) (-41395365307 / 1000000000000), orderedInterval (-20355260385 / 1000000000000) (-20355260384 / 1000000000000))
    | 15 => (orderedInterval (-50197915025 / 1000000000000) (-50197914549 / 1000000000000), orderedInterval (6095800175 / 1000000000000) (6095800651 / 1000000000000))
    | 16 => (orderedInterval (43824330486 / 1000000000000) (43824330487 / 1000000000000), orderedInterval (31079146017 / 1000000000000) (31079146018 / 1000000000000))
    | 17 => (orderedInterval (-29458182054 / 1000000000000) (-29458167272 / 1000000000000), orderedInterval (33636063760 / 1000000000000) (33636078542 / 1000000000000))
    | 18 => (orderedInterval (57798907149 / 1000000000000) (57798907151 / 1000000000000), orderedInterval (16189195437 / 1000000000000) (16189195438 / 1000000000000))
    | 19 => (orderedInterval (-27912634095 / 1000000000000) (-27912632113 / 1000000000000), orderedInterval (59061430703 / 1000000000000) (59061432685 / 1000000000000))
    | 20 => (orderedInterval (10700104630 / 1000000000000) (10700104632 / 1000000000000), orderedInterval (81720242240 / 1000000000000) (81720242241 / 1000000000000))
    | 21 => (orderedInterval (84673687649 / 1000000000000) (84673687650 / 1000000000000), orderedInterval (73171966638 / 1000000000000) (73171966639 / 1000000000000))
    | 22 => (orderedInterval (-47808646119 / 1000000000000) (-47808588569 / 1000000000000), orderedInterval (48882503663 / 1000000000000) (48882561213 / 1000000000000))
    | 23 => (orderedInterval (-52061581713 / 1000000000000) (-52061565743 / 1000000000000), orderedInterval (26617292380 / 1000000000000) (26617308350 / 1000000000000))
    | 24 => (orderedInterval (-81992186306 / 1000000000000) (-81992186305 / 1000000000000), orderedInterval (-36157891787 / 1000000000000) (-36157891786 / 1000000000000))
    | 25 => (orderedInterval (39536744416 / 1000000000000) (39536744417 / 1000000000000), orderedInterval (20472101465 / 1000000000000) (20472101466 / 1000000000000))
    | _ => (orderedInterval (53737398700 / 1000000000000) (53737398705 / 1000000000000), orderedInterval (9025143393 / 1000000000000) (9025143399 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-13872833771 / 1000000000000) (-13872832429 / 1000000000000)
      | 1 => orderedInterval (-3616273664 / 1000000000000) (-3616273640 / 1000000000000)
      | 2 => orderedInterval (480036111 / 1000000000000) (480036127 / 1000000000000)
      | 3 => orderedInterval (-288080669 / 1000000000000) (-288080599 / 1000000000000)
      | 4 => orderedInterval (2453684441 / 1000000000000) (2453684625 / 1000000000000)
      | 5 => orderedInterval (-3841835592 / 1000000000000) (-3841835191 / 1000000000000)
      | 6 => orderedInterval (-7313409876 / 1000000000000) (-7313409719 / 1000000000000)
      | 7 => orderedInterval (3511056860 / 1000000000000) (3511059411 / 1000000000000)
      | _ => orderedInterval (-13795198558 / 1000000000000) (-13795198509 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-19684663161 / 1000000000000) (-19684661754 / 1000000000000)
      | 1 => orderedInterval (-1445902861 / 1000000000000) (-1445902835 / 1000000000000)
      | 2 => orderedInterval (3634720574 / 1000000000000) (3634720602 / 1000000000000)
      | 3 => orderedInterval (24395357335 / 1000000000000) (24395357478 / 1000000000000)
      | 4 => orderedInterval (5508948817 / 1000000000000) (5508949200 / 1000000000000)
      | 5 => orderedInterval (-575158746 / 1000000000000) (-575158014 / 1000000000000)
      | 6 => orderedInterval (-4102683021 / 1000000000000) (-4102682882 / 1000000000000)
      | 7 => orderedInterval (-3479682168 / 1000000000000) (-3479679791 / 1000000000000)
      | _ => orderedInterval (-5301512930 / 1000000000000) (-5301512860 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (15459974389 / 1000000000000) (15459975931 / 1000000000000)
      | 1 => orderedInterval (7400193375 / 1000000000000) (7400193409 / 1000000000000)
      | 2 => orderedInterval (-244669561 / 1000000000000) (-244669510 / 1000000000000)
      | 3 => orderedInterval (-4359511352 / 1000000000000) (-4359511046 / 1000000000000)
      | 4 => orderedInterval (-6976696295 / 1000000000000) (-6976695490 / 1000000000000)
      | 5 => orderedInterval (7872590330 / 1000000000000) (7872591676 / 1000000000000)
      | 6 => orderedInterval (8402032576 / 1000000000000) (8402032700 / 1000000000000)
      | 7 => orderedInterval (-5196937128 / 1000000000000) (-5196934843 / 1000000000000)
      | _ => orderedInterval (26814490879 / 1000000000000) (26814490981 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (18742698464 / 1000000000000) (18742700196 / 1000000000000)
      | 1 => orderedInterval (6324734810 / 1000000000000) (6324734860 / 1000000000000)
      | 2 => orderedInterval (-12170599488 / 1000000000000) (-12170599392 / 1000000000000)
      | 3 => orderedInterval (-140661256074 / 1000000000000) (-140661255403 / 1000000000000)
      | 4 => orderedInterval (-10159870835 / 1000000000000) (-10159869137 / 1000000000000)
      | 5 => orderedInterval (-2007411518 / 1000000000000) (-2007409046 / 1000000000000)
      | 6 => orderedInterval (4475315533 / 1000000000000) (4475315645 / 1000000000000)
      | 7 => orderedInterval (3197699236 / 1000000000000) (3197701467 / 1000000000000)
      | _ => orderedInterval (13822871156 / 1000000000000) (13822871312 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-17435902464 / 1000000000000) (-17435900470 / 1000000000000)
      | 1 => orderedInterval (-17895933964 / 1000000000000) (-17895933888 / 1000000000000)
      | 2 => orderedInterval (-2500348482 / 1000000000000) (-2500348300 / 1000000000000)
      | 3 => orderedInterval (32775877970 / 1000000000000) (32775879457 / 1000000000000)
      | 4 => orderedInterval (21688275461 / 1000000000000) (21688279065 / 1000000000000)
      | 5 => orderedInterval (-17955537255 / 1000000000000) (-17955532693 / 1000000000000)
      | 6 => orderedInterval (-9243664065 / 1000000000000) (-9243663963 / 1000000000000)
      | 7 => orderedInterval (5843343234 / 1000000000000) (5843345470 / 1000000000000)
      | _ => orderedInterval (-62644425858 / 1000000000000) (-62644425609 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-36282854718 / 1000000000000) (-36282849924 / 1000000000000)
    | 1 => orderedInterval (-1050576161 / 1000000000000) (-1050570856 / 1000000000000)
    | 2 => orderedInterval (49171467213 / 1000000000000) (49171473808 / 1000000000000)
    | 3 => orderedInterval (-118435818716 / 1000000000000) (-118435809498 / 1000000000000)
    | _ => orderedInterval (-67368315423 / 1000000000000) (-67368300931 / 1000000000000)

theorem compactCertificate299_stateChecks0 :
    compactCertificate299.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (345 / 2)) (orderedInterval (-28969062279 / 1000000000000) (-28969062278 / 1000000000000), orderedInterval (-53314078140 / 1000000000000) (-53314078139 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 40 12 (101650175405169 / 800000000000)) (orderedInterval (57910273158 / 1000000000000) (57910318224 / 1000000000000), orderedInterval (-40930038184 / 1000000000000) (-40929993118 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 65 12 (32871578191377 / 160000000000)) (orderedInterval (-49932959673 / 1000000000000) (-49932944182 / 1000000000000), orderedInterval (24726286023 / 1000000000000) (24726301514 / 1000000000000))) = true
  rfl'

theorem compactCertificate299_stateChecks1 :
    compactCertificate299.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 12 12 (29661267664083 / 800000000000)) (orderedInterval (20810871472 / 1000000000000) (20810871474 / 1000000000000), orderedInterval (129097872210 / 1000000000000) (129097872211 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (79674337148151 / 800000000000)) (orderedInterval (-12255949676 / 1000000000000) (-12255949608 / 1000000000000), orderedInterval (79068411470 / 1000000000000) (79068411539 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 86 12 (216331324223067 / 800000000000)) (orderedInterval (41398497578 / 1000000000000) (41398497579 / 1000000000000), orderedInterval (25229626631 / 1000000000000) (25229626632 / 1000000000000))) = true
  rfl'

theorem compactCertificate299_stateChecks2 :
    compactCertificate299.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (159348674296371 / 800000000000)) (orderedInterval (-50158998254 / 1000000000000) (-50158979762 / 1000000000000), orderedInterval (26206151542 / 1000000000000) (26206170034 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 109 12 (273046669417983 / 800000000000)) (orderedInterval (14412135819 / 1000000000000) (14412135989 / 1000000000000), orderedInterval (-40733831991 / 1000000000000) (-40733831822 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 80 12 (201124940870397 / 800000000000)) (orderedInterval (38255669484 / 1000000000000) (38255669485 / 1000000000000), orderedInterval (32615490473 / 1000000000000) (32615490474 / 1000000000000))) = true
  rfl'

theorem compactCertificate299_stateChecks3 :
    compactCertificate299.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 123 12 (308577380894931 / 800000000000)) (orderedInterval (-3687964085 / 1000000000000) (-3687964084 / 1000000000000), orderedInterval (-40453397239 / 1000000000000) (-40453397238 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (178157233925499 / 800000000000)) (orderedInterval (-22206066443 / 1000000000000) (-22206066442 / 1000000000000), orderedInterval (-48587398384 / 1000000000000) (-48587398383 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 126 12 (316143137961591 / 800000000000)) (orderedInterval (4937533411 / 1000000000000) (4937533412 / 1000000000000), orderedInterval (39825749032 / 1000000000000) (39825749033 / 1000000000000))) = true
  rfl'

theorem compactCertificate299_stateChecks4 :
    compactCertificate299.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 118 12 (295381928492979 / 800000000000)) (orderedInterval (-26605744034 / 1000000000000) (-26605735002 / 1000000000000), orderedInterval (31915941648 / 1000000000000) (31915950680 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 84 12 (210798481967907 / 800000000000)) (orderedInterval (18653034873 / 1000000000000) (18653034874 / 1000000000000), orderedInterval (45440962732 / 1000000000000) (45440962733 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 95 12 (239023011444453 / 800000000000)) (orderedInterval (-41395365308 / 1000000000000) (-41395365307 / 1000000000000), orderedInterval (-20355260385 / 1000000000000) (-20355260384 / 1000000000000))) = true
  rfl'

theorem compactCertificate299_stateChecks5 :
    compactCertificate299.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 79 12 (199272467540757 / 800000000000)) (orderedInterval (-50197915025 / 1000000000000) (-50197914549 / 1000000000000), orderedInterval (6095800175 / 1000000000000) (6095800651 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (176063268399897 / 800000000000)) (orderedInterval (43824330486 / 1000000000000) (43824330487 / 1000000000000), orderedInterval (31079146017 / 1000000000000) (31079146018 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 102 12 (51029997577803 / 160000000000)) (orderedInterval (-29458182054 / 1000000000000) (-29458167272 / 1000000000000), orderedInterval (33636063760 / 1000000000000) (33636078542 / 1000000000000))) = true
  rfl'

theorem compactCertificate299_stateChecks6 :
    compactCertificate299.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 56 12 (141151658861841 / 800000000000)) (orderedInterval (57798907149 / 1000000000000) (57798907151 / 1000000000000), orderedInterval (16189195437 / 1000000000000) (16189195438 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 48 12 (119655824429001 / 800000000000)) (orderedInterval (-27912634095 / 1000000000000) (-27912632113 / 1000000000000), orderedInterval (59061430703 / 1000000000000) (59061432685 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (74875059129603 / 800000000000)) (orderedInterval (10700104630 / 1000000000000) (10700104632 / 1000000000000), orderedInterval (81720242240 / 1000000000000) (81720242241 / 1000000000000))) = true
  rfl'

theorem compactCertificate299_stateChecks7 :
    compactCertificate299.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 16 12 (40268055823101 / 800000000000)) (orderedInterval (84673687649 / 1000000000000) (84673687650 / 1000000000000), orderedInterval (73171966638 / 1000000000000) (73171966639 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 44 12 (109335604812303 / 800000000000)) (orderedInterval (-47808646119 / 1000000000000) (-47808588569 / 1000000000000), orderedInterval (48882503663 / 1000000000000) (48882561213 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 59 12 (149288420982831 / 800000000000)) (orderedInterval (-52061581713 / 1000000000000) (-52061565743 / 1000000000000), orderedInterval (26617292380 / 1000000000000) (26617308350 / 1000000000000))) = true
  rfl'

theorem compactCertificate299_stateChecks8 :
    compactCertificate299.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 25 12 (63124940870397 / 800000000000)) (orderedInterval (-81992186306 / 1000000000000) (-81992186305 / 1000000000000), orderedInterval (-36157891787 / 1000000000000) (-36157891786 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 102 12 (256599380046237 / 800000000000)) (orderedInterval (39536744416 / 1000000000000) (39536744417 / 1000000000000), orderedInterval (20472101465 / 1000000000000) (20472101466 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (171396494012883 / 800000000000)) (orderedInterval (53737398700 / 1000000000000) (53737398705 / 1000000000000), orderedInterval (9025143393 / 1000000000000) (9025143399 / 1000000000000))) = true
  rfl'

theorem compactCertificate299_states : ∀ j,
    BesselStateValid (compactCertificate299.point j) (compactCertificate299.state j) :=
  compactCertificate299.statesValid_of_checks3 compactCertificate299_stateChecks0
    compactCertificate299_stateChecks1 compactCertificate299_stateChecks2
    compactCertificate299_stateChecks3 compactCertificate299_stateChecks4
    compactCertificate299_stateChecks5 compactCertificate299_stateChecks6
    compactCertificate299_stateChecks7 compactCertificate299_stateChecks8

theorem compactCertificate299_chunkChecks0_0 :
    compactCertificate299.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (345 / 2) 0 (IntervalRat.scale (345 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-28969062279 / 1000000000000) (-28969062278 / 1000000000000), orderedInterval (-53314078140 / 1000000000000) (-53314078139 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (101650175405169 / 800000000000) 0 (IntervalRat.scale (345 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (57910273158 / 1000000000000) (57910318224 / 1000000000000), orderedInterval (-40930038184 / 1000000000000) (-40929993118 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (32871578191377 / 160000000000) 0 (IntervalRat.scale (345 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-49932959673 / 1000000000000) (-49932944182 / 1000000000000), orderedInterval (24726286023 / 1000000000000) (24726301514 / 1000000000000)))) (orderedInterval (-13872833771 / 1000000000000) (-13872832429 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (29661267664083 / 800000000000) 0 (IntervalRat.scale (345 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (20810871472 / 1000000000000) (20810871474 / 1000000000000), orderedInterval (129097872210 / 1000000000000) (129097872211 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (79674337148151 / 800000000000) 0 (IntervalRat.scale (345 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-12255949676 / 1000000000000) (-12255949608 / 1000000000000), orderedInterval (79068411470 / 1000000000000) (79068411539 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (216331324223067 / 800000000000) 0 (IntervalRat.scale (345 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (41398497578 / 1000000000000) (41398497579 / 1000000000000), orderedInterval (25229626631 / 1000000000000) (25229626632 / 1000000000000)))) (orderedInterval (-3616273664 / 1000000000000) (-3616273640 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (159348674296371 / 800000000000) 0 (IntervalRat.scale (345 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-50158998254 / 1000000000000) (-50158979762 / 1000000000000), orderedInterval (26206151542 / 1000000000000) (26206170034 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (273046669417983 / 800000000000) 0 (IntervalRat.scale (345 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (14412135819 / 1000000000000) (14412135989 / 1000000000000), orderedInterval (-40733831991 / 1000000000000) (-40733831822 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (201124940870397 / 800000000000) 0 (IntervalRat.scale (345 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (38255669484 / 1000000000000) (38255669485 / 1000000000000), orderedInterval (32615490473 / 1000000000000) (32615490474 / 1000000000000)))) (orderedInterval (480036111 / 1000000000000) (480036127 / 1000000000000))) = true
  rfl'

theorem compactCertificate299_chunkChecks0_1 :
    compactCertificate299.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (308577380894931 / 800000000000) 0 (IntervalRat.scale (345 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-3687964085 / 1000000000000) (-3687964084 / 1000000000000), orderedInterval (-40453397239 / 1000000000000) (-40453397238 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (178157233925499 / 800000000000) 0 (IntervalRat.scale (345 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-22206066443 / 1000000000000) (-22206066442 / 1000000000000), orderedInterval (-48587398384 / 1000000000000) (-48587398383 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (316143137961591 / 800000000000) 0 (IntervalRat.scale (345 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (4937533411 / 1000000000000) (4937533412 / 1000000000000), orderedInterval (39825749032 / 1000000000000) (39825749033 / 1000000000000)))) (orderedInterval (-288080669 / 1000000000000) (-288080599 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (295381928492979 / 800000000000) 0 (IntervalRat.scale (345 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-26605744034 / 1000000000000) (-26605735002 / 1000000000000), orderedInterval (31915941648 / 1000000000000) (31915950680 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (210798481967907 / 800000000000) 0 (IntervalRat.scale (345 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (18653034873 / 1000000000000) (18653034874 / 1000000000000), orderedInterval (45440962732 / 1000000000000) (45440962733 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (239023011444453 / 800000000000) 0 (IntervalRat.scale (345 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-41395365308 / 1000000000000) (-41395365307 / 1000000000000), orderedInterval (-20355260385 / 1000000000000) (-20355260384 / 1000000000000)))) (orderedInterval (2453684441 / 1000000000000) (2453684625 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (199272467540757 / 800000000000) 0 (IntervalRat.scale (345 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-50197915025 / 1000000000000) (-50197914549 / 1000000000000), orderedInterval (6095800175 / 1000000000000) (6095800651 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (176063268399897 / 800000000000) 0 (IntervalRat.scale (345 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (43824330486 / 1000000000000) (43824330487 / 1000000000000), orderedInterval (31079146017 / 1000000000000) (31079146018 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (51029997577803 / 160000000000) 0 (IntervalRat.scale (345 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-29458182054 / 1000000000000) (-29458167272 / 1000000000000), orderedInterval (33636063760 / 1000000000000) (33636078542 / 1000000000000)))) (orderedInterval (-3841835592 / 1000000000000) (-3841835191 / 1000000000000))) = true
  rfl'

theorem compactCertificate299_chunkChecks0_2 :
    compactCertificate299.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (141151658861841 / 800000000000) 0 (IntervalRat.scale (345 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (57798907149 / 1000000000000) (57798907151 / 1000000000000), orderedInterval (16189195437 / 1000000000000) (16189195438 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (119655824429001 / 800000000000) 0 (IntervalRat.scale (345 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-27912634095 / 1000000000000) (-27912632113 / 1000000000000), orderedInterval (59061430703 / 1000000000000) (59061432685 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (74875059129603 / 800000000000) 0 (IntervalRat.scale (345 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (10700104630 / 1000000000000) (10700104632 / 1000000000000), orderedInterval (81720242240 / 1000000000000) (81720242241 / 1000000000000)))) (orderedInterval (-7313409876 / 1000000000000) (-7313409719 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (40268055823101 / 800000000000) 0 (IntervalRat.scale (345 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (84673687649 / 1000000000000) (84673687650 / 1000000000000), orderedInterval (73171966638 / 1000000000000) (73171966639 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (109335604812303 / 800000000000) 0 (IntervalRat.scale (345 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-47808646119 / 1000000000000) (-47808588569 / 1000000000000), orderedInterval (48882503663 / 1000000000000) (48882561213 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (149288420982831 / 800000000000) 0 (IntervalRat.scale (345 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-52061581713 / 1000000000000) (-52061565743 / 1000000000000), orderedInterval (26617292380 / 1000000000000) (26617308350 / 1000000000000)))) (orderedInterval (3511056860 / 1000000000000) (3511059411 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (63124940870397 / 800000000000) 0 (IntervalRat.scale (345 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-81992186306 / 1000000000000) (-81992186305 / 1000000000000), orderedInterval (-36157891787 / 1000000000000) (-36157891786 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (256599380046237 / 800000000000) 0 (IntervalRat.scale (345 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (39536744416 / 1000000000000) (39536744417 / 1000000000000), orderedInterval (20472101465 / 1000000000000) (20472101466 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (171396494012883 / 800000000000) 0 (IntervalRat.scale (345 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (53737398700 / 1000000000000) (53737398705 / 1000000000000), orderedInterval (9025143393 / 1000000000000) (9025143399 / 1000000000000)))) (orderedInterval (-13795198558 / 1000000000000) (-13795198509 / 1000000000000))) = true
  rfl'

theorem compactCertificate299_chunkChecks0 :
    compactCertificate299.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate299.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate299_chunkChecks0_0
    compactCertificate299_chunkChecks0_1 compactCertificate299_chunkChecks0_2

theorem compactCertificate299_chunkChecks1_0 :
    compactCertificate299.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (345 / 2) 1 (IntervalRat.scale (345 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-28969062279 / 1000000000000) (-28969062278 / 1000000000000), orderedInterval (-53314078140 / 1000000000000) (-53314078139 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (101650175405169 / 800000000000) 1 (IntervalRat.scale (345 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (57910273158 / 1000000000000) (57910318224 / 1000000000000), orderedInterval (-40930038184 / 1000000000000) (-40929993118 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (32871578191377 / 160000000000) 1 (IntervalRat.scale (345 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-49932959673 / 1000000000000) (-49932944182 / 1000000000000), orderedInterval (24726286023 / 1000000000000) (24726301514 / 1000000000000)))) (orderedInterval (-19684663161 / 1000000000000) (-19684661754 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (29661267664083 / 800000000000) 1 (IntervalRat.scale (345 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (20810871472 / 1000000000000) (20810871474 / 1000000000000), orderedInterval (129097872210 / 1000000000000) (129097872211 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (79674337148151 / 800000000000) 1 (IntervalRat.scale (345 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-12255949676 / 1000000000000) (-12255949608 / 1000000000000), orderedInterval (79068411470 / 1000000000000) (79068411539 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (216331324223067 / 800000000000) 1 (IntervalRat.scale (345 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (41398497578 / 1000000000000) (41398497579 / 1000000000000), orderedInterval (25229626631 / 1000000000000) (25229626632 / 1000000000000)))) (orderedInterval (-1445902861 / 1000000000000) (-1445902835 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (159348674296371 / 800000000000) 1 (IntervalRat.scale (345 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-50158998254 / 1000000000000) (-50158979762 / 1000000000000), orderedInterval (26206151542 / 1000000000000) (26206170034 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (273046669417983 / 800000000000) 1 (IntervalRat.scale (345 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (14412135819 / 1000000000000) (14412135989 / 1000000000000), orderedInterval (-40733831991 / 1000000000000) (-40733831822 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (201124940870397 / 800000000000) 1 (IntervalRat.scale (345 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (38255669484 / 1000000000000) (38255669485 / 1000000000000), orderedInterval (32615490473 / 1000000000000) (32615490474 / 1000000000000)))) (orderedInterval (3634720574 / 1000000000000) (3634720602 / 1000000000000))) = true
  rfl'

theorem compactCertificate299_chunkChecks1_1 :
    compactCertificate299.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (308577380894931 / 800000000000) 1 (IntervalRat.scale (345 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-3687964085 / 1000000000000) (-3687964084 / 1000000000000), orderedInterval (-40453397239 / 1000000000000) (-40453397238 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (178157233925499 / 800000000000) 1 (IntervalRat.scale (345 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-22206066443 / 1000000000000) (-22206066442 / 1000000000000), orderedInterval (-48587398384 / 1000000000000) (-48587398383 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (316143137961591 / 800000000000) 1 (IntervalRat.scale (345 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (4937533411 / 1000000000000) (4937533412 / 1000000000000), orderedInterval (39825749032 / 1000000000000) (39825749033 / 1000000000000)))) (orderedInterval (24395357335 / 1000000000000) (24395357478 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (295381928492979 / 800000000000) 1 (IntervalRat.scale (345 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-26605744034 / 1000000000000) (-26605735002 / 1000000000000), orderedInterval (31915941648 / 1000000000000) (31915950680 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (210798481967907 / 800000000000) 1 (IntervalRat.scale (345 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (18653034873 / 1000000000000) (18653034874 / 1000000000000), orderedInterval (45440962732 / 1000000000000) (45440962733 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (239023011444453 / 800000000000) 1 (IntervalRat.scale (345 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-41395365308 / 1000000000000) (-41395365307 / 1000000000000), orderedInterval (-20355260385 / 1000000000000) (-20355260384 / 1000000000000)))) (orderedInterval (5508948817 / 1000000000000) (5508949200 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (199272467540757 / 800000000000) 1 (IntervalRat.scale (345 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-50197915025 / 1000000000000) (-50197914549 / 1000000000000), orderedInterval (6095800175 / 1000000000000) (6095800651 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (176063268399897 / 800000000000) 1 (IntervalRat.scale (345 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (43824330486 / 1000000000000) (43824330487 / 1000000000000), orderedInterval (31079146017 / 1000000000000) (31079146018 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (51029997577803 / 160000000000) 1 (IntervalRat.scale (345 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-29458182054 / 1000000000000) (-29458167272 / 1000000000000), orderedInterval (33636063760 / 1000000000000) (33636078542 / 1000000000000)))) (orderedInterval (-575158746 / 1000000000000) (-575158014 / 1000000000000))) = true
  rfl'

theorem compactCertificate299_chunkChecks1_2 :
    compactCertificate299.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (141151658861841 / 800000000000) 1 (IntervalRat.scale (345 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (57798907149 / 1000000000000) (57798907151 / 1000000000000), orderedInterval (16189195437 / 1000000000000) (16189195438 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (119655824429001 / 800000000000) 1 (IntervalRat.scale (345 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-27912634095 / 1000000000000) (-27912632113 / 1000000000000), orderedInterval (59061430703 / 1000000000000) (59061432685 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (74875059129603 / 800000000000) 1 (IntervalRat.scale (345 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (10700104630 / 1000000000000) (10700104632 / 1000000000000), orderedInterval (81720242240 / 1000000000000) (81720242241 / 1000000000000)))) (orderedInterval (-4102683021 / 1000000000000) (-4102682882 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (40268055823101 / 800000000000) 1 (IntervalRat.scale (345 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (84673687649 / 1000000000000) (84673687650 / 1000000000000), orderedInterval (73171966638 / 1000000000000) (73171966639 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (109335604812303 / 800000000000) 1 (IntervalRat.scale (345 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-47808646119 / 1000000000000) (-47808588569 / 1000000000000), orderedInterval (48882503663 / 1000000000000) (48882561213 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (149288420982831 / 800000000000) 1 (IntervalRat.scale (345 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-52061581713 / 1000000000000) (-52061565743 / 1000000000000), orderedInterval (26617292380 / 1000000000000) (26617308350 / 1000000000000)))) (orderedInterval (-3479682168 / 1000000000000) (-3479679791 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (63124940870397 / 800000000000) 1 (IntervalRat.scale (345 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-81992186306 / 1000000000000) (-81992186305 / 1000000000000), orderedInterval (-36157891787 / 1000000000000) (-36157891786 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (256599380046237 / 800000000000) 1 (IntervalRat.scale (345 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (39536744416 / 1000000000000) (39536744417 / 1000000000000), orderedInterval (20472101465 / 1000000000000) (20472101466 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (171396494012883 / 800000000000) 1 (IntervalRat.scale (345 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (53737398700 / 1000000000000) (53737398705 / 1000000000000), orderedInterval (9025143393 / 1000000000000) (9025143399 / 1000000000000)))) (orderedInterval (-5301512930 / 1000000000000) (-5301512860 / 1000000000000))) = true
  rfl'

theorem compactCertificate299_chunkChecks1 :
    compactCertificate299.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate299.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate299_chunkChecks1_0
    compactCertificate299_chunkChecks1_1 compactCertificate299_chunkChecks1_2

theorem compactCertificate299_chunkChecks2_0 :
    compactCertificate299.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (345 / 2) 2 (IntervalRat.scale (345 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-28969062279 / 1000000000000) (-28969062278 / 1000000000000), orderedInterval (-53314078140 / 1000000000000) (-53314078139 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (101650175405169 / 800000000000) 2 (IntervalRat.scale (345 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (57910273158 / 1000000000000) (57910318224 / 1000000000000), orderedInterval (-40930038184 / 1000000000000) (-40929993118 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (32871578191377 / 160000000000) 2 (IntervalRat.scale (345 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-49932959673 / 1000000000000) (-49932944182 / 1000000000000), orderedInterval (24726286023 / 1000000000000) (24726301514 / 1000000000000)))) (orderedInterval (15459974389 / 1000000000000) (15459975931 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (29661267664083 / 800000000000) 2 (IntervalRat.scale (345 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (20810871472 / 1000000000000) (20810871474 / 1000000000000), orderedInterval (129097872210 / 1000000000000) (129097872211 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (79674337148151 / 800000000000) 2 (IntervalRat.scale (345 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-12255949676 / 1000000000000) (-12255949608 / 1000000000000), orderedInterval (79068411470 / 1000000000000) (79068411539 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (216331324223067 / 800000000000) 2 (IntervalRat.scale (345 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (41398497578 / 1000000000000) (41398497579 / 1000000000000), orderedInterval (25229626631 / 1000000000000) (25229626632 / 1000000000000)))) (orderedInterval (7400193375 / 1000000000000) (7400193409 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (159348674296371 / 800000000000) 2 (IntervalRat.scale (345 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-50158998254 / 1000000000000) (-50158979762 / 1000000000000), orderedInterval (26206151542 / 1000000000000) (26206170034 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (273046669417983 / 800000000000) 2 (IntervalRat.scale (345 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (14412135819 / 1000000000000) (14412135989 / 1000000000000), orderedInterval (-40733831991 / 1000000000000) (-40733831822 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (201124940870397 / 800000000000) 2 (IntervalRat.scale (345 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (38255669484 / 1000000000000) (38255669485 / 1000000000000), orderedInterval (32615490473 / 1000000000000) (32615490474 / 1000000000000)))) (orderedInterval (-244669561 / 1000000000000) (-244669510 / 1000000000000))) = true
  rfl'

theorem compactCertificate299_chunkChecks2_1 :
    compactCertificate299.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (308577380894931 / 800000000000) 2 (IntervalRat.scale (345 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-3687964085 / 1000000000000) (-3687964084 / 1000000000000), orderedInterval (-40453397239 / 1000000000000) (-40453397238 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (178157233925499 / 800000000000) 2 (IntervalRat.scale (345 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-22206066443 / 1000000000000) (-22206066442 / 1000000000000), orderedInterval (-48587398384 / 1000000000000) (-48587398383 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (316143137961591 / 800000000000) 2 (IntervalRat.scale (345 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (4937533411 / 1000000000000) (4937533412 / 1000000000000), orderedInterval (39825749032 / 1000000000000) (39825749033 / 1000000000000)))) (orderedInterval (-4359511352 / 1000000000000) (-4359511046 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (295381928492979 / 800000000000) 2 (IntervalRat.scale (345 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-26605744034 / 1000000000000) (-26605735002 / 1000000000000), orderedInterval (31915941648 / 1000000000000) (31915950680 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (210798481967907 / 800000000000) 2 (IntervalRat.scale (345 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (18653034873 / 1000000000000) (18653034874 / 1000000000000), orderedInterval (45440962732 / 1000000000000) (45440962733 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (239023011444453 / 800000000000) 2 (IntervalRat.scale (345 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-41395365308 / 1000000000000) (-41395365307 / 1000000000000), orderedInterval (-20355260385 / 1000000000000) (-20355260384 / 1000000000000)))) (orderedInterval (-6976696295 / 1000000000000) (-6976695490 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (199272467540757 / 800000000000) 2 (IntervalRat.scale (345 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-50197915025 / 1000000000000) (-50197914549 / 1000000000000), orderedInterval (6095800175 / 1000000000000) (6095800651 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (176063268399897 / 800000000000) 2 (IntervalRat.scale (345 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (43824330486 / 1000000000000) (43824330487 / 1000000000000), orderedInterval (31079146017 / 1000000000000) (31079146018 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (51029997577803 / 160000000000) 2 (IntervalRat.scale (345 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-29458182054 / 1000000000000) (-29458167272 / 1000000000000), orderedInterval (33636063760 / 1000000000000) (33636078542 / 1000000000000)))) (orderedInterval (7872590330 / 1000000000000) (7872591676 / 1000000000000))) = true
  rfl'

theorem compactCertificate299_chunkChecks2_2 :
    compactCertificate299.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (141151658861841 / 800000000000) 2 (IntervalRat.scale (345 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (57798907149 / 1000000000000) (57798907151 / 1000000000000), orderedInterval (16189195437 / 1000000000000) (16189195438 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (119655824429001 / 800000000000) 2 (IntervalRat.scale (345 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-27912634095 / 1000000000000) (-27912632113 / 1000000000000), orderedInterval (59061430703 / 1000000000000) (59061432685 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (74875059129603 / 800000000000) 2 (IntervalRat.scale (345 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (10700104630 / 1000000000000) (10700104632 / 1000000000000), orderedInterval (81720242240 / 1000000000000) (81720242241 / 1000000000000)))) (orderedInterval (8402032576 / 1000000000000) (8402032700 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (40268055823101 / 800000000000) 2 (IntervalRat.scale (345 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (84673687649 / 1000000000000) (84673687650 / 1000000000000), orderedInterval (73171966638 / 1000000000000) (73171966639 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (109335604812303 / 800000000000) 2 (IntervalRat.scale (345 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-47808646119 / 1000000000000) (-47808588569 / 1000000000000), orderedInterval (48882503663 / 1000000000000) (48882561213 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (149288420982831 / 800000000000) 2 (IntervalRat.scale (345 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-52061581713 / 1000000000000) (-52061565743 / 1000000000000), orderedInterval (26617292380 / 1000000000000) (26617308350 / 1000000000000)))) (orderedInterval (-5196937128 / 1000000000000) (-5196934843 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (63124940870397 / 800000000000) 2 (IntervalRat.scale (345 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-81992186306 / 1000000000000) (-81992186305 / 1000000000000), orderedInterval (-36157891787 / 1000000000000) (-36157891786 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (256599380046237 / 800000000000) 2 (IntervalRat.scale (345 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (39536744416 / 1000000000000) (39536744417 / 1000000000000), orderedInterval (20472101465 / 1000000000000) (20472101466 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (171396494012883 / 800000000000) 2 (IntervalRat.scale (345 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (53737398700 / 1000000000000) (53737398705 / 1000000000000), orderedInterval (9025143393 / 1000000000000) (9025143399 / 1000000000000)))) (orderedInterval (26814490879 / 1000000000000) (26814490981 / 1000000000000))) = true
  rfl'

theorem compactCertificate299_chunkChecks2 :
    compactCertificate299.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate299.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate299_chunkChecks2_0
    compactCertificate299_chunkChecks2_1 compactCertificate299_chunkChecks2_2

theorem compactCertificate299_chunkChecks3_0 :
    compactCertificate299.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (345 / 2) 3 (IntervalRat.scale (345 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-28969062279 / 1000000000000) (-28969062278 / 1000000000000), orderedInterval (-53314078140 / 1000000000000) (-53314078139 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (101650175405169 / 800000000000) 3 (IntervalRat.scale (345 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (57910273158 / 1000000000000) (57910318224 / 1000000000000), orderedInterval (-40930038184 / 1000000000000) (-40929993118 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (32871578191377 / 160000000000) 3 (IntervalRat.scale (345 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-49932959673 / 1000000000000) (-49932944182 / 1000000000000), orderedInterval (24726286023 / 1000000000000) (24726301514 / 1000000000000)))) (orderedInterval (18742698464 / 1000000000000) (18742700196 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (29661267664083 / 800000000000) 3 (IntervalRat.scale (345 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (20810871472 / 1000000000000) (20810871474 / 1000000000000), orderedInterval (129097872210 / 1000000000000) (129097872211 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (79674337148151 / 800000000000) 3 (IntervalRat.scale (345 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-12255949676 / 1000000000000) (-12255949608 / 1000000000000), orderedInterval (79068411470 / 1000000000000) (79068411539 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (216331324223067 / 800000000000) 3 (IntervalRat.scale (345 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (41398497578 / 1000000000000) (41398497579 / 1000000000000), orderedInterval (25229626631 / 1000000000000) (25229626632 / 1000000000000)))) (orderedInterval (6324734810 / 1000000000000) (6324734860 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (159348674296371 / 800000000000) 3 (IntervalRat.scale (345 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-50158998254 / 1000000000000) (-50158979762 / 1000000000000), orderedInterval (26206151542 / 1000000000000) (26206170034 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (273046669417983 / 800000000000) 3 (IntervalRat.scale (345 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (14412135819 / 1000000000000) (14412135989 / 1000000000000), orderedInterval (-40733831991 / 1000000000000) (-40733831822 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (201124940870397 / 800000000000) 3 (IntervalRat.scale (345 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (38255669484 / 1000000000000) (38255669485 / 1000000000000), orderedInterval (32615490473 / 1000000000000) (32615490474 / 1000000000000)))) (orderedInterval (-12170599488 / 1000000000000) (-12170599392 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate299_chunkChecks3_1 :
    compactCertificate299.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (308577380894931 / 800000000000) 3 (IntervalRat.scale (345 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-3687964085 / 1000000000000) (-3687964084 / 1000000000000), orderedInterval (-40453397239 / 1000000000000) (-40453397238 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (178157233925499 / 800000000000) 3 (IntervalRat.scale (345 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-22206066443 / 1000000000000) (-22206066442 / 1000000000000), orderedInterval (-48587398384 / 1000000000000) (-48587398383 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (316143137961591 / 800000000000) 3 (IntervalRat.scale (345 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (4937533411 / 1000000000000) (4937533412 / 1000000000000), orderedInterval (39825749032 / 1000000000000) (39825749033 / 1000000000000)))) (orderedInterval (-140661256074 / 1000000000000) (-140661255403 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (295381928492979 / 800000000000) 3 (IntervalRat.scale (345 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-26605744034 / 1000000000000) (-26605735002 / 1000000000000), orderedInterval (31915941648 / 1000000000000) (31915950680 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (210798481967907 / 800000000000) 3 (IntervalRat.scale (345 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (18653034873 / 1000000000000) (18653034874 / 1000000000000), orderedInterval (45440962732 / 1000000000000) (45440962733 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (239023011444453 / 800000000000) 3 (IntervalRat.scale (345 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-41395365308 / 1000000000000) (-41395365307 / 1000000000000), orderedInterval (-20355260385 / 1000000000000) (-20355260384 / 1000000000000)))) (orderedInterval (-10159870835 / 1000000000000) (-10159869137 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (199272467540757 / 800000000000) 3 (IntervalRat.scale (345 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-50197915025 / 1000000000000) (-50197914549 / 1000000000000), orderedInterval (6095800175 / 1000000000000) (6095800651 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (176063268399897 / 800000000000) 3 (IntervalRat.scale (345 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (43824330486 / 1000000000000) (43824330487 / 1000000000000), orderedInterval (31079146017 / 1000000000000) (31079146018 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (51029997577803 / 160000000000) 3 (IntervalRat.scale (345 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-29458182054 / 1000000000000) (-29458167272 / 1000000000000), orderedInterval (33636063760 / 1000000000000) (33636078542 / 1000000000000)))) (orderedInterval (-2007411518 / 1000000000000) (-2007409046 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate299_chunkChecks3_2 :
    compactCertificate299.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (141151658861841 / 800000000000) 3 (IntervalRat.scale (345 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (57798907149 / 1000000000000) (57798907151 / 1000000000000), orderedInterval (16189195437 / 1000000000000) (16189195438 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (119655824429001 / 800000000000) 3 (IntervalRat.scale (345 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-27912634095 / 1000000000000) (-27912632113 / 1000000000000), orderedInterval (59061430703 / 1000000000000) (59061432685 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (74875059129603 / 800000000000) 3 (IntervalRat.scale (345 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (10700104630 / 1000000000000) (10700104632 / 1000000000000), orderedInterval (81720242240 / 1000000000000) (81720242241 / 1000000000000)))) (orderedInterval (4475315533 / 1000000000000) (4475315645 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (40268055823101 / 800000000000) 3 (IntervalRat.scale (345 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (84673687649 / 1000000000000) (84673687650 / 1000000000000), orderedInterval (73171966638 / 1000000000000) (73171966639 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (109335604812303 / 800000000000) 3 (IntervalRat.scale (345 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-47808646119 / 1000000000000) (-47808588569 / 1000000000000), orderedInterval (48882503663 / 1000000000000) (48882561213 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (149288420982831 / 800000000000) 3 (IntervalRat.scale (345 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-52061581713 / 1000000000000) (-52061565743 / 1000000000000), orderedInterval (26617292380 / 1000000000000) (26617308350 / 1000000000000)))) (orderedInterval (3197699236 / 1000000000000) (3197701467 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (63124940870397 / 800000000000) 3 (IntervalRat.scale (345 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-81992186306 / 1000000000000) (-81992186305 / 1000000000000), orderedInterval (-36157891787 / 1000000000000) (-36157891786 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (256599380046237 / 800000000000) 3 (IntervalRat.scale (345 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (39536744416 / 1000000000000) (39536744417 / 1000000000000), orderedInterval (20472101465 / 1000000000000) (20472101466 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (171396494012883 / 800000000000) 3 (IntervalRat.scale (345 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (53737398700 / 1000000000000) (53737398705 / 1000000000000), orderedInterval (9025143393 / 1000000000000) (9025143399 / 1000000000000)))) (orderedInterval (13822871156 / 1000000000000) (13822871312 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate299_chunkChecks3 :
    compactCertificate299.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate299.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate299_chunkChecks3_0
    compactCertificate299_chunkChecks3_1 compactCertificate299_chunkChecks3_2

theorem compactCertificate299_chunkChecks4_0 :
    compactCertificate299.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (345 / 2) 4 (IntervalRat.scale (345 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-28969062279 / 1000000000000) (-28969062278 / 1000000000000), orderedInterval (-53314078140 / 1000000000000) (-53314078139 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (101650175405169 / 800000000000) 4 (IntervalRat.scale (345 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (57910273158 / 1000000000000) (57910318224 / 1000000000000), orderedInterval (-40930038184 / 1000000000000) (-40929993118 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (32871578191377 / 160000000000) 4 (IntervalRat.scale (345 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-49932959673 / 1000000000000) (-49932944182 / 1000000000000), orderedInterval (24726286023 / 1000000000000) (24726301514 / 1000000000000)))) (orderedInterval (-17435902464 / 1000000000000) (-17435900470 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (29661267664083 / 800000000000) 4 (IntervalRat.scale (345 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (20810871472 / 1000000000000) (20810871474 / 1000000000000), orderedInterval (129097872210 / 1000000000000) (129097872211 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (79674337148151 / 800000000000) 4 (IntervalRat.scale (345 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-12255949676 / 1000000000000) (-12255949608 / 1000000000000), orderedInterval (79068411470 / 1000000000000) (79068411539 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (216331324223067 / 800000000000) 4 (IntervalRat.scale (345 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (41398497578 / 1000000000000) (41398497579 / 1000000000000), orderedInterval (25229626631 / 1000000000000) (25229626632 / 1000000000000)))) (orderedInterval (-17895933964 / 1000000000000) (-17895933888 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (159348674296371 / 800000000000) 4 (IntervalRat.scale (345 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-50158998254 / 1000000000000) (-50158979762 / 1000000000000), orderedInterval (26206151542 / 1000000000000) (26206170034 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (273046669417983 / 800000000000) 4 (IntervalRat.scale (345 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (14412135819 / 1000000000000) (14412135989 / 1000000000000), orderedInterval (-40733831991 / 1000000000000) (-40733831822 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (201124940870397 / 800000000000) 4 (IntervalRat.scale (345 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (38255669484 / 1000000000000) (38255669485 / 1000000000000), orderedInterval (32615490473 / 1000000000000) (32615490474 / 1000000000000)))) (orderedInterval (-2500348482 / 1000000000000) (-2500348300 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate299_chunkChecks4_1 :
    compactCertificate299.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (308577380894931 / 800000000000) 4 (IntervalRat.scale (345 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-3687964085 / 1000000000000) (-3687964084 / 1000000000000), orderedInterval (-40453397239 / 1000000000000) (-40453397238 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (178157233925499 / 800000000000) 4 (IntervalRat.scale (345 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-22206066443 / 1000000000000) (-22206066442 / 1000000000000), orderedInterval (-48587398384 / 1000000000000) (-48587398383 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (316143137961591 / 800000000000) 4 (IntervalRat.scale (345 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (4937533411 / 1000000000000) (4937533412 / 1000000000000), orderedInterval (39825749032 / 1000000000000) (39825749033 / 1000000000000)))) (orderedInterval (32775877970 / 1000000000000) (32775879457 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (295381928492979 / 800000000000) 4 (IntervalRat.scale (345 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-26605744034 / 1000000000000) (-26605735002 / 1000000000000), orderedInterval (31915941648 / 1000000000000) (31915950680 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (210798481967907 / 800000000000) 4 (IntervalRat.scale (345 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (18653034873 / 1000000000000) (18653034874 / 1000000000000), orderedInterval (45440962732 / 1000000000000) (45440962733 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (239023011444453 / 800000000000) 4 (IntervalRat.scale (345 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-41395365308 / 1000000000000) (-41395365307 / 1000000000000), orderedInterval (-20355260385 / 1000000000000) (-20355260384 / 1000000000000)))) (orderedInterval (21688275461 / 1000000000000) (21688279065 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (199272467540757 / 800000000000) 4 (IntervalRat.scale (345 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-50197915025 / 1000000000000) (-50197914549 / 1000000000000), orderedInterval (6095800175 / 1000000000000) (6095800651 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (176063268399897 / 800000000000) 4 (IntervalRat.scale (345 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (43824330486 / 1000000000000) (43824330487 / 1000000000000), orderedInterval (31079146017 / 1000000000000) (31079146018 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (51029997577803 / 160000000000) 4 (IntervalRat.scale (345 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-29458182054 / 1000000000000) (-29458167272 / 1000000000000), orderedInterval (33636063760 / 1000000000000) (33636078542 / 1000000000000)))) (orderedInterval (-17955537255 / 1000000000000) (-17955532693 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate299_chunkChecks4_2 :
    compactCertificate299.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (141151658861841 / 800000000000) 4 (IntervalRat.scale (345 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (57798907149 / 1000000000000) (57798907151 / 1000000000000), orderedInterval (16189195437 / 1000000000000) (16189195438 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (119655824429001 / 800000000000) 4 (IntervalRat.scale (345 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-27912634095 / 1000000000000) (-27912632113 / 1000000000000), orderedInterval (59061430703 / 1000000000000) (59061432685 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (74875059129603 / 800000000000) 4 (IntervalRat.scale (345 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (10700104630 / 1000000000000) (10700104632 / 1000000000000), orderedInterval (81720242240 / 1000000000000) (81720242241 / 1000000000000)))) (orderedInterval (-9243664065 / 1000000000000) (-9243663963 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (40268055823101 / 800000000000) 4 (IntervalRat.scale (345 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (84673687649 / 1000000000000) (84673687650 / 1000000000000), orderedInterval (73171966638 / 1000000000000) (73171966639 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (109335604812303 / 800000000000) 4 (IntervalRat.scale (345 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-47808646119 / 1000000000000) (-47808588569 / 1000000000000), orderedInterval (48882503663 / 1000000000000) (48882561213 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (149288420982831 / 800000000000) 4 (IntervalRat.scale (345 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-52061581713 / 1000000000000) (-52061565743 / 1000000000000), orderedInterval (26617292380 / 1000000000000) (26617308350 / 1000000000000)))) (orderedInterval (5843343234 / 1000000000000) (5843345470 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (63124940870397 / 800000000000) 4 (IntervalRat.scale (345 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-81992186306 / 1000000000000) (-81992186305 / 1000000000000), orderedInterval (-36157891787 / 1000000000000) (-36157891786 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (256599380046237 / 800000000000) 4 (IntervalRat.scale (345 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (39536744416 / 1000000000000) (39536744417 / 1000000000000), orderedInterval (20472101465 / 1000000000000) (20472101466 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (171396494012883 / 800000000000) 4 (IntervalRat.scale (345 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (53737398700 / 1000000000000) (53737398705 / 1000000000000), orderedInterval (9025143393 / 1000000000000) (9025143399 / 1000000000000)))) (orderedInterval (-62644425858 / 1000000000000) (-62644425609 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate299_chunkChecks4 :
    compactCertificate299.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate299.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate299_chunkChecks4_0
    compactCertificate299_chunkChecks4_1 compactCertificate299_chunkChecks4_2

theorem compactCertificate299_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate299.chunkCheck r b = true :=
  compactCertificate299.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate299_chunkChecks0
    · exact compactCertificate299_chunkChecks1
    · exact compactCertificate299_chunkChecks2
    · exact compactCertificate299_chunkChecks3
    · exact compactCertificate299_chunkChecks4)

theorem compactCertificate299_coefficient0 :
    compactCertificate299.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate299_coefficient1 :
    compactCertificate299.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate299_coefficient2 :
    compactCertificate299.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate299_coefficient3 :
    compactCertificate299.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate299_coefficient4 :
    compactCertificate299.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate299_coefficients : ∀ r : Fin 5,
    compactCertificate299.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate299_coefficient0
  · exact compactCertificate299_coefficient1
  · exact compactCertificate299_coefficient2
  · exact compactCertificate299_coefficient3
  · exact compactCertificate299_coefficient4

theorem compactCertificate299_lower : (1 : ℚ) ≤ compactCertificate299.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate299, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate299_proves {t : ℝ} (ht : t ∈ compactCertificate299.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate299.proves compactCertificate299_states compactCertificate299_chunks
    compactCertificate299_coefficients compactCertificate299_lower ht

end Erdos232
