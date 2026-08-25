/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate392 : CompactCertificate where
  left := 263
  right := 264
  center := 527 / 2
  grid := fun i =>
    match i.val with
    | 0 => 84
    | 1 => 62
    | 2 => 100
    | 3 => 18
    | 4 => 48
    | 5 => 132
    | 6 => 97
    | 7 => 166
    | 8 => 122
    | 9 => 188
    | 10 => 108
    | 11 => 192
    | 12 => 180
    | 13 => 128
    | 14 => 145
    | 15 => 121
    | 16 => 107
    | 17 => 155
    | 18 => 86
    | 19 => 73
    | 20 => 46
    | 21 => 24
    | 22 => 66
    | 23 => 91
    | 24 => 38
    | 25 => 156
    | _ => 104
  point := fun i =>
    match i.val with
    | 0 => 527 / 2
    | 1 => 776371629543827 / 4000000000000
    | 2 => 251062633432691 / 800000000000
    | 3 => 226543305202489 / 4000000000000
    | 4 => 608527183725733 / 4000000000000
    | 5 => 1652269679210961 / 4000000000000
    | 6 => 1217054367451993 / 4000000000000
    | 7 => 2085443402656189 / 4000000000000
    | 8 => 1536128171575351 / 4000000000000
    | 9 => 2356815648284473 / 4000000000000
    | 10 => 1360708148967217 / 4000000000000
    | 11 => 2414600488489253 / 4000000000000
    | 12 => 2256032990084057 / 4000000000000
    | 13 => 1610011594160681 / 4000000000000
    | 14 => 1825581551177199 / 4000000000000
    | 15 => 1521979570927231 / 4000000000000
    | 16 => 1344715107923851 / 4000000000000
    | 17 => 389750851065249 / 800000000000
    | 18 => 1078071365510003 / 4000000000000
    | 19 => 913893035856283 / 4000000000000
    | 20 => 571871828424649 / 4000000000000
    | 21 => 307554571286583 / 4000000000000
    | 22 => 835070488928749 / 4000000000000
    | 23 => 1140217360260173 / 4000000000000
    | 24 => 482128171575351 / 4000000000000
    | 25 => 1959824250498071 / 4000000000000
    | _ => 1309071773112889 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (18739226979 / 1000000000000) (18739226980 / 1000000000000), orderedInterval (45405158957 / 1000000000000) (45405158958 / 1000000000000))
    | 1 => (orderedInterval (5655839083 / 1000000000000) (5655839085 / 1000000000000), orderedInterval (56976627561 / 1000000000000) (56976627562 / 1000000000000))
    | 2 => (orderedInterval (19753768049 / 1000000000000) (19753768050 / 1000000000000), orderedInterval (40445077052 / 1000000000000) (40445077053 / 1000000000000))
    | 3 => (orderedInterval (81057735629 / 1000000000000) (81057735630 / 1000000000000), orderedInterval (67622973310 / 1000000000000) (67622973311 / 1000000000000))
    | 4 => (orderedInterval (55178185289 / 1000000000000) (55178213721 / 1000000000000), orderedInterval (-33945477040 / 1000000000000) (-33945448609 / 1000000000000))
    | 5 => (orderedInterval (-29173345338 / 1000000000000) (-29173316701 / 1000000000000), orderedInterval (26305381237 / 1000000000000) (26305409874 / 1000000000000))
    | 6 => (orderedInterval (-14132108264 / 1000000000000) (-14132108263 / 1000000000000), orderedInterval (-43480978417 / 1000000000000) (-43480978416 / 1000000000000))
    | 7 => (orderedInterval (20913926478 / 1000000000000) (20913926479 / 1000000000000), orderedInterval (27974246988 / 1000000000000) (27974246989 / 1000000000000))
    | 8 => (orderedInterval (40699218309 / 1000000000000) (40699218479 / 1000000000000), orderedInterval (1086256307 / 1000000000000) (1086256478 / 1000000000000))
    | 9 => (orderedInterval (-19374041168 / 1000000000000) (-19374039828 / 1000000000000), orderedInterval (26570557026 / 1000000000000) (26570558366 / 1000000000000))
    | 10 => (orderedInterval (43047123125 / 1000000000000) (43047123787 / 1000000000000), orderedInterval (-4350441271 / 1000000000000) (-4350440610 / 1000000000000))
    | 11 => (orderedInterval (30813265823 / 1000000000000) (30813265835 / 1000000000000), orderedInterval (10229208707 / 1000000000000) (10229208719 / 1000000000000))
    | 12 => (orderedInterval (-21469772748 / 1000000000000) (-21469769605 / 1000000000000), orderedInterval (25860683261 / 1000000000000) (25860686403 / 1000000000000))
    | 13 => (orderedInterval (36526467721 / 1000000000000) (36526467722 / 1000000000000), orderedInterval (15685772015 / 1000000000000) (15685772017 / 1000000000000))
    | 14 => (orderedInterval (-37232329165 / 1000000000000) (-37232328114 / 1000000000000), orderedInterval (2980073259 / 1000000000000) (2980074310 / 1000000000000))
    | 15 => (orderedInterval (-37289600094 / 1000000000000) (-37289600092 / 1000000000000), orderedInterval (-16762332645 / 1000000000000) (-16762332644 / 1000000000000))
    | 16 => (orderedInterval (-31620010805 / 1000000000000) (-31620010804 / 1000000000000), orderedInterval (-29850612198 / 1000000000000) (-29850612197 / 1000000000000))
    | 17 => (orderedInterval (-30931267525 / 1000000000000) (-30931267524 / 1000000000000), orderedInterval (-18675950926 / 1000000000000) (-18675950925 / 1000000000000))
    | 18 => (orderedInterval (6098266125 / 1000000000000) (6098266126 / 1000000000000), orderedInterval (48205739897 / 1000000000000) (48205739898 / 1000000000000))
    | 19 => (orderedInterval (4121251649 / 1000000000000) (4121251658 / 1000000000000), orderedInterval (-52634394320 / 1000000000000) (-52634394312 / 1000000000000))
    | 20 => (orderedInterval (-46009332364 / 1000000000000) (-46009283417 / 1000000000000), orderedInterval (48493365430 / 1000000000000) (48493414376 / 1000000000000))
    | 21 => (orderedInterval (69395230185 / 1000000000000) (69395310119 / 1000000000000), orderedInterval (-59307308731 / 1000000000000) (-59307228796 / 1000000000000))
    | 22 => (orderedInterval (44407672924 / 1000000000000) (44407752167 / 1000000000000), orderedInterval (-32929716705 / 1000000000000) (-32929637462 / 1000000000000))
    | 23 => (orderedInterval (2155720107 / 1000000000000) (2155720110 / 1000000000000), orderedInterval (-47212721676 / 1000000000000) (-47212721673 / 1000000000000))
    | 24 => (orderedInterval (67885484790 / 1000000000000) (67885488704 / 1000000000000), orderedInterval (-26229127791 / 1000000000000) (-26229123877 / 1000000000000))
    | 25 => (orderedInterval (21893645253 / 1000000000000) (21893645254 / 1000000000000), orderedInterval (28613457005 / 1000000000000) (28613457006 / 1000000000000))
    | _ => (orderedInterval (42804219094 / 1000000000000) (42804219099 / 1000000000000), orderedInterval (10567211192 / 1000000000000) (10567211196 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (8639448637 / 1000000000000) (8639448657 / 1000000000000)
      | 1 => orderedInterval (3209153519 / 1000000000000) (3209156625 / 1000000000000)
      | 2 => orderedInterval (338550630 / 1000000000000) (338550650 / 1000000000000)
      | 3 => orderedInterval (11012257780 / 1000000000000) (11012258174 / 1000000000000)
      | 4 => orderedInterval (4030060080 / 1000000000000) (4030060174 / 1000000000000)
      | 5 => orderedInterval (586937509 / 1000000000000) (586937535 / 1000000000000)
      | 6 => orderedInterval (-2706175642 / 1000000000000) (-2706173982 / 1000000000000)
      | 7 => orderedInterval (-2454077035 / 1000000000000) (-2454073729 / 1000000000000)
      | _ => orderedInterval (-9404152667 / 1000000000000) (-9404152569 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (21214756339 / 1000000000000) (21214756360 / 1000000000000)
      | 1 => orderedInterval (-3804775957 / 1000000000000) (-3804772130 / 1000000000000)
      | 2 => orderedInterval (-1668948519 / 1000000000000) (-1668948486 / 1000000000000)
      | 3 => orderedInterval (-7641920289 / 1000000000000) (-7641919472 / 1000000000000)
      | 4 => orderedInterval (1240343354 / 1000000000000) (1240343536 / 1000000000000)
      | 5 => orderedInterval (1015803047 / 1000000000000) (1015803084 / 1000000000000)
      | 6 => orderedInterval (-4444100170 / 1000000000000) (-4444099243 / 1000000000000)
      | 7 => orderedInterval (4825755295 / 1000000000000) (4825757179 / 1000000000000)
      | _ => orderedInterval (-6865760120 / 1000000000000) (-6865760005 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-9180942955 / 1000000000000) (-9180942930 / 1000000000000)
      | 1 => orderedInterval (-5712998152 / 1000000000000) (-5712992739 / 1000000000000)
      | 2 => orderedInterval (442384786 / 1000000000000) (442384842 / 1000000000000)
      | 3 => orderedInterval (-45487963220 / 1000000000000) (-45487961472 / 1000000000000)
      | 4 => orderedInterval (-10405180007 / 1000000000000) (-10405179646 / 1000000000000)
      | 5 => orderedInterval (655962880 / 1000000000000) (655962935 / 1000000000000)
      | 6 => orderedInterval (1653291512 / 1000000000000) (1653292043 / 1000000000000)
      | 7 => orderedInterval (916545323 / 1000000000000) (916546613 / 1000000000000)
      | _ => orderedInterval (18490912818 / 1000000000000) (18490912976 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-22183627763 / 1000000000000) (-22183627734 / 1000000000000)
      | 1 => orderedInterval (7471405299 / 1000000000000) (7471413437 / 1000000000000)
      | 2 => orderedInterval (6600504042 / 1000000000000) (6600504139 / 1000000000000)
      | 3 => orderedInterval (36168238684 / 1000000000000) (36168242493 / 1000000000000)
      | 4 => orderedInterval (-590598954 / 1000000000000) (-590598225 / 1000000000000)
      | 5 => orderedInterval (55167595 / 1000000000000) (55167679 / 1000000000000)
      | 6 => orderedInterval (6047472926 / 1000000000000) (6047473240 / 1000000000000)
      | 7 => orderedInterval (-4983044645 / 1000000000000) (-4983043680 / 1000000000000)
      | _ => orderedInterval (18717316974 / 1000000000000) (18717317212 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (9943684941 / 1000000000000) (9943684975 / 1000000000000)
      | 1 => orderedInterval (12689480876 / 1000000000000) (12689493461 / 1000000000000)
      | 2 => orderedInterval (-5498605659 / 1000000000000) (-5498605486 / 1000000000000)
      | 3 => orderedInterval (215296017809 / 1000000000000) (215296026223 / 1000000000000)
      | 4 => orderedInterval (28641216356 / 1000000000000) (28641217849 / 1000000000000)
      | 5 => orderedInterval (-6333261794 / 1000000000000) (-6333261661 / 1000000000000)
      | 6 => orderedInterval (-1374769271 / 1000000000000) (-1374769074 / 1000000000000)
      | 7 => orderedInterval (-594701486 / 1000000000000) (-594700729 / 1000000000000)
      | _ => orderedInterval (-40538237245 / 1000000000000) (-40538236865 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (13252002811 / 1000000000000) (13252011535 / 1000000000000)
    | 1 => orderedInterval (3871152980 / 1000000000000) (3871160823 / 1000000000000)
    | 2 => orderedInterval (-48627987015 / 1000000000000) (-48627977378 / 1000000000000)
    | 3 => orderedInterval (47302834158 / 1000000000000) (47302848561 / 1000000000000)
    | _ => orderedInterval (212230824527 / 1000000000000) (212230848693 / 1000000000000)

theorem compactCertificate392_stateChecks0 :
    compactCertificate392.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 84 12 (527 / 2)) (orderedInterval (18739226979 / 1000000000000) (18739226980 / 1000000000000), orderedInterval (45405158957 / 1000000000000) (45405158958 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (776371629543827 / 4000000000000)) (orderedInterval (5655839083 / 1000000000000) (5655839085 / 1000000000000), orderedInterval (56976627561 / 1000000000000) (56976627562 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 100 12 (251062633432691 / 800000000000)) (orderedInterval (19753768049 / 1000000000000) (19753768050 / 1000000000000), orderedInterval (40445077052 / 1000000000000) (40445077053 / 1000000000000))) = true
  rfl'

theorem compactCertificate392_stateChecks1 :
    compactCertificate392.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 18 12 (226543305202489 / 4000000000000)) (orderedInterval (81057735629 / 1000000000000) (81057735630 / 1000000000000), orderedInterval (67622973310 / 1000000000000) (67622973311 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 48 12 (608527183725733 / 4000000000000)) (orderedInterval (55178185289 / 1000000000000) (55178213721 / 1000000000000), orderedInterval (-33945477040 / 1000000000000) (-33945448609 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 132 12 (1652269679210961 / 4000000000000)) (orderedInterval (-29173345338 / 1000000000000) (-29173316701 / 1000000000000), orderedInterval (26305381237 / 1000000000000) (26305409874 / 1000000000000))) = true
  rfl'

theorem compactCertificate392_stateChecks2 :
    compactCertificate392.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 97 12 (1217054367451993 / 4000000000000)) (orderedInterval (-14132108264 / 1000000000000) (-14132108263 / 1000000000000), orderedInterval (-43480978417 / 1000000000000) (-43480978416 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 166 12 (2085443402656189 / 4000000000000)) (orderedInterval (20913926478 / 1000000000000) (20913926479 / 1000000000000), orderedInterval (27974246988 / 1000000000000) (27974246989 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 122 12 (1536128171575351 / 4000000000000)) (orderedInterval (40699218309 / 1000000000000) (40699218479 / 1000000000000), orderedInterval (1086256307 / 1000000000000) (1086256478 / 1000000000000))) = true
  rfl'

theorem compactCertificate392_stateChecks3 :
    compactCertificate392.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 188 12 (2356815648284473 / 4000000000000)) (orderedInterval (-19374041168 / 1000000000000) (-19374039828 / 1000000000000), orderedInterval (26570557026 / 1000000000000) (26570558366 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 108 12 (1360708148967217 / 4000000000000)) (orderedInterval (43047123125 / 1000000000000) (43047123787 / 1000000000000), orderedInterval (-4350441271 / 1000000000000) (-4350440610 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 192 12 (2414600488489253 / 4000000000000)) (orderedInterval (30813265823 / 1000000000000) (30813265835 / 1000000000000), orderedInterval (10229208707 / 1000000000000) (10229208719 / 1000000000000))) = true
  rfl'

theorem compactCertificate392_stateChecks4 :
    compactCertificate392.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 180 12 (2256032990084057 / 4000000000000)) (orderedInterval (-21469772748 / 1000000000000) (-21469769605 / 1000000000000), orderedInterval (25860683261 / 1000000000000) (25860686403 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 128 12 (1610011594160681 / 4000000000000)) (orderedInterval (36526467721 / 1000000000000) (36526467722 / 1000000000000), orderedInterval (15685772015 / 1000000000000) (15685772017 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 145 12 (1825581551177199 / 4000000000000)) (orderedInterval (-37232329165 / 1000000000000) (-37232328114 / 1000000000000), orderedInterval (2980073259 / 1000000000000) (2980074310 / 1000000000000))) = true
  rfl'

theorem compactCertificate392_stateChecks5 :
    compactCertificate392.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 121 12 (1521979570927231 / 4000000000000)) (orderedInterval (-37289600094 / 1000000000000) (-37289600092 / 1000000000000), orderedInterval (-16762332645 / 1000000000000) (-16762332644 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 107 12 (1344715107923851 / 4000000000000)) (orderedInterval (-31620010805 / 1000000000000) (-31620010804 / 1000000000000), orderedInterval (-29850612198 / 1000000000000) (-29850612197 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 155 12 (389750851065249 / 800000000000)) (orderedInterval (-30931267525 / 1000000000000) (-30931267524 / 1000000000000), orderedInterval (-18675950926 / 1000000000000) (-18675950925 / 1000000000000))) = true
  rfl'

theorem compactCertificate392_stateChecks6 :
    compactCertificate392.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 86 12 (1078071365510003 / 4000000000000)) (orderedInterval (6098266125 / 1000000000000) (6098266126 / 1000000000000), orderedInterval (48205739897 / 1000000000000) (48205739898 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 73 12 (913893035856283 / 4000000000000)) (orderedInterval (4121251649 / 1000000000000) (4121251658 / 1000000000000), orderedInterval (-52634394320 / 1000000000000) (-52634394312 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (571871828424649 / 4000000000000)) (orderedInterval (-46009332364 / 1000000000000) (-46009283417 / 1000000000000), orderedInterval (48493365430 / 1000000000000) (48493414376 / 1000000000000))) = true
  rfl'

theorem compactCertificate392_stateChecks7 :
    compactCertificate392.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 24 12 (307554571286583 / 4000000000000)) (orderedInterval (69395230185 / 1000000000000) (69395310119 / 1000000000000), orderedInterval (-59307308731 / 1000000000000) (-59307228796 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (835070488928749 / 4000000000000)) (orderedInterval (44407672924 / 1000000000000) (44407752167 / 1000000000000), orderedInterval (-32929716705 / 1000000000000) (-32929637462 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 91 12 (1140217360260173 / 4000000000000)) (orderedInterval (2155720107 / 1000000000000) (2155720110 / 1000000000000), orderedInterval (-47212721676 / 1000000000000) (-47212721673 / 1000000000000))) = true
  rfl'

theorem compactCertificate392_stateChecks8 :
    compactCertificate392.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (482128171575351 / 4000000000000)) (orderedInterval (67885484790 / 1000000000000) (67885488704 / 1000000000000), orderedInterval (-26229127791 / 1000000000000) (-26229123877 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 156 12 (1959824250498071 / 4000000000000)) (orderedInterval (21893645253 / 1000000000000) (21893645254 / 1000000000000), orderedInterval (28613457005 / 1000000000000) (28613457006 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 104 12 (1309071773112889 / 4000000000000)) (orderedInterval (42804219094 / 1000000000000) (42804219099 / 1000000000000), orderedInterval (10567211192 / 1000000000000) (10567211196 / 1000000000000))) = true
  rfl'

theorem compactCertificate392_states : ∀ j,
    BesselStateValid (compactCertificate392.point j) (compactCertificate392.state j) :=
  compactCertificate392.statesValid_of_checks3 compactCertificate392_stateChecks0
    compactCertificate392_stateChecks1 compactCertificate392_stateChecks2
    compactCertificate392_stateChecks3 compactCertificate392_stateChecks4
    compactCertificate392_stateChecks5 compactCertificate392_stateChecks6
    compactCertificate392_stateChecks7 compactCertificate392_stateChecks8

theorem compactCertificate392_chunkChecks0_0 :
    compactCertificate392.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (527 / 2) 0 (IntervalRat.scale (527 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (18739226979 / 1000000000000) (18739226980 / 1000000000000), orderedInterval (45405158957 / 1000000000000) (45405158958 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (776371629543827 / 4000000000000) 0 (IntervalRat.scale (527 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (5655839083 / 1000000000000) (5655839085 / 1000000000000), orderedInterval (56976627561 / 1000000000000) (56976627562 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (251062633432691 / 800000000000) 0 (IntervalRat.scale (527 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (19753768049 / 1000000000000) (19753768050 / 1000000000000), orderedInterval (40445077052 / 1000000000000) (40445077053 / 1000000000000)))) (orderedInterval (8639448637 / 1000000000000) (8639448657 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (226543305202489 / 4000000000000) 0 (IntervalRat.scale (527 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (81057735629 / 1000000000000) (81057735630 / 1000000000000), orderedInterval (67622973310 / 1000000000000) (67622973311 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (608527183725733 / 4000000000000) 0 (IntervalRat.scale (527 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (55178185289 / 1000000000000) (55178213721 / 1000000000000), orderedInterval (-33945477040 / 1000000000000) (-33945448609 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1652269679210961 / 4000000000000) 0 (IntervalRat.scale (527 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29173345338 / 1000000000000) (-29173316701 / 1000000000000), orderedInterval (26305381237 / 1000000000000) (26305409874 / 1000000000000)))) (orderedInterval (3209153519 / 1000000000000) (3209156625 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1217054367451993 / 4000000000000) 0 (IntervalRat.scale (527 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-14132108264 / 1000000000000) (-14132108263 / 1000000000000), orderedInterval (-43480978417 / 1000000000000) (-43480978416 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2085443402656189 / 4000000000000) 0 (IntervalRat.scale (527 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (20913926478 / 1000000000000) (20913926479 / 1000000000000), orderedInterval (27974246988 / 1000000000000) (27974246989 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1536128171575351 / 4000000000000) 0 (IntervalRat.scale (527 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (40699218309 / 1000000000000) (40699218479 / 1000000000000), orderedInterval (1086256307 / 1000000000000) (1086256478 / 1000000000000)))) (orderedInterval (338550630 / 1000000000000) (338550650 / 1000000000000))) = true
  rfl'

theorem compactCertificate392_chunkChecks0_1 :
    compactCertificate392.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2356815648284473 / 4000000000000) 0 (IntervalRat.scale (527 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-19374041168 / 1000000000000) (-19374039828 / 1000000000000), orderedInterval (26570557026 / 1000000000000) (26570558366 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1360708148967217 / 4000000000000) 0 (IntervalRat.scale (527 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (43047123125 / 1000000000000) (43047123787 / 1000000000000), orderedInterval (-4350441271 / 1000000000000) (-4350440610 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2414600488489253 / 4000000000000) 0 (IntervalRat.scale (527 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (30813265823 / 1000000000000) (30813265835 / 1000000000000), orderedInterval (10229208707 / 1000000000000) (10229208719 / 1000000000000)))) (orderedInterval (11012257780 / 1000000000000) (11012258174 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2256032990084057 / 4000000000000) 0 (IntervalRat.scale (527 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-21469772748 / 1000000000000) (-21469769605 / 1000000000000), orderedInterval (25860683261 / 1000000000000) (25860686403 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1610011594160681 / 4000000000000) 0 (IntervalRat.scale (527 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (36526467721 / 1000000000000) (36526467722 / 1000000000000), orderedInterval (15685772015 / 1000000000000) (15685772017 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1825581551177199 / 4000000000000) 0 (IntervalRat.scale (527 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-37232329165 / 1000000000000) (-37232328114 / 1000000000000), orderedInterval (2980073259 / 1000000000000) (2980074310 / 1000000000000)))) (orderedInterval (4030060080 / 1000000000000) (4030060174 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1521979570927231 / 4000000000000) 0 (IntervalRat.scale (527 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-37289600094 / 1000000000000) (-37289600092 / 1000000000000), orderedInterval (-16762332645 / 1000000000000) (-16762332644 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1344715107923851 / 4000000000000) 0 (IntervalRat.scale (527 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-31620010805 / 1000000000000) (-31620010804 / 1000000000000), orderedInterval (-29850612198 / 1000000000000) (-29850612197 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (389750851065249 / 800000000000) 0 (IntervalRat.scale (527 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-30931267525 / 1000000000000) (-30931267524 / 1000000000000), orderedInterval (-18675950926 / 1000000000000) (-18675950925 / 1000000000000)))) (orderedInterval (586937509 / 1000000000000) (586937535 / 1000000000000))) = true
  rfl'

theorem compactCertificate392_chunkChecks0_2 :
    compactCertificate392.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1078071365510003 / 4000000000000) 0 (IntervalRat.scale (527 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (6098266125 / 1000000000000) (6098266126 / 1000000000000), orderedInterval (48205739897 / 1000000000000) (48205739898 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (913893035856283 / 4000000000000) 0 (IntervalRat.scale (527 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (4121251649 / 1000000000000) (4121251658 / 1000000000000), orderedInterval (-52634394320 / 1000000000000) (-52634394312 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (571871828424649 / 4000000000000) 0 (IntervalRat.scale (527 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-46009332364 / 1000000000000) (-46009283417 / 1000000000000), orderedInterval (48493365430 / 1000000000000) (48493414376 / 1000000000000)))) (orderedInterval (-2706175642 / 1000000000000) (-2706173982 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (307554571286583 / 4000000000000) 0 (IntervalRat.scale (527 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (69395230185 / 1000000000000) (69395310119 / 1000000000000), orderedInterval (-59307308731 / 1000000000000) (-59307228796 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (835070488928749 / 4000000000000) 0 (IntervalRat.scale (527 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (44407672924 / 1000000000000) (44407752167 / 1000000000000), orderedInterval (-32929716705 / 1000000000000) (-32929637462 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1140217360260173 / 4000000000000) 0 (IntervalRat.scale (527 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (2155720107 / 1000000000000) (2155720110 / 1000000000000), orderedInterval (-47212721676 / 1000000000000) (-47212721673 / 1000000000000)))) (orderedInterval (-2454077035 / 1000000000000) (-2454073729 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (482128171575351 / 4000000000000) 0 (IntervalRat.scale (527 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (67885484790 / 1000000000000) (67885488704 / 1000000000000), orderedInterval (-26229127791 / 1000000000000) (-26229123877 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1959824250498071 / 4000000000000) 0 (IntervalRat.scale (527 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (21893645253 / 1000000000000) (21893645254 / 1000000000000), orderedInterval (28613457005 / 1000000000000) (28613457006 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1309071773112889 / 4000000000000) 0 (IntervalRat.scale (527 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (42804219094 / 1000000000000) (42804219099 / 1000000000000), orderedInterval (10567211192 / 1000000000000) (10567211196 / 1000000000000)))) (orderedInterval (-9404152667 / 1000000000000) (-9404152569 / 1000000000000))) = true
  rfl'

theorem compactCertificate392_chunkChecks0 :
    compactCertificate392.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate392.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate392_chunkChecks0_0
    compactCertificate392_chunkChecks0_1 compactCertificate392_chunkChecks0_2

theorem compactCertificate392_chunkChecks1_0 :
    compactCertificate392.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (527 / 2) 1 (IntervalRat.scale (527 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (18739226979 / 1000000000000) (18739226980 / 1000000000000), orderedInterval (45405158957 / 1000000000000) (45405158958 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (776371629543827 / 4000000000000) 1 (IntervalRat.scale (527 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (5655839083 / 1000000000000) (5655839085 / 1000000000000), orderedInterval (56976627561 / 1000000000000) (56976627562 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (251062633432691 / 800000000000) 1 (IntervalRat.scale (527 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (19753768049 / 1000000000000) (19753768050 / 1000000000000), orderedInterval (40445077052 / 1000000000000) (40445077053 / 1000000000000)))) (orderedInterval (21214756339 / 1000000000000) (21214756360 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (226543305202489 / 4000000000000) 1 (IntervalRat.scale (527 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (81057735629 / 1000000000000) (81057735630 / 1000000000000), orderedInterval (67622973310 / 1000000000000) (67622973311 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (608527183725733 / 4000000000000) 1 (IntervalRat.scale (527 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (55178185289 / 1000000000000) (55178213721 / 1000000000000), orderedInterval (-33945477040 / 1000000000000) (-33945448609 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1652269679210961 / 4000000000000) 1 (IntervalRat.scale (527 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29173345338 / 1000000000000) (-29173316701 / 1000000000000), orderedInterval (26305381237 / 1000000000000) (26305409874 / 1000000000000)))) (orderedInterval (-3804775957 / 1000000000000) (-3804772130 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1217054367451993 / 4000000000000) 1 (IntervalRat.scale (527 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-14132108264 / 1000000000000) (-14132108263 / 1000000000000), orderedInterval (-43480978417 / 1000000000000) (-43480978416 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2085443402656189 / 4000000000000) 1 (IntervalRat.scale (527 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (20913926478 / 1000000000000) (20913926479 / 1000000000000), orderedInterval (27974246988 / 1000000000000) (27974246989 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1536128171575351 / 4000000000000) 1 (IntervalRat.scale (527 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (40699218309 / 1000000000000) (40699218479 / 1000000000000), orderedInterval (1086256307 / 1000000000000) (1086256478 / 1000000000000)))) (orderedInterval (-1668948519 / 1000000000000) (-1668948486 / 1000000000000))) = true
  rfl'

theorem compactCertificate392_chunkChecks1_1 :
    compactCertificate392.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2356815648284473 / 4000000000000) 1 (IntervalRat.scale (527 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-19374041168 / 1000000000000) (-19374039828 / 1000000000000), orderedInterval (26570557026 / 1000000000000) (26570558366 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1360708148967217 / 4000000000000) 1 (IntervalRat.scale (527 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (43047123125 / 1000000000000) (43047123787 / 1000000000000), orderedInterval (-4350441271 / 1000000000000) (-4350440610 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2414600488489253 / 4000000000000) 1 (IntervalRat.scale (527 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (30813265823 / 1000000000000) (30813265835 / 1000000000000), orderedInterval (10229208707 / 1000000000000) (10229208719 / 1000000000000)))) (orderedInterval (-7641920289 / 1000000000000) (-7641919472 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2256032990084057 / 4000000000000) 1 (IntervalRat.scale (527 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-21469772748 / 1000000000000) (-21469769605 / 1000000000000), orderedInterval (25860683261 / 1000000000000) (25860686403 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1610011594160681 / 4000000000000) 1 (IntervalRat.scale (527 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (36526467721 / 1000000000000) (36526467722 / 1000000000000), orderedInterval (15685772015 / 1000000000000) (15685772017 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1825581551177199 / 4000000000000) 1 (IntervalRat.scale (527 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-37232329165 / 1000000000000) (-37232328114 / 1000000000000), orderedInterval (2980073259 / 1000000000000) (2980074310 / 1000000000000)))) (orderedInterval (1240343354 / 1000000000000) (1240343536 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1521979570927231 / 4000000000000) 1 (IntervalRat.scale (527 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-37289600094 / 1000000000000) (-37289600092 / 1000000000000), orderedInterval (-16762332645 / 1000000000000) (-16762332644 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1344715107923851 / 4000000000000) 1 (IntervalRat.scale (527 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-31620010805 / 1000000000000) (-31620010804 / 1000000000000), orderedInterval (-29850612198 / 1000000000000) (-29850612197 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (389750851065249 / 800000000000) 1 (IntervalRat.scale (527 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-30931267525 / 1000000000000) (-30931267524 / 1000000000000), orderedInterval (-18675950926 / 1000000000000) (-18675950925 / 1000000000000)))) (orderedInterval (1015803047 / 1000000000000) (1015803084 / 1000000000000))) = true
  rfl'

theorem compactCertificate392_chunkChecks1_2 :
    compactCertificate392.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1078071365510003 / 4000000000000) 1 (IntervalRat.scale (527 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (6098266125 / 1000000000000) (6098266126 / 1000000000000), orderedInterval (48205739897 / 1000000000000) (48205739898 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (913893035856283 / 4000000000000) 1 (IntervalRat.scale (527 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (4121251649 / 1000000000000) (4121251658 / 1000000000000), orderedInterval (-52634394320 / 1000000000000) (-52634394312 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (571871828424649 / 4000000000000) 1 (IntervalRat.scale (527 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-46009332364 / 1000000000000) (-46009283417 / 1000000000000), orderedInterval (48493365430 / 1000000000000) (48493414376 / 1000000000000)))) (orderedInterval (-4444100170 / 1000000000000) (-4444099243 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (307554571286583 / 4000000000000) 1 (IntervalRat.scale (527 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (69395230185 / 1000000000000) (69395310119 / 1000000000000), orderedInterval (-59307308731 / 1000000000000) (-59307228796 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (835070488928749 / 4000000000000) 1 (IntervalRat.scale (527 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (44407672924 / 1000000000000) (44407752167 / 1000000000000), orderedInterval (-32929716705 / 1000000000000) (-32929637462 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1140217360260173 / 4000000000000) 1 (IntervalRat.scale (527 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (2155720107 / 1000000000000) (2155720110 / 1000000000000), orderedInterval (-47212721676 / 1000000000000) (-47212721673 / 1000000000000)))) (orderedInterval (4825755295 / 1000000000000) (4825757179 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (482128171575351 / 4000000000000) 1 (IntervalRat.scale (527 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (67885484790 / 1000000000000) (67885488704 / 1000000000000), orderedInterval (-26229127791 / 1000000000000) (-26229123877 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1959824250498071 / 4000000000000) 1 (IntervalRat.scale (527 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (21893645253 / 1000000000000) (21893645254 / 1000000000000), orderedInterval (28613457005 / 1000000000000) (28613457006 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1309071773112889 / 4000000000000) 1 (IntervalRat.scale (527 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (42804219094 / 1000000000000) (42804219099 / 1000000000000), orderedInterval (10567211192 / 1000000000000) (10567211196 / 1000000000000)))) (orderedInterval (-6865760120 / 1000000000000) (-6865760005 / 1000000000000))) = true
  rfl'

theorem compactCertificate392_chunkChecks1 :
    compactCertificate392.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate392.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate392_chunkChecks1_0
    compactCertificate392_chunkChecks1_1 compactCertificate392_chunkChecks1_2

theorem compactCertificate392_chunkChecks2_0 :
    compactCertificate392.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (527 / 2) 2 (IntervalRat.scale (527 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (18739226979 / 1000000000000) (18739226980 / 1000000000000), orderedInterval (45405158957 / 1000000000000) (45405158958 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (776371629543827 / 4000000000000) 2 (IntervalRat.scale (527 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (5655839083 / 1000000000000) (5655839085 / 1000000000000), orderedInterval (56976627561 / 1000000000000) (56976627562 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (251062633432691 / 800000000000) 2 (IntervalRat.scale (527 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (19753768049 / 1000000000000) (19753768050 / 1000000000000), orderedInterval (40445077052 / 1000000000000) (40445077053 / 1000000000000)))) (orderedInterval (-9180942955 / 1000000000000) (-9180942930 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (226543305202489 / 4000000000000) 2 (IntervalRat.scale (527 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (81057735629 / 1000000000000) (81057735630 / 1000000000000), orderedInterval (67622973310 / 1000000000000) (67622973311 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (608527183725733 / 4000000000000) 2 (IntervalRat.scale (527 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (55178185289 / 1000000000000) (55178213721 / 1000000000000), orderedInterval (-33945477040 / 1000000000000) (-33945448609 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1652269679210961 / 4000000000000) 2 (IntervalRat.scale (527 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29173345338 / 1000000000000) (-29173316701 / 1000000000000), orderedInterval (26305381237 / 1000000000000) (26305409874 / 1000000000000)))) (orderedInterval (-5712998152 / 1000000000000) (-5712992739 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1217054367451993 / 4000000000000) 2 (IntervalRat.scale (527 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-14132108264 / 1000000000000) (-14132108263 / 1000000000000), orderedInterval (-43480978417 / 1000000000000) (-43480978416 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2085443402656189 / 4000000000000) 2 (IntervalRat.scale (527 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (20913926478 / 1000000000000) (20913926479 / 1000000000000), orderedInterval (27974246988 / 1000000000000) (27974246989 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1536128171575351 / 4000000000000) 2 (IntervalRat.scale (527 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (40699218309 / 1000000000000) (40699218479 / 1000000000000), orderedInterval (1086256307 / 1000000000000) (1086256478 / 1000000000000)))) (orderedInterval (442384786 / 1000000000000) (442384842 / 1000000000000))) = true
  rfl'

theorem compactCertificate392_chunkChecks2_1 :
    compactCertificate392.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2356815648284473 / 4000000000000) 2 (IntervalRat.scale (527 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-19374041168 / 1000000000000) (-19374039828 / 1000000000000), orderedInterval (26570557026 / 1000000000000) (26570558366 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1360708148967217 / 4000000000000) 2 (IntervalRat.scale (527 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (43047123125 / 1000000000000) (43047123787 / 1000000000000), orderedInterval (-4350441271 / 1000000000000) (-4350440610 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2414600488489253 / 4000000000000) 2 (IntervalRat.scale (527 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (30813265823 / 1000000000000) (30813265835 / 1000000000000), orderedInterval (10229208707 / 1000000000000) (10229208719 / 1000000000000)))) (orderedInterval (-45487963220 / 1000000000000) (-45487961472 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2256032990084057 / 4000000000000) 2 (IntervalRat.scale (527 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-21469772748 / 1000000000000) (-21469769605 / 1000000000000), orderedInterval (25860683261 / 1000000000000) (25860686403 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1610011594160681 / 4000000000000) 2 (IntervalRat.scale (527 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (36526467721 / 1000000000000) (36526467722 / 1000000000000), orderedInterval (15685772015 / 1000000000000) (15685772017 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1825581551177199 / 4000000000000) 2 (IntervalRat.scale (527 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-37232329165 / 1000000000000) (-37232328114 / 1000000000000), orderedInterval (2980073259 / 1000000000000) (2980074310 / 1000000000000)))) (orderedInterval (-10405180007 / 1000000000000) (-10405179646 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1521979570927231 / 4000000000000) 2 (IntervalRat.scale (527 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-37289600094 / 1000000000000) (-37289600092 / 1000000000000), orderedInterval (-16762332645 / 1000000000000) (-16762332644 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1344715107923851 / 4000000000000) 2 (IntervalRat.scale (527 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-31620010805 / 1000000000000) (-31620010804 / 1000000000000), orderedInterval (-29850612198 / 1000000000000) (-29850612197 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (389750851065249 / 800000000000) 2 (IntervalRat.scale (527 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-30931267525 / 1000000000000) (-30931267524 / 1000000000000), orderedInterval (-18675950926 / 1000000000000) (-18675950925 / 1000000000000)))) (orderedInterval (655962880 / 1000000000000) (655962935 / 1000000000000))) = true
  rfl'

theorem compactCertificate392_chunkChecks2_2 :
    compactCertificate392.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1078071365510003 / 4000000000000) 2 (IntervalRat.scale (527 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (6098266125 / 1000000000000) (6098266126 / 1000000000000), orderedInterval (48205739897 / 1000000000000) (48205739898 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (913893035856283 / 4000000000000) 2 (IntervalRat.scale (527 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (4121251649 / 1000000000000) (4121251658 / 1000000000000), orderedInterval (-52634394320 / 1000000000000) (-52634394312 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (571871828424649 / 4000000000000) 2 (IntervalRat.scale (527 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-46009332364 / 1000000000000) (-46009283417 / 1000000000000), orderedInterval (48493365430 / 1000000000000) (48493414376 / 1000000000000)))) (orderedInterval (1653291512 / 1000000000000) (1653292043 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (307554571286583 / 4000000000000) 2 (IntervalRat.scale (527 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (69395230185 / 1000000000000) (69395310119 / 1000000000000), orderedInterval (-59307308731 / 1000000000000) (-59307228796 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (835070488928749 / 4000000000000) 2 (IntervalRat.scale (527 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (44407672924 / 1000000000000) (44407752167 / 1000000000000), orderedInterval (-32929716705 / 1000000000000) (-32929637462 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1140217360260173 / 4000000000000) 2 (IntervalRat.scale (527 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (2155720107 / 1000000000000) (2155720110 / 1000000000000), orderedInterval (-47212721676 / 1000000000000) (-47212721673 / 1000000000000)))) (orderedInterval (916545323 / 1000000000000) (916546613 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (482128171575351 / 4000000000000) 2 (IntervalRat.scale (527 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (67885484790 / 1000000000000) (67885488704 / 1000000000000), orderedInterval (-26229127791 / 1000000000000) (-26229123877 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1959824250498071 / 4000000000000) 2 (IntervalRat.scale (527 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (21893645253 / 1000000000000) (21893645254 / 1000000000000), orderedInterval (28613457005 / 1000000000000) (28613457006 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1309071773112889 / 4000000000000) 2 (IntervalRat.scale (527 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (42804219094 / 1000000000000) (42804219099 / 1000000000000), orderedInterval (10567211192 / 1000000000000) (10567211196 / 1000000000000)))) (orderedInterval (18490912818 / 1000000000000) (18490912976 / 1000000000000))) = true
  rfl'

theorem compactCertificate392_chunkChecks2 :
    compactCertificate392.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate392.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate392_chunkChecks2_0
    compactCertificate392_chunkChecks2_1 compactCertificate392_chunkChecks2_2

theorem compactCertificate392_chunkChecks3_0 :
    compactCertificate392.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (527 / 2) 3 (IntervalRat.scale (527 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (18739226979 / 1000000000000) (18739226980 / 1000000000000), orderedInterval (45405158957 / 1000000000000) (45405158958 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (776371629543827 / 4000000000000) 3 (IntervalRat.scale (527 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (5655839083 / 1000000000000) (5655839085 / 1000000000000), orderedInterval (56976627561 / 1000000000000) (56976627562 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (251062633432691 / 800000000000) 3 (IntervalRat.scale (527 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (19753768049 / 1000000000000) (19753768050 / 1000000000000), orderedInterval (40445077052 / 1000000000000) (40445077053 / 1000000000000)))) (orderedInterval (-22183627763 / 1000000000000) (-22183627734 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (226543305202489 / 4000000000000) 3 (IntervalRat.scale (527 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (81057735629 / 1000000000000) (81057735630 / 1000000000000), orderedInterval (67622973310 / 1000000000000) (67622973311 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (608527183725733 / 4000000000000) 3 (IntervalRat.scale (527 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (55178185289 / 1000000000000) (55178213721 / 1000000000000), orderedInterval (-33945477040 / 1000000000000) (-33945448609 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1652269679210961 / 4000000000000) 3 (IntervalRat.scale (527 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29173345338 / 1000000000000) (-29173316701 / 1000000000000), orderedInterval (26305381237 / 1000000000000) (26305409874 / 1000000000000)))) (orderedInterval (7471405299 / 1000000000000) (7471413437 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1217054367451993 / 4000000000000) 3 (IntervalRat.scale (527 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-14132108264 / 1000000000000) (-14132108263 / 1000000000000), orderedInterval (-43480978417 / 1000000000000) (-43480978416 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2085443402656189 / 4000000000000) 3 (IntervalRat.scale (527 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (20913926478 / 1000000000000) (20913926479 / 1000000000000), orderedInterval (27974246988 / 1000000000000) (27974246989 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1536128171575351 / 4000000000000) 3 (IntervalRat.scale (527 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (40699218309 / 1000000000000) (40699218479 / 1000000000000), orderedInterval (1086256307 / 1000000000000) (1086256478 / 1000000000000)))) (orderedInterval (6600504042 / 1000000000000) (6600504139 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate392_chunkChecks3_1 :
    compactCertificate392.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2356815648284473 / 4000000000000) 3 (IntervalRat.scale (527 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-19374041168 / 1000000000000) (-19374039828 / 1000000000000), orderedInterval (26570557026 / 1000000000000) (26570558366 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1360708148967217 / 4000000000000) 3 (IntervalRat.scale (527 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (43047123125 / 1000000000000) (43047123787 / 1000000000000), orderedInterval (-4350441271 / 1000000000000) (-4350440610 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2414600488489253 / 4000000000000) 3 (IntervalRat.scale (527 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (30813265823 / 1000000000000) (30813265835 / 1000000000000), orderedInterval (10229208707 / 1000000000000) (10229208719 / 1000000000000)))) (orderedInterval (36168238684 / 1000000000000) (36168242493 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2256032990084057 / 4000000000000) 3 (IntervalRat.scale (527 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-21469772748 / 1000000000000) (-21469769605 / 1000000000000), orderedInterval (25860683261 / 1000000000000) (25860686403 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1610011594160681 / 4000000000000) 3 (IntervalRat.scale (527 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (36526467721 / 1000000000000) (36526467722 / 1000000000000), orderedInterval (15685772015 / 1000000000000) (15685772017 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1825581551177199 / 4000000000000) 3 (IntervalRat.scale (527 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-37232329165 / 1000000000000) (-37232328114 / 1000000000000), orderedInterval (2980073259 / 1000000000000) (2980074310 / 1000000000000)))) (orderedInterval (-590598954 / 1000000000000) (-590598225 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1521979570927231 / 4000000000000) 3 (IntervalRat.scale (527 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-37289600094 / 1000000000000) (-37289600092 / 1000000000000), orderedInterval (-16762332645 / 1000000000000) (-16762332644 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1344715107923851 / 4000000000000) 3 (IntervalRat.scale (527 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-31620010805 / 1000000000000) (-31620010804 / 1000000000000), orderedInterval (-29850612198 / 1000000000000) (-29850612197 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (389750851065249 / 800000000000) 3 (IntervalRat.scale (527 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-30931267525 / 1000000000000) (-30931267524 / 1000000000000), orderedInterval (-18675950926 / 1000000000000) (-18675950925 / 1000000000000)))) (orderedInterval (55167595 / 1000000000000) (55167679 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate392_chunkChecks3_2 :
    compactCertificate392.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1078071365510003 / 4000000000000) 3 (IntervalRat.scale (527 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (6098266125 / 1000000000000) (6098266126 / 1000000000000), orderedInterval (48205739897 / 1000000000000) (48205739898 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (913893035856283 / 4000000000000) 3 (IntervalRat.scale (527 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (4121251649 / 1000000000000) (4121251658 / 1000000000000), orderedInterval (-52634394320 / 1000000000000) (-52634394312 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (571871828424649 / 4000000000000) 3 (IntervalRat.scale (527 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-46009332364 / 1000000000000) (-46009283417 / 1000000000000), orderedInterval (48493365430 / 1000000000000) (48493414376 / 1000000000000)))) (orderedInterval (6047472926 / 1000000000000) (6047473240 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (307554571286583 / 4000000000000) 3 (IntervalRat.scale (527 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (69395230185 / 1000000000000) (69395310119 / 1000000000000), orderedInterval (-59307308731 / 1000000000000) (-59307228796 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (835070488928749 / 4000000000000) 3 (IntervalRat.scale (527 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (44407672924 / 1000000000000) (44407752167 / 1000000000000), orderedInterval (-32929716705 / 1000000000000) (-32929637462 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1140217360260173 / 4000000000000) 3 (IntervalRat.scale (527 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (2155720107 / 1000000000000) (2155720110 / 1000000000000), orderedInterval (-47212721676 / 1000000000000) (-47212721673 / 1000000000000)))) (orderedInterval (-4983044645 / 1000000000000) (-4983043680 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (482128171575351 / 4000000000000) 3 (IntervalRat.scale (527 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (67885484790 / 1000000000000) (67885488704 / 1000000000000), orderedInterval (-26229127791 / 1000000000000) (-26229123877 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1959824250498071 / 4000000000000) 3 (IntervalRat.scale (527 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (21893645253 / 1000000000000) (21893645254 / 1000000000000), orderedInterval (28613457005 / 1000000000000) (28613457006 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1309071773112889 / 4000000000000) 3 (IntervalRat.scale (527 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (42804219094 / 1000000000000) (42804219099 / 1000000000000), orderedInterval (10567211192 / 1000000000000) (10567211196 / 1000000000000)))) (orderedInterval (18717316974 / 1000000000000) (18717317212 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate392_chunkChecks3 :
    compactCertificate392.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate392.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate392_chunkChecks3_0
    compactCertificate392_chunkChecks3_1 compactCertificate392_chunkChecks3_2

theorem compactCertificate392_chunkChecks4_0 :
    compactCertificate392.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (527 / 2) 4 (IntervalRat.scale (527 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (18739226979 / 1000000000000) (18739226980 / 1000000000000), orderedInterval (45405158957 / 1000000000000) (45405158958 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (776371629543827 / 4000000000000) 4 (IntervalRat.scale (527 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (5655839083 / 1000000000000) (5655839085 / 1000000000000), orderedInterval (56976627561 / 1000000000000) (56976627562 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (251062633432691 / 800000000000) 4 (IntervalRat.scale (527 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (19753768049 / 1000000000000) (19753768050 / 1000000000000), orderedInterval (40445077052 / 1000000000000) (40445077053 / 1000000000000)))) (orderedInterval (9943684941 / 1000000000000) (9943684975 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (226543305202489 / 4000000000000) 4 (IntervalRat.scale (527 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (81057735629 / 1000000000000) (81057735630 / 1000000000000), orderedInterval (67622973310 / 1000000000000) (67622973311 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (608527183725733 / 4000000000000) 4 (IntervalRat.scale (527 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (55178185289 / 1000000000000) (55178213721 / 1000000000000), orderedInterval (-33945477040 / 1000000000000) (-33945448609 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1652269679210961 / 4000000000000) 4 (IntervalRat.scale (527 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29173345338 / 1000000000000) (-29173316701 / 1000000000000), orderedInterval (26305381237 / 1000000000000) (26305409874 / 1000000000000)))) (orderedInterval (12689480876 / 1000000000000) (12689493461 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1217054367451993 / 4000000000000) 4 (IntervalRat.scale (527 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-14132108264 / 1000000000000) (-14132108263 / 1000000000000), orderedInterval (-43480978417 / 1000000000000) (-43480978416 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2085443402656189 / 4000000000000) 4 (IntervalRat.scale (527 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (20913926478 / 1000000000000) (20913926479 / 1000000000000), orderedInterval (27974246988 / 1000000000000) (27974246989 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1536128171575351 / 4000000000000) 4 (IntervalRat.scale (527 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (40699218309 / 1000000000000) (40699218479 / 1000000000000), orderedInterval (1086256307 / 1000000000000) (1086256478 / 1000000000000)))) (orderedInterval (-5498605659 / 1000000000000) (-5498605486 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate392_chunkChecks4_1 :
    compactCertificate392.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2356815648284473 / 4000000000000) 4 (IntervalRat.scale (527 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-19374041168 / 1000000000000) (-19374039828 / 1000000000000), orderedInterval (26570557026 / 1000000000000) (26570558366 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1360708148967217 / 4000000000000) 4 (IntervalRat.scale (527 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (43047123125 / 1000000000000) (43047123787 / 1000000000000), orderedInterval (-4350441271 / 1000000000000) (-4350440610 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2414600488489253 / 4000000000000) 4 (IntervalRat.scale (527 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (30813265823 / 1000000000000) (30813265835 / 1000000000000), orderedInterval (10229208707 / 1000000000000) (10229208719 / 1000000000000)))) (orderedInterval (215296017809 / 1000000000000) (215296026223 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2256032990084057 / 4000000000000) 4 (IntervalRat.scale (527 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-21469772748 / 1000000000000) (-21469769605 / 1000000000000), orderedInterval (25860683261 / 1000000000000) (25860686403 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1610011594160681 / 4000000000000) 4 (IntervalRat.scale (527 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (36526467721 / 1000000000000) (36526467722 / 1000000000000), orderedInterval (15685772015 / 1000000000000) (15685772017 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1825581551177199 / 4000000000000) 4 (IntervalRat.scale (527 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-37232329165 / 1000000000000) (-37232328114 / 1000000000000), orderedInterval (2980073259 / 1000000000000) (2980074310 / 1000000000000)))) (orderedInterval (28641216356 / 1000000000000) (28641217849 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1521979570927231 / 4000000000000) 4 (IntervalRat.scale (527 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-37289600094 / 1000000000000) (-37289600092 / 1000000000000), orderedInterval (-16762332645 / 1000000000000) (-16762332644 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1344715107923851 / 4000000000000) 4 (IntervalRat.scale (527 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-31620010805 / 1000000000000) (-31620010804 / 1000000000000), orderedInterval (-29850612198 / 1000000000000) (-29850612197 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (389750851065249 / 800000000000) 4 (IntervalRat.scale (527 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-30931267525 / 1000000000000) (-30931267524 / 1000000000000), orderedInterval (-18675950926 / 1000000000000) (-18675950925 / 1000000000000)))) (orderedInterval (-6333261794 / 1000000000000) (-6333261661 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate392_chunkChecks4_2 :
    compactCertificate392.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1078071365510003 / 4000000000000) 4 (IntervalRat.scale (527 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (6098266125 / 1000000000000) (6098266126 / 1000000000000), orderedInterval (48205739897 / 1000000000000) (48205739898 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (913893035856283 / 4000000000000) 4 (IntervalRat.scale (527 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (4121251649 / 1000000000000) (4121251658 / 1000000000000), orderedInterval (-52634394320 / 1000000000000) (-52634394312 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (571871828424649 / 4000000000000) 4 (IntervalRat.scale (527 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-46009332364 / 1000000000000) (-46009283417 / 1000000000000), orderedInterval (48493365430 / 1000000000000) (48493414376 / 1000000000000)))) (orderedInterval (-1374769271 / 1000000000000) (-1374769074 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (307554571286583 / 4000000000000) 4 (IntervalRat.scale (527 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (69395230185 / 1000000000000) (69395310119 / 1000000000000), orderedInterval (-59307308731 / 1000000000000) (-59307228796 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (835070488928749 / 4000000000000) 4 (IntervalRat.scale (527 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (44407672924 / 1000000000000) (44407752167 / 1000000000000), orderedInterval (-32929716705 / 1000000000000) (-32929637462 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1140217360260173 / 4000000000000) 4 (IntervalRat.scale (527 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (2155720107 / 1000000000000) (2155720110 / 1000000000000), orderedInterval (-47212721676 / 1000000000000) (-47212721673 / 1000000000000)))) (orderedInterval (-594701486 / 1000000000000) (-594700729 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (482128171575351 / 4000000000000) 4 (IntervalRat.scale (527 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (67885484790 / 1000000000000) (67885488704 / 1000000000000), orderedInterval (-26229127791 / 1000000000000) (-26229123877 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1959824250498071 / 4000000000000) 4 (IntervalRat.scale (527 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (21893645253 / 1000000000000) (21893645254 / 1000000000000), orderedInterval (28613457005 / 1000000000000) (28613457006 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1309071773112889 / 4000000000000) 4 (IntervalRat.scale (527 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (42804219094 / 1000000000000) (42804219099 / 1000000000000), orderedInterval (10567211192 / 1000000000000) (10567211196 / 1000000000000)))) (orderedInterval (-40538237245 / 1000000000000) (-40538236865 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate392_chunkChecks4 :
    compactCertificate392.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate392.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate392_chunkChecks4_0
    compactCertificate392_chunkChecks4_1 compactCertificate392_chunkChecks4_2

theorem compactCertificate392_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate392.chunkCheck r b = true :=
  compactCertificate392.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate392_chunkChecks0
    · exact compactCertificate392_chunkChecks1
    · exact compactCertificate392_chunkChecks2
    · exact compactCertificate392_chunkChecks3
    · exact compactCertificate392_chunkChecks4)

theorem compactCertificate392_coefficient0 :
    compactCertificate392.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate392_coefficient1 :
    compactCertificate392.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate392_coefficient2 :
    compactCertificate392.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate392_coefficient3 :
    compactCertificate392.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate392_coefficient4 :
    compactCertificate392.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate392_coefficients : ∀ r : Fin 5,
    compactCertificate392.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate392_coefficient0
  · exact compactCertificate392_coefficient1
  · exact compactCertificate392_coefficient2
  · exact compactCertificate392_coefficient3
  · exact compactCertificate392_coefficient4

theorem compactCertificate392_lower : (1 : ℚ) ≤ compactCertificate392.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate392, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate392_proves {t : ℝ} (ht : t ∈ compactCertificate392.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate392.proves compactCertificate392_states compactCertificate392_chunks
    compactCertificate392_coefficients compactCertificate392_lower ht

end Erdos232
