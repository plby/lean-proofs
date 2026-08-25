/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate334 : CompactCertificate where
  left := 206
  right := 207
  center := 413 / 2
  grid := fun i =>
    match i.val with
    | 0 => 66
    | 1 => 48
    | 2 => 78
    | 3 => 14
    | 4 => 38
    | 5 => 103
    | 6 => 76
    | 7 => 130
    | 8 => 96
    | 9 => 147
    | 10 => 85
    | 11 => 151
    | 12 => 141
    | 13 => 100
    | 14 => 114
    | 15 => 95
    | 16 => 84
    | 17 => 122
    | 18 => 67
    | 19 => 57
    | 20 => 36
    | 21 => 19
    | 22 => 52
    | 23 => 71
    | 24 => 30
    | 25 => 122
    | _ => 82
  point := fun i =>
    match i.val with
    | 0 => 413 / 2
    | 1 => 608427861483113 / 4000000000000
    | 2 => 196753069464329 / 800000000000
    | 3 => 177537732540091 / 4000000000000
    | 4 => 476891322350527 / 4000000000000
    | 5 => 1294852708755459 / 4000000000000
    | 6 => 953782644701467 / 4000000000000
    | 7 => 1634322818400391 / 4000000000000
    | 8 => 1203834791006869 / 4000000000000
    | 9 => 1846992149414587 / 4000000000000
    | 10 => 1066361414655523 / 4000000000000
    | 11 => 1892277043161407 / 4000000000000
    | 12 => 1768010673443483 / 4000000000000
    | 13 => 1261735841344139 / 4000000000000
    | 14 => 1430673967051581 / 4000000000000
    | 15 => 1192746798468589 / 4000000000000
    | 16 => 1053827968828369 / 4000000000000
    | 17 => 305440420284531 / 800000000000
    | 18 => 844864276955657 / 4000000000000
    | 19 => 716200804190977 / 4000000000000
    | 20 => 448165208993131 / 4000000000000
    | 21 => 241024739926677 / 4000000000000
    | 22 => 654429054891031 / 4000000000000
    | 23 => 893566925592887 / 4000000000000
    | 24 => 377834791006869 / 4000000000000
    | 25 => 1535877448682549 / 4000000000000
    | _ => 1025894956917691 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-3347293728 / 1000000000000) (-3347293721 / 1000000000000), orderedInterval (55431105980 / 1000000000000) (55431105988 / 1000000000000))
    | 1 => (orderedInterval (56004045110 / 1000000000000) (56004067685 / 1000000000000), orderedInterval (-32570473721 / 1000000000000) (-32570451146 / 1000000000000))
    | 2 => (orderedInterval (50563020086 / 1000000000000) (50563020510 / 1000000000000), orderedInterval (-5748880842 / 1000000000000) (-5748880418 / 1000000000000))
    | 3 => (orderedInterval (110944629965 / 1000000000000) (110944629966 / 1000000000000), orderedInterval (43849674390 / 1000000000000) (43849674391 / 1000000000000))
    | 4 => (orderedInterval (42853243059 / 1000000000000) (42853243060 / 1000000000000), orderedInterval (59009483972 / 1000000000000) (59009483973 / 1000000000000))
    | 5 => (orderedInterval (-35124288389 / 1000000000000) (-35124288388 / 1000000000000), orderedInterval (-27017884312 / 1000000000000) (-27017884311 / 1000000000000))
    | 6 => (orderedInterval (23377640664 / 1000000000000) (23377640665 / 1000000000000), orderedInterval (46030942091 / 1000000000000) (46030942092 / 1000000000000))
    | 7 => (orderedInterval (32307729848 / 1000000000000) (32307729849 / 1000000000000), orderedInterval (22639420790 / 1000000000000) (22639420791 / 1000000000000))
    | 8 => (orderedInterval (6908756577 / 1000000000000) (6908756578 / 1000000000000), orderedInterval (45459149784 / 1000000000000) (45459149785 / 1000000000000))
    | 9 => (orderedInterval (-24456977197 / 1000000000000) (-24456977196 / 1000000000000), orderedInterval (-27912256492 / 1000000000000) (-27912256491 / 1000000000000))
    | 10 => (orderedInterval (-16292314228 / 1000000000000) (-16292314227 / 1000000000000), orderedInterval (-46040815024 / 1000000000000) (-46040815023 / 1000000000000))
    | 11 => (orderedInterval (18421314154 / 1000000000000) (18421314936 / 1000000000000), orderedInterval (-31742926519 / 1000000000000) (-31742925737 / 1000000000000))
    | 12 => (orderedInterval (6674170044 / 1000000000000) (6674170051 / 1000000000000), orderedInterval (-37367472969 / 1000000000000) (-37367472962 / 1000000000000))
    | 13 => (orderedInterval (39661777281 / 1000000000000) (39661812094 / 1000000000000), orderedInterval (-21162063175 / 1000000000000) (-21162028362 / 1000000000000))
    | 14 => (orderedInterval (12949571207 / 1000000000000) (12949571208 / 1000000000000), orderedInterval (40134428216 / 1000000000000) (40134428217 / 1000000000000))
    | 15 => (orderedInterval (-22973793189 / 1000000000000) (-22973793188 / 1000000000000), orderedInterval (-40051086329 / 1000000000000) (-40051086328 / 1000000000000))
    | 16 => (orderedInterval (16769564950 / 1000000000000) (16769564951 / 1000000000000), orderedInterval (46176330823 / 1000000000000) (46176330824 / 1000000000000))
    | 17 => (orderedInterval (-25951621700 / 1000000000000) (-25951613789 / 1000000000000), orderedInterval (31560611903 / 1000000000000) (31560619814 / 1000000000000))
    | 18 => (orderedInterval (-54812455389 / 1000000000000) (-54812455357 / 1000000000000), orderedInterval (-2977525328 / 1000000000000) (-2977525296 / 1000000000000))
    | 19 => (orderedInterval (-41256869150 / 1000000000000) (-41256869149 / 1000000000000), orderedInterval (-42936030012 / 1000000000000) (-42936030011 / 1000000000000))
    | 20 => (orderedInterval (-20233033483 / 1000000000000) (-20233033166 / 1000000000000), orderedInterval (72703530191 / 1000000000000) (72703530507 / 1000000000000))
    | 21 => (orderedInterval (-100273250774 / 1000000000000) (-100273250773 / 1000000000000), orderedInterval (-21754841323 / 1000000000000) (-21754841322 / 1000000000000))
    | 22 => (orderedInterval (53447802524 / 1000000000000) (53447802525 / 1000000000000), orderedInterval (31999837984 / 1000000000000) (31999837985 / 1000000000000))
    | 23 => (orderedInterval (-48131308593 / 1000000000000) (-48131308592 / 1000000000000), orderedInterval (-22982611714 / 1000000000000) (-22982611713 / 1000000000000))
    | 24 => (orderedInterval (68857501555 / 1000000000000) (68857501556 / 1000000000000), orderedInterval (44337526203 / 1000000000000) (44337526204 / 1000000000000))
    | 25 => (orderedInterval (40551240839 / 1000000000000) (40551240910 / 1000000000000), orderedInterval (3633894660 / 1000000000000) (3633894731 / 1000000000000))
    | _ => (orderedInterval (-17174854585 / 1000000000000) (-17174854236 / 1000000000000), orderedInterval (46801318888 / 1000000000000) (46801319237 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (2162194650 / 1000000000000) (2162194904 / 1000000000000)
      | 1 => orderedInterval (2857949190 / 1000000000000) (2857949215 / 1000000000000)
      | 2 => orderedInterval (-829528642 / 1000000000000) (-829528630 / 1000000000000)
      | 3 => orderedInterval (5757281444 / 1000000000000) (5757281637 / 1000000000000)
      | 4 => orderedInterval (3564509663 / 1000000000000) (3564512980 / 1000000000000)
      | 5 => orderedInterval (-1889424294 / 1000000000000) (-1889424071 / 1000000000000)
      | 6 => orderedInterval (10440542403 / 1000000000000) (10440542471 / 1000000000000)
      | 7 => orderedInterval (4327723477 / 1000000000000) (4327723502 / 1000000000000)
      | _ => orderedInterval (336610758 / 1000000000000) (336610887 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (21345613259 / 1000000000000) (21345613464 / 1000000000000)
      | 1 => orderedInterval (4152581720 / 1000000000000) (4152581749 / 1000000000000)
      | 2 => orderedInterval (219577320 / 1000000000000) (219577341 / 1000000000000)
      | 3 => orderedInterval (-3651261003 / 1000000000000) (-3651260578 / 1000000000000)
      | 4 => orderedInterval (-1964642417 / 1000000000000) (-1964637348 / 1000000000000)
      | 5 => orderedInterval (-2545163414 / 1000000000000) (-2545163010 / 1000000000000)
      | 6 => orderedInterval (3878300066 / 1000000000000) (3878300125 / 1000000000000)
      | 7 => orderedInterval (1447476460 / 1000000000000) (1447476483 / 1000000000000)
      | _ => orderedInterval (-11334007112 / 1000000000000) (-11334006939 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-3268523080 / 1000000000000) (-3268522907 / 1000000000000)
      | 1 => orderedInterval (-6622180622 / 1000000000000) (-6622180582 / 1000000000000)
      | 2 => orderedInterval (3545425421 / 1000000000000) (3545425458 / 1000000000000)
      | 3 => orderedInterval (-33442409580 / 1000000000000) (-33442408630 / 1000000000000)
      | 4 => orderedInterval (-7993112090 / 1000000000000) (-7993104317 / 1000000000000)
      | 5 => orderedInterval (4399024182 / 1000000000000) (4399024920 / 1000000000000)
      | 6 => orderedInterval (-10749436271 / 1000000000000) (-10749436216 / 1000000000000)
      | 7 => orderedInterval (-3720402059 / 1000000000000) (-3720402036 / 1000000000000)
      | _ => orderedInterval (6409924935 / 1000000000000) (6409925175 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-21263404916 / 1000000000000) (-21263404764 / 1000000000000)
      | 1 => orderedInterval (-7776846749 / 1000000000000) (-7776846689 / 1000000000000)
      | 2 => orderedInterval (1990613243 / 1000000000000) (1990613309 / 1000000000000)
      | 3 => orderedInterval (6304147065 / 1000000000000) (6304149203 / 1000000000000)
      | 4 => orderedInterval (1611084359 / 1000000000000) (1611096243 / 1000000000000)
      | 5 => orderedInterval (1751428918 / 1000000000000) (1751430267 / 1000000000000)
      | 6 => orderedInterval (-2419529972 / 1000000000000) (-2419529920 / 1000000000000)
      | 7 => orderedInterval (-1860799639 / 1000000000000) (-1860799616 / 1000000000000)
      | _ => orderedInterval (18668459200 / 1000000000000) (18668459547 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (5002779298 / 1000000000000) (5002779440 / 1000000000000)
      | 1 => orderedInterval (15325535848 / 1000000000000) (15325535939 / 1000000000000)
      | 2 => orderedInterval (-14538297842 / 1000000000000) (-14538297720 / 1000000000000)
      | 3 => orderedInterval (177355814055 / 1000000000000) (177355818904 / 1000000000000)
      | 4 => orderedInterval (17284865720 / 1000000000000) (17284883954 / 1000000000000)
      | 5 => orderedInterval (-11477844605 / 1000000000000) (-11477842120 / 1000000000000)
      | 6 => orderedInterval (10878533753 / 1000000000000) (10878533804 / 1000000000000)
      | 7 => orderedInterval (4605589512 / 1000000000000) (4605589537 / 1000000000000)
      | _ => orderedInterval (-31953364311 / 1000000000000) (-31953363791 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (26727858649 / 1000000000000) (26727862895 / 1000000000000)
    | 1 => orderedInterval (11548474879 / 1000000000000) (11548481287 / 1000000000000)
    | 2 => orderedInterval (-51441689164 / 1000000000000) (-51441679135 / 1000000000000)
    | 3 => orderedInterval (-2994848491 / 1000000000000) (-2994832420 / 1000000000000)
    | _ => orderedInterval (172483611428 / 1000000000000) (172483637947 / 1000000000000)

theorem compactCertificate334_stateChecks0 :
    compactCertificate334.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (413 / 2)) (orderedInterval (-3347293728 / 1000000000000) (-3347293721 / 1000000000000), orderedInterval (55431105980 / 1000000000000) (55431105988 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 48 12 (608427861483113 / 4000000000000)) (orderedInterval (56004045110 / 1000000000000) (56004067685 / 1000000000000), orderedInterval (-32570473721 / 1000000000000) (-32570451146 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 78 12 (196753069464329 / 800000000000)) (orderedInterval (50563020086 / 1000000000000) (50563020510 / 1000000000000), orderedInterval (-5748880842 / 1000000000000) (-5748880418 / 1000000000000))) = true
  rfl'

theorem compactCertificate334_stateChecks1 :
    compactCertificate334.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 14 12 (177537732540091 / 4000000000000)) (orderedInterval (110944629965 / 1000000000000) (110944629966 / 1000000000000), orderedInterval (43849674390 / 1000000000000) (43849674391 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (476891322350527 / 4000000000000)) (orderedInterval (42853243059 / 1000000000000) (42853243060 / 1000000000000), orderedInterval (59009483972 / 1000000000000) (59009483973 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 103 12 (1294852708755459 / 4000000000000)) (orderedInterval (-35124288389 / 1000000000000) (-35124288388 / 1000000000000), orderedInterval (-27017884312 / 1000000000000) (-27017884311 / 1000000000000))) = true
  rfl'

theorem compactCertificate334_stateChecks2 :
    compactCertificate334.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 76 12 (953782644701467 / 4000000000000)) (orderedInterval (23377640664 / 1000000000000) (23377640665 / 1000000000000), orderedInterval (46030942091 / 1000000000000) (46030942092 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 130 12 (1634322818400391 / 4000000000000)) (orderedInterval (32307729848 / 1000000000000) (32307729849 / 1000000000000), orderedInterval (22639420790 / 1000000000000) (22639420791 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 96 12 (1203834791006869 / 4000000000000)) (orderedInterval (6908756577 / 1000000000000) (6908756578 / 1000000000000), orderedInterval (45459149784 / 1000000000000) (45459149785 / 1000000000000))) = true
  rfl'

theorem compactCertificate334_stateChecks3 :
    compactCertificate334.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 147 12 (1846992149414587 / 4000000000000)) (orderedInterval (-24456977197 / 1000000000000) (-24456977196 / 1000000000000), orderedInterval (-27912256492 / 1000000000000) (-27912256491 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 85 12 (1066361414655523 / 4000000000000)) (orderedInterval (-16292314228 / 1000000000000) (-16292314227 / 1000000000000), orderedInterval (-46040815024 / 1000000000000) (-46040815023 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 151 12 (1892277043161407 / 4000000000000)) (orderedInterval (18421314154 / 1000000000000) (18421314936 / 1000000000000), orderedInterval (-31742926519 / 1000000000000) (-31742925737 / 1000000000000))) = true
  rfl'

theorem compactCertificate334_stateChecks4 :
    compactCertificate334.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 141 12 (1768010673443483 / 4000000000000)) (orderedInterval (6674170044 / 1000000000000) (6674170051 / 1000000000000), orderedInterval (-37367472969 / 1000000000000) (-37367472962 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 100 12 (1261735841344139 / 4000000000000)) (orderedInterval (39661777281 / 1000000000000) (39661812094 / 1000000000000), orderedInterval (-21162063175 / 1000000000000) (-21162028362 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 114 12 (1430673967051581 / 4000000000000)) (orderedInterval (12949571207 / 1000000000000) (12949571208 / 1000000000000), orderedInterval (40134428216 / 1000000000000) (40134428217 / 1000000000000))) = true
  rfl'

theorem compactCertificate334_stateChecks5 :
    compactCertificate334.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 95 12 (1192746798468589 / 4000000000000)) (orderedInterval (-22973793189 / 1000000000000) (-22973793188 / 1000000000000), orderedInterval (-40051086329 / 1000000000000) (-40051086328 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 84 12 (1053827968828369 / 4000000000000)) (orderedInterval (16769564950 / 1000000000000) (16769564951 / 1000000000000), orderedInterval (46176330823 / 1000000000000) (46176330824 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 122 12 (305440420284531 / 800000000000)) (orderedInterval (-25951621700 / 1000000000000) (-25951613789 / 1000000000000), orderedInterval (31560611903 / 1000000000000) (31560619814 / 1000000000000))) = true
  rfl'

theorem compactCertificate334_stateChecks6 :
    compactCertificate334.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (844864276955657 / 4000000000000)) (orderedInterval (-54812455389 / 1000000000000) (-54812455357 / 1000000000000), orderedInterval (-2977525328 / 1000000000000) (-2977525296 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 57 12 (716200804190977 / 4000000000000)) (orderedInterval (-41256869150 / 1000000000000) (-41256869149 / 1000000000000), orderedInterval (-42936030012 / 1000000000000) (-42936030011 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 36 12 (448165208993131 / 4000000000000)) (orderedInterval (-20233033483 / 1000000000000) (-20233033166 / 1000000000000), orderedInterval (72703530191 / 1000000000000) (72703530507 / 1000000000000))) = true
  rfl'

theorem compactCertificate334_stateChecks7 :
    compactCertificate334.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 19 12 (241024739926677 / 4000000000000)) (orderedInterval (-100273250774 / 1000000000000) (-100273250773 / 1000000000000), orderedInterval (-21754841323 / 1000000000000) (-21754841322 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 52 12 (654429054891031 / 4000000000000)) (orderedInterval (53447802524 / 1000000000000) (53447802525 / 1000000000000), orderedInterval (31999837984 / 1000000000000) (31999837985 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (893566925592887 / 4000000000000)) (orderedInterval (-48131308593 / 1000000000000) (-48131308592 / 1000000000000), orderedInterval (-22982611714 / 1000000000000) (-22982611713 / 1000000000000))) = true
  rfl'

theorem compactCertificate334_stateChecks8 :
    compactCertificate334.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (377834791006869 / 4000000000000)) (orderedInterval (68857501555 / 1000000000000) (68857501556 / 1000000000000), orderedInterval (44337526203 / 1000000000000) (44337526204 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 122 12 (1535877448682549 / 4000000000000)) (orderedInterval (40551240839 / 1000000000000) (40551240910 / 1000000000000), orderedInterval (3633894660 / 1000000000000) (3633894731 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 82 12 (1025894956917691 / 4000000000000)) (orderedInterval (-17174854585 / 1000000000000) (-17174854236 / 1000000000000), orderedInterval (46801318888 / 1000000000000) (46801319237 / 1000000000000))) = true
  rfl'

theorem compactCertificate334_states : ∀ j,
    BesselStateValid (compactCertificate334.point j) (compactCertificate334.state j) :=
  compactCertificate334.statesValid_of_checks3 compactCertificate334_stateChecks0
    compactCertificate334_stateChecks1 compactCertificate334_stateChecks2
    compactCertificate334_stateChecks3 compactCertificate334_stateChecks4
    compactCertificate334_stateChecks5 compactCertificate334_stateChecks6
    compactCertificate334_stateChecks7 compactCertificate334_stateChecks8

theorem compactCertificate334_chunkChecks0_0 :
    compactCertificate334.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (413 / 2) 0 (IntervalRat.scale (413 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-3347293728 / 1000000000000) (-3347293721 / 1000000000000), orderedInterval (55431105980 / 1000000000000) (55431105988 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (608427861483113 / 4000000000000) 0 (IntervalRat.scale (413 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (56004045110 / 1000000000000) (56004067685 / 1000000000000), orderedInterval (-32570473721 / 1000000000000) (-32570451146 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (196753069464329 / 800000000000) 0 (IntervalRat.scale (413 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (50563020086 / 1000000000000) (50563020510 / 1000000000000), orderedInterval (-5748880842 / 1000000000000) (-5748880418 / 1000000000000)))) (orderedInterval (2162194650 / 1000000000000) (2162194904 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (177537732540091 / 4000000000000) 0 (IntervalRat.scale (413 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (110944629965 / 1000000000000) (110944629966 / 1000000000000), orderedInterval (43849674390 / 1000000000000) (43849674391 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (476891322350527 / 4000000000000) 0 (IntervalRat.scale (413 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (42853243059 / 1000000000000) (42853243060 / 1000000000000), orderedInterval (59009483972 / 1000000000000) (59009483973 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1294852708755459 / 4000000000000) 0 (IntervalRat.scale (413 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-35124288389 / 1000000000000) (-35124288388 / 1000000000000), orderedInterval (-27017884312 / 1000000000000) (-27017884311 / 1000000000000)))) (orderedInterval (2857949190 / 1000000000000) (2857949215 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (953782644701467 / 4000000000000) 0 (IntervalRat.scale (413 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (23377640664 / 1000000000000) (23377640665 / 1000000000000), orderedInterval (46030942091 / 1000000000000) (46030942092 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1634322818400391 / 4000000000000) 0 (IntervalRat.scale (413 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (32307729848 / 1000000000000) (32307729849 / 1000000000000), orderedInterval (22639420790 / 1000000000000) (22639420791 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1203834791006869 / 4000000000000) 0 (IntervalRat.scale (413 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (6908756577 / 1000000000000) (6908756578 / 1000000000000), orderedInterval (45459149784 / 1000000000000) (45459149785 / 1000000000000)))) (orderedInterval (-829528642 / 1000000000000) (-829528630 / 1000000000000))) = true
  rfl'

theorem compactCertificate334_chunkChecks0_1 :
    compactCertificate334.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1846992149414587 / 4000000000000) 0 (IntervalRat.scale (413 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-24456977197 / 1000000000000) (-24456977196 / 1000000000000), orderedInterval (-27912256492 / 1000000000000) (-27912256491 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1066361414655523 / 4000000000000) 0 (IntervalRat.scale (413 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-16292314228 / 1000000000000) (-16292314227 / 1000000000000), orderedInterval (-46040815024 / 1000000000000) (-46040815023 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1892277043161407 / 4000000000000) 0 (IntervalRat.scale (413 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (18421314154 / 1000000000000) (18421314936 / 1000000000000), orderedInterval (-31742926519 / 1000000000000) (-31742925737 / 1000000000000)))) (orderedInterval (5757281444 / 1000000000000) (5757281637 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1768010673443483 / 4000000000000) 0 (IntervalRat.scale (413 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (6674170044 / 1000000000000) (6674170051 / 1000000000000), orderedInterval (-37367472969 / 1000000000000) (-37367472962 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1261735841344139 / 4000000000000) 0 (IntervalRat.scale (413 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (39661777281 / 1000000000000) (39661812094 / 1000000000000), orderedInterval (-21162063175 / 1000000000000) (-21162028362 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1430673967051581 / 4000000000000) 0 (IntervalRat.scale (413 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (12949571207 / 1000000000000) (12949571208 / 1000000000000), orderedInterval (40134428216 / 1000000000000) (40134428217 / 1000000000000)))) (orderedInterval (3564509663 / 1000000000000) (3564512980 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1192746798468589 / 4000000000000) 0 (IntervalRat.scale (413 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-22973793189 / 1000000000000) (-22973793188 / 1000000000000), orderedInterval (-40051086329 / 1000000000000) (-40051086328 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1053827968828369 / 4000000000000) 0 (IntervalRat.scale (413 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (16769564950 / 1000000000000) (16769564951 / 1000000000000), orderedInterval (46176330823 / 1000000000000) (46176330824 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (305440420284531 / 800000000000) 0 (IntervalRat.scale (413 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-25951621700 / 1000000000000) (-25951613789 / 1000000000000), orderedInterval (31560611903 / 1000000000000) (31560619814 / 1000000000000)))) (orderedInterval (-1889424294 / 1000000000000) (-1889424071 / 1000000000000))) = true
  rfl'

theorem compactCertificate334_chunkChecks0_2 :
    compactCertificate334.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (844864276955657 / 4000000000000) 0 (IntervalRat.scale (413 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-54812455389 / 1000000000000) (-54812455357 / 1000000000000), orderedInterval (-2977525328 / 1000000000000) (-2977525296 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (716200804190977 / 4000000000000) 0 (IntervalRat.scale (413 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-41256869150 / 1000000000000) (-41256869149 / 1000000000000), orderedInterval (-42936030012 / 1000000000000) (-42936030011 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (448165208993131 / 4000000000000) 0 (IntervalRat.scale (413 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-20233033483 / 1000000000000) (-20233033166 / 1000000000000), orderedInterval (72703530191 / 1000000000000) (72703530507 / 1000000000000)))) (orderedInterval (10440542403 / 1000000000000) (10440542471 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (241024739926677 / 4000000000000) 0 (IntervalRat.scale (413 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-100273250774 / 1000000000000) (-100273250773 / 1000000000000), orderedInterval (-21754841323 / 1000000000000) (-21754841322 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (654429054891031 / 4000000000000) 0 (IntervalRat.scale (413 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (53447802524 / 1000000000000) (53447802525 / 1000000000000), orderedInterval (31999837984 / 1000000000000) (31999837985 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (893566925592887 / 4000000000000) 0 (IntervalRat.scale (413 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-48131308593 / 1000000000000) (-48131308592 / 1000000000000), orderedInterval (-22982611714 / 1000000000000) (-22982611713 / 1000000000000)))) (orderedInterval (4327723477 / 1000000000000) (4327723502 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (377834791006869 / 4000000000000) 0 (IntervalRat.scale (413 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (68857501555 / 1000000000000) (68857501556 / 1000000000000), orderedInterval (44337526203 / 1000000000000) (44337526204 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1535877448682549 / 4000000000000) 0 (IntervalRat.scale (413 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (40551240839 / 1000000000000) (40551240910 / 1000000000000), orderedInterval (3633894660 / 1000000000000) (3633894731 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1025894956917691 / 4000000000000) 0 (IntervalRat.scale (413 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-17174854585 / 1000000000000) (-17174854236 / 1000000000000), orderedInterval (46801318888 / 1000000000000) (46801319237 / 1000000000000)))) (orderedInterval (336610758 / 1000000000000) (336610887 / 1000000000000))) = true
  rfl'

theorem compactCertificate334_chunkChecks0 :
    compactCertificate334.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate334.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate334_chunkChecks0_0
    compactCertificate334_chunkChecks0_1 compactCertificate334_chunkChecks0_2

theorem compactCertificate334_chunkChecks1_0 :
    compactCertificate334.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (413 / 2) 1 (IntervalRat.scale (413 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-3347293728 / 1000000000000) (-3347293721 / 1000000000000), orderedInterval (55431105980 / 1000000000000) (55431105988 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (608427861483113 / 4000000000000) 1 (IntervalRat.scale (413 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (56004045110 / 1000000000000) (56004067685 / 1000000000000), orderedInterval (-32570473721 / 1000000000000) (-32570451146 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (196753069464329 / 800000000000) 1 (IntervalRat.scale (413 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (50563020086 / 1000000000000) (50563020510 / 1000000000000), orderedInterval (-5748880842 / 1000000000000) (-5748880418 / 1000000000000)))) (orderedInterval (21345613259 / 1000000000000) (21345613464 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (177537732540091 / 4000000000000) 1 (IntervalRat.scale (413 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (110944629965 / 1000000000000) (110944629966 / 1000000000000), orderedInterval (43849674390 / 1000000000000) (43849674391 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (476891322350527 / 4000000000000) 1 (IntervalRat.scale (413 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (42853243059 / 1000000000000) (42853243060 / 1000000000000), orderedInterval (59009483972 / 1000000000000) (59009483973 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1294852708755459 / 4000000000000) 1 (IntervalRat.scale (413 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-35124288389 / 1000000000000) (-35124288388 / 1000000000000), orderedInterval (-27017884312 / 1000000000000) (-27017884311 / 1000000000000)))) (orderedInterval (4152581720 / 1000000000000) (4152581749 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (953782644701467 / 4000000000000) 1 (IntervalRat.scale (413 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (23377640664 / 1000000000000) (23377640665 / 1000000000000), orderedInterval (46030942091 / 1000000000000) (46030942092 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1634322818400391 / 4000000000000) 1 (IntervalRat.scale (413 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (32307729848 / 1000000000000) (32307729849 / 1000000000000), orderedInterval (22639420790 / 1000000000000) (22639420791 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1203834791006869 / 4000000000000) 1 (IntervalRat.scale (413 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (6908756577 / 1000000000000) (6908756578 / 1000000000000), orderedInterval (45459149784 / 1000000000000) (45459149785 / 1000000000000)))) (orderedInterval (219577320 / 1000000000000) (219577341 / 1000000000000))) = true
  rfl'

theorem compactCertificate334_chunkChecks1_1 :
    compactCertificate334.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1846992149414587 / 4000000000000) 1 (IntervalRat.scale (413 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-24456977197 / 1000000000000) (-24456977196 / 1000000000000), orderedInterval (-27912256492 / 1000000000000) (-27912256491 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1066361414655523 / 4000000000000) 1 (IntervalRat.scale (413 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-16292314228 / 1000000000000) (-16292314227 / 1000000000000), orderedInterval (-46040815024 / 1000000000000) (-46040815023 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1892277043161407 / 4000000000000) 1 (IntervalRat.scale (413 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (18421314154 / 1000000000000) (18421314936 / 1000000000000), orderedInterval (-31742926519 / 1000000000000) (-31742925737 / 1000000000000)))) (orderedInterval (-3651261003 / 1000000000000) (-3651260578 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1768010673443483 / 4000000000000) 1 (IntervalRat.scale (413 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (6674170044 / 1000000000000) (6674170051 / 1000000000000), orderedInterval (-37367472969 / 1000000000000) (-37367472962 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1261735841344139 / 4000000000000) 1 (IntervalRat.scale (413 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (39661777281 / 1000000000000) (39661812094 / 1000000000000), orderedInterval (-21162063175 / 1000000000000) (-21162028362 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1430673967051581 / 4000000000000) 1 (IntervalRat.scale (413 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (12949571207 / 1000000000000) (12949571208 / 1000000000000), orderedInterval (40134428216 / 1000000000000) (40134428217 / 1000000000000)))) (orderedInterval (-1964642417 / 1000000000000) (-1964637348 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1192746798468589 / 4000000000000) 1 (IntervalRat.scale (413 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-22973793189 / 1000000000000) (-22973793188 / 1000000000000), orderedInterval (-40051086329 / 1000000000000) (-40051086328 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1053827968828369 / 4000000000000) 1 (IntervalRat.scale (413 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (16769564950 / 1000000000000) (16769564951 / 1000000000000), orderedInterval (46176330823 / 1000000000000) (46176330824 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (305440420284531 / 800000000000) 1 (IntervalRat.scale (413 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-25951621700 / 1000000000000) (-25951613789 / 1000000000000), orderedInterval (31560611903 / 1000000000000) (31560619814 / 1000000000000)))) (orderedInterval (-2545163414 / 1000000000000) (-2545163010 / 1000000000000))) = true
  rfl'

theorem compactCertificate334_chunkChecks1_2 :
    compactCertificate334.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (844864276955657 / 4000000000000) 1 (IntervalRat.scale (413 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-54812455389 / 1000000000000) (-54812455357 / 1000000000000), orderedInterval (-2977525328 / 1000000000000) (-2977525296 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (716200804190977 / 4000000000000) 1 (IntervalRat.scale (413 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-41256869150 / 1000000000000) (-41256869149 / 1000000000000), orderedInterval (-42936030012 / 1000000000000) (-42936030011 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (448165208993131 / 4000000000000) 1 (IntervalRat.scale (413 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-20233033483 / 1000000000000) (-20233033166 / 1000000000000), orderedInterval (72703530191 / 1000000000000) (72703530507 / 1000000000000)))) (orderedInterval (3878300066 / 1000000000000) (3878300125 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (241024739926677 / 4000000000000) 1 (IntervalRat.scale (413 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-100273250774 / 1000000000000) (-100273250773 / 1000000000000), orderedInterval (-21754841323 / 1000000000000) (-21754841322 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (654429054891031 / 4000000000000) 1 (IntervalRat.scale (413 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (53447802524 / 1000000000000) (53447802525 / 1000000000000), orderedInterval (31999837984 / 1000000000000) (31999837985 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (893566925592887 / 4000000000000) 1 (IntervalRat.scale (413 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-48131308593 / 1000000000000) (-48131308592 / 1000000000000), orderedInterval (-22982611714 / 1000000000000) (-22982611713 / 1000000000000)))) (orderedInterval (1447476460 / 1000000000000) (1447476483 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (377834791006869 / 4000000000000) 1 (IntervalRat.scale (413 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (68857501555 / 1000000000000) (68857501556 / 1000000000000), orderedInterval (44337526203 / 1000000000000) (44337526204 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1535877448682549 / 4000000000000) 1 (IntervalRat.scale (413 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (40551240839 / 1000000000000) (40551240910 / 1000000000000), orderedInterval (3633894660 / 1000000000000) (3633894731 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1025894956917691 / 4000000000000) 1 (IntervalRat.scale (413 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-17174854585 / 1000000000000) (-17174854236 / 1000000000000), orderedInterval (46801318888 / 1000000000000) (46801319237 / 1000000000000)))) (orderedInterval (-11334007112 / 1000000000000) (-11334006939 / 1000000000000))) = true
  rfl'

theorem compactCertificate334_chunkChecks1 :
    compactCertificate334.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate334.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate334_chunkChecks1_0
    compactCertificate334_chunkChecks1_1 compactCertificate334_chunkChecks1_2

theorem compactCertificate334_chunkChecks2_0 :
    compactCertificate334.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (413 / 2) 2 (IntervalRat.scale (413 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-3347293728 / 1000000000000) (-3347293721 / 1000000000000), orderedInterval (55431105980 / 1000000000000) (55431105988 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (608427861483113 / 4000000000000) 2 (IntervalRat.scale (413 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (56004045110 / 1000000000000) (56004067685 / 1000000000000), orderedInterval (-32570473721 / 1000000000000) (-32570451146 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (196753069464329 / 800000000000) 2 (IntervalRat.scale (413 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (50563020086 / 1000000000000) (50563020510 / 1000000000000), orderedInterval (-5748880842 / 1000000000000) (-5748880418 / 1000000000000)))) (orderedInterval (-3268523080 / 1000000000000) (-3268522907 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (177537732540091 / 4000000000000) 2 (IntervalRat.scale (413 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (110944629965 / 1000000000000) (110944629966 / 1000000000000), orderedInterval (43849674390 / 1000000000000) (43849674391 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (476891322350527 / 4000000000000) 2 (IntervalRat.scale (413 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (42853243059 / 1000000000000) (42853243060 / 1000000000000), orderedInterval (59009483972 / 1000000000000) (59009483973 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1294852708755459 / 4000000000000) 2 (IntervalRat.scale (413 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-35124288389 / 1000000000000) (-35124288388 / 1000000000000), orderedInterval (-27017884312 / 1000000000000) (-27017884311 / 1000000000000)))) (orderedInterval (-6622180622 / 1000000000000) (-6622180582 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (953782644701467 / 4000000000000) 2 (IntervalRat.scale (413 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (23377640664 / 1000000000000) (23377640665 / 1000000000000), orderedInterval (46030942091 / 1000000000000) (46030942092 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1634322818400391 / 4000000000000) 2 (IntervalRat.scale (413 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (32307729848 / 1000000000000) (32307729849 / 1000000000000), orderedInterval (22639420790 / 1000000000000) (22639420791 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1203834791006869 / 4000000000000) 2 (IntervalRat.scale (413 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (6908756577 / 1000000000000) (6908756578 / 1000000000000), orderedInterval (45459149784 / 1000000000000) (45459149785 / 1000000000000)))) (orderedInterval (3545425421 / 1000000000000) (3545425458 / 1000000000000))) = true
  rfl'

theorem compactCertificate334_chunkChecks2_1 :
    compactCertificate334.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1846992149414587 / 4000000000000) 2 (IntervalRat.scale (413 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-24456977197 / 1000000000000) (-24456977196 / 1000000000000), orderedInterval (-27912256492 / 1000000000000) (-27912256491 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1066361414655523 / 4000000000000) 2 (IntervalRat.scale (413 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-16292314228 / 1000000000000) (-16292314227 / 1000000000000), orderedInterval (-46040815024 / 1000000000000) (-46040815023 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1892277043161407 / 4000000000000) 2 (IntervalRat.scale (413 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (18421314154 / 1000000000000) (18421314936 / 1000000000000), orderedInterval (-31742926519 / 1000000000000) (-31742925737 / 1000000000000)))) (orderedInterval (-33442409580 / 1000000000000) (-33442408630 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1768010673443483 / 4000000000000) 2 (IntervalRat.scale (413 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (6674170044 / 1000000000000) (6674170051 / 1000000000000), orderedInterval (-37367472969 / 1000000000000) (-37367472962 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1261735841344139 / 4000000000000) 2 (IntervalRat.scale (413 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (39661777281 / 1000000000000) (39661812094 / 1000000000000), orderedInterval (-21162063175 / 1000000000000) (-21162028362 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1430673967051581 / 4000000000000) 2 (IntervalRat.scale (413 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (12949571207 / 1000000000000) (12949571208 / 1000000000000), orderedInterval (40134428216 / 1000000000000) (40134428217 / 1000000000000)))) (orderedInterval (-7993112090 / 1000000000000) (-7993104317 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1192746798468589 / 4000000000000) 2 (IntervalRat.scale (413 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-22973793189 / 1000000000000) (-22973793188 / 1000000000000), orderedInterval (-40051086329 / 1000000000000) (-40051086328 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1053827968828369 / 4000000000000) 2 (IntervalRat.scale (413 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (16769564950 / 1000000000000) (16769564951 / 1000000000000), orderedInterval (46176330823 / 1000000000000) (46176330824 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (305440420284531 / 800000000000) 2 (IntervalRat.scale (413 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-25951621700 / 1000000000000) (-25951613789 / 1000000000000), orderedInterval (31560611903 / 1000000000000) (31560619814 / 1000000000000)))) (orderedInterval (4399024182 / 1000000000000) (4399024920 / 1000000000000))) = true
  rfl'

theorem compactCertificate334_chunkChecks2_2 :
    compactCertificate334.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (844864276955657 / 4000000000000) 2 (IntervalRat.scale (413 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-54812455389 / 1000000000000) (-54812455357 / 1000000000000), orderedInterval (-2977525328 / 1000000000000) (-2977525296 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (716200804190977 / 4000000000000) 2 (IntervalRat.scale (413 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-41256869150 / 1000000000000) (-41256869149 / 1000000000000), orderedInterval (-42936030012 / 1000000000000) (-42936030011 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (448165208993131 / 4000000000000) 2 (IntervalRat.scale (413 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-20233033483 / 1000000000000) (-20233033166 / 1000000000000), orderedInterval (72703530191 / 1000000000000) (72703530507 / 1000000000000)))) (orderedInterval (-10749436271 / 1000000000000) (-10749436216 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (241024739926677 / 4000000000000) 2 (IntervalRat.scale (413 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-100273250774 / 1000000000000) (-100273250773 / 1000000000000), orderedInterval (-21754841323 / 1000000000000) (-21754841322 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (654429054891031 / 4000000000000) 2 (IntervalRat.scale (413 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (53447802524 / 1000000000000) (53447802525 / 1000000000000), orderedInterval (31999837984 / 1000000000000) (31999837985 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (893566925592887 / 4000000000000) 2 (IntervalRat.scale (413 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-48131308593 / 1000000000000) (-48131308592 / 1000000000000), orderedInterval (-22982611714 / 1000000000000) (-22982611713 / 1000000000000)))) (orderedInterval (-3720402059 / 1000000000000) (-3720402036 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (377834791006869 / 4000000000000) 2 (IntervalRat.scale (413 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (68857501555 / 1000000000000) (68857501556 / 1000000000000), orderedInterval (44337526203 / 1000000000000) (44337526204 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1535877448682549 / 4000000000000) 2 (IntervalRat.scale (413 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (40551240839 / 1000000000000) (40551240910 / 1000000000000), orderedInterval (3633894660 / 1000000000000) (3633894731 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1025894956917691 / 4000000000000) 2 (IntervalRat.scale (413 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-17174854585 / 1000000000000) (-17174854236 / 1000000000000), orderedInterval (46801318888 / 1000000000000) (46801319237 / 1000000000000)))) (orderedInterval (6409924935 / 1000000000000) (6409925175 / 1000000000000))) = true
  rfl'

theorem compactCertificate334_chunkChecks2 :
    compactCertificate334.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate334.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate334_chunkChecks2_0
    compactCertificate334_chunkChecks2_1 compactCertificate334_chunkChecks2_2

theorem compactCertificate334_chunkChecks3_0 :
    compactCertificate334.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (413 / 2) 3 (IntervalRat.scale (413 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-3347293728 / 1000000000000) (-3347293721 / 1000000000000), orderedInterval (55431105980 / 1000000000000) (55431105988 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (608427861483113 / 4000000000000) 3 (IntervalRat.scale (413 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (56004045110 / 1000000000000) (56004067685 / 1000000000000), orderedInterval (-32570473721 / 1000000000000) (-32570451146 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (196753069464329 / 800000000000) 3 (IntervalRat.scale (413 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (50563020086 / 1000000000000) (50563020510 / 1000000000000), orderedInterval (-5748880842 / 1000000000000) (-5748880418 / 1000000000000)))) (orderedInterval (-21263404916 / 1000000000000) (-21263404764 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (177537732540091 / 4000000000000) 3 (IntervalRat.scale (413 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (110944629965 / 1000000000000) (110944629966 / 1000000000000), orderedInterval (43849674390 / 1000000000000) (43849674391 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (476891322350527 / 4000000000000) 3 (IntervalRat.scale (413 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (42853243059 / 1000000000000) (42853243060 / 1000000000000), orderedInterval (59009483972 / 1000000000000) (59009483973 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1294852708755459 / 4000000000000) 3 (IntervalRat.scale (413 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-35124288389 / 1000000000000) (-35124288388 / 1000000000000), orderedInterval (-27017884312 / 1000000000000) (-27017884311 / 1000000000000)))) (orderedInterval (-7776846749 / 1000000000000) (-7776846689 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (953782644701467 / 4000000000000) 3 (IntervalRat.scale (413 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (23377640664 / 1000000000000) (23377640665 / 1000000000000), orderedInterval (46030942091 / 1000000000000) (46030942092 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1634322818400391 / 4000000000000) 3 (IntervalRat.scale (413 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (32307729848 / 1000000000000) (32307729849 / 1000000000000), orderedInterval (22639420790 / 1000000000000) (22639420791 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1203834791006869 / 4000000000000) 3 (IntervalRat.scale (413 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (6908756577 / 1000000000000) (6908756578 / 1000000000000), orderedInterval (45459149784 / 1000000000000) (45459149785 / 1000000000000)))) (orderedInterval (1990613243 / 1000000000000) (1990613309 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate334_chunkChecks3_1 :
    compactCertificate334.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1846992149414587 / 4000000000000) 3 (IntervalRat.scale (413 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-24456977197 / 1000000000000) (-24456977196 / 1000000000000), orderedInterval (-27912256492 / 1000000000000) (-27912256491 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1066361414655523 / 4000000000000) 3 (IntervalRat.scale (413 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-16292314228 / 1000000000000) (-16292314227 / 1000000000000), orderedInterval (-46040815024 / 1000000000000) (-46040815023 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1892277043161407 / 4000000000000) 3 (IntervalRat.scale (413 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (18421314154 / 1000000000000) (18421314936 / 1000000000000), orderedInterval (-31742926519 / 1000000000000) (-31742925737 / 1000000000000)))) (orderedInterval (6304147065 / 1000000000000) (6304149203 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1768010673443483 / 4000000000000) 3 (IntervalRat.scale (413 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (6674170044 / 1000000000000) (6674170051 / 1000000000000), orderedInterval (-37367472969 / 1000000000000) (-37367472962 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1261735841344139 / 4000000000000) 3 (IntervalRat.scale (413 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (39661777281 / 1000000000000) (39661812094 / 1000000000000), orderedInterval (-21162063175 / 1000000000000) (-21162028362 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1430673967051581 / 4000000000000) 3 (IntervalRat.scale (413 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (12949571207 / 1000000000000) (12949571208 / 1000000000000), orderedInterval (40134428216 / 1000000000000) (40134428217 / 1000000000000)))) (orderedInterval (1611084359 / 1000000000000) (1611096243 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1192746798468589 / 4000000000000) 3 (IntervalRat.scale (413 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-22973793189 / 1000000000000) (-22973793188 / 1000000000000), orderedInterval (-40051086329 / 1000000000000) (-40051086328 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1053827968828369 / 4000000000000) 3 (IntervalRat.scale (413 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (16769564950 / 1000000000000) (16769564951 / 1000000000000), orderedInterval (46176330823 / 1000000000000) (46176330824 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (305440420284531 / 800000000000) 3 (IntervalRat.scale (413 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-25951621700 / 1000000000000) (-25951613789 / 1000000000000), orderedInterval (31560611903 / 1000000000000) (31560619814 / 1000000000000)))) (orderedInterval (1751428918 / 1000000000000) (1751430267 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate334_chunkChecks3_2 :
    compactCertificate334.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (844864276955657 / 4000000000000) 3 (IntervalRat.scale (413 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-54812455389 / 1000000000000) (-54812455357 / 1000000000000), orderedInterval (-2977525328 / 1000000000000) (-2977525296 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (716200804190977 / 4000000000000) 3 (IntervalRat.scale (413 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-41256869150 / 1000000000000) (-41256869149 / 1000000000000), orderedInterval (-42936030012 / 1000000000000) (-42936030011 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (448165208993131 / 4000000000000) 3 (IntervalRat.scale (413 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-20233033483 / 1000000000000) (-20233033166 / 1000000000000), orderedInterval (72703530191 / 1000000000000) (72703530507 / 1000000000000)))) (orderedInterval (-2419529972 / 1000000000000) (-2419529920 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (241024739926677 / 4000000000000) 3 (IntervalRat.scale (413 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-100273250774 / 1000000000000) (-100273250773 / 1000000000000), orderedInterval (-21754841323 / 1000000000000) (-21754841322 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (654429054891031 / 4000000000000) 3 (IntervalRat.scale (413 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (53447802524 / 1000000000000) (53447802525 / 1000000000000), orderedInterval (31999837984 / 1000000000000) (31999837985 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (893566925592887 / 4000000000000) 3 (IntervalRat.scale (413 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-48131308593 / 1000000000000) (-48131308592 / 1000000000000), orderedInterval (-22982611714 / 1000000000000) (-22982611713 / 1000000000000)))) (orderedInterval (-1860799639 / 1000000000000) (-1860799616 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (377834791006869 / 4000000000000) 3 (IntervalRat.scale (413 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (68857501555 / 1000000000000) (68857501556 / 1000000000000), orderedInterval (44337526203 / 1000000000000) (44337526204 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1535877448682549 / 4000000000000) 3 (IntervalRat.scale (413 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (40551240839 / 1000000000000) (40551240910 / 1000000000000), orderedInterval (3633894660 / 1000000000000) (3633894731 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1025894956917691 / 4000000000000) 3 (IntervalRat.scale (413 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-17174854585 / 1000000000000) (-17174854236 / 1000000000000), orderedInterval (46801318888 / 1000000000000) (46801319237 / 1000000000000)))) (orderedInterval (18668459200 / 1000000000000) (18668459547 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate334_chunkChecks3 :
    compactCertificate334.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate334.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate334_chunkChecks3_0
    compactCertificate334_chunkChecks3_1 compactCertificate334_chunkChecks3_2

theorem compactCertificate334_chunkChecks4_0 :
    compactCertificate334.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (413 / 2) 4 (IntervalRat.scale (413 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-3347293728 / 1000000000000) (-3347293721 / 1000000000000), orderedInterval (55431105980 / 1000000000000) (55431105988 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (608427861483113 / 4000000000000) 4 (IntervalRat.scale (413 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (56004045110 / 1000000000000) (56004067685 / 1000000000000), orderedInterval (-32570473721 / 1000000000000) (-32570451146 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (196753069464329 / 800000000000) 4 (IntervalRat.scale (413 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (50563020086 / 1000000000000) (50563020510 / 1000000000000), orderedInterval (-5748880842 / 1000000000000) (-5748880418 / 1000000000000)))) (orderedInterval (5002779298 / 1000000000000) (5002779440 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (177537732540091 / 4000000000000) 4 (IntervalRat.scale (413 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (110944629965 / 1000000000000) (110944629966 / 1000000000000), orderedInterval (43849674390 / 1000000000000) (43849674391 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (476891322350527 / 4000000000000) 4 (IntervalRat.scale (413 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (42853243059 / 1000000000000) (42853243060 / 1000000000000), orderedInterval (59009483972 / 1000000000000) (59009483973 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1294852708755459 / 4000000000000) 4 (IntervalRat.scale (413 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-35124288389 / 1000000000000) (-35124288388 / 1000000000000), orderedInterval (-27017884312 / 1000000000000) (-27017884311 / 1000000000000)))) (orderedInterval (15325535848 / 1000000000000) (15325535939 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (953782644701467 / 4000000000000) 4 (IntervalRat.scale (413 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (23377640664 / 1000000000000) (23377640665 / 1000000000000), orderedInterval (46030942091 / 1000000000000) (46030942092 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1634322818400391 / 4000000000000) 4 (IntervalRat.scale (413 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (32307729848 / 1000000000000) (32307729849 / 1000000000000), orderedInterval (22639420790 / 1000000000000) (22639420791 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1203834791006869 / 4000000000000) 4 (IntervalRat.scale (413 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (6908756577 / 1000000000000) (6908756578 / 1000000000000), orderedInterval (45459149784 / 1000000000000) (45459149785 / 1000000000000)))) (orderedInterval (-14538297842 / 1000000000000) (-14538297720 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate334_chunkChecks4_1 :
    compactCertificate334.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1846992149414587 / 4000000000000) 4 (IntervalRat.scale (413 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-24456977197 / 1000000000000) (-24456977196 / 1000000000000), orderedInterval (-27912256492 / 1000000000000) (-27912256491 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1066361414655523 / 4000000000000) 4 (IntervalRat.scale (413 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-16292314228 / 1000000000000) (-16292314227 / 1000000000000), orderedInterval (-46040815024 / 1000000000000) (-46040815023 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1892277043161407 / 4000000000000) 4 (IntervalRat.scale (413 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (18421314154 / 1000000000000) (18421314936 / 1000000000000), orderedInterval (-31742926519 / 1000000000000) (-31742925737 / 1000000000000)))) (orderedInterval (177355814055 / 1000000000000) (177355818904 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1768010673443483 / 4000000000000) 4 (IntervalRat.scale (413 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (6674170044 / 1000000000000) (6674170051 / 1000000000000), orderedInterval (-37367472969 / 1000000000000) (-37367472962 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1261735841344139 / 4000000000000) 4 (IntervalRat.scale (413 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (39661777281 / 1000000000000) (39661812094 / 1000000000000), orderedInterval (-21162063175 / 1000000000000) (-21162028362 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1430673967051581 / 4000000000000) 4 (IntervalRat.scale (413 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (12949571207 / 1000000000000) (12949571208 / 1000000000000), orderedInterval (40134428216 / 1000000000000) (40134428217 / 1000000000000)))) (orderedInterval (17284865720 / 1000000000000) (17284883954 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1192746798468589 / 4000000000000) 4 (IntervalRat.scale (413 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-22973793189 / 1000000000000) (-22973793188 / 1000000000000), orderedInterval (-40051086329 / 1000000000000) (-40051086328 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1053827968828369 / 4000000000000) 4 (IntervalRat.scale (413 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (16769564950 / 1000000000000) (16769564951 / 1000000000000), orderedInterval (46176330823 / 1000000000000) (46176330824 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (305440420284531 / 800000000000) 4 (IntervalRat.scale (413 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-25951621700 / 1000000000000) (-25951613789 / 1000000000000), orderedInterval (31560611903 / 1000000000000) (31560619814 / 1000000000000)))) (orderedInterval (-11477844605 / 1000000000000) (-11477842120 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate334_chunkChecks4_2 :
    compactCertificate334.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (844864276955657 / 4000000000000) 4 (IntervalRat.scale (413 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-54812455389 / 1000000000000) (-54812455357 / 1000000000000), orderedInterval (-2977525328 / 1000000000000) (-2977525296 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (716200804190977 / 4000000000000) 4 (IntervalRat.scale (413 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-41256869150 / 1000000000000) (-41256869149 / 1000000000000), orderedInterval (-42936030012 / 1000000000000) (-42936030011 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (448165208993131 / 4000000000000) 4 (IntervalRat.scale (413 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-20233033483 / 1000000000000) (-20233033166 / 1000000000000), orderedInterval (72703530191 / 1000000000000) (72703530507 / 1000000000000)))) (orderedInterval (10878533753 / 1000000000000) (10878533804 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (241024739926677 / 4000000000000) 4 (IntervalRat.scale (413 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-100273250774 / 1000000000000) (-100273250773 / 1000000000000), orderedInterval (-21754841323 / 1000000000000) (-21754841322 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (654429054891031 / 4000000000000) 4 (IntervalRat.scale (413 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (53447802524 / 1000000000000) (53447802525 / 1000000000000), orderedInterval (31999837984 / 1000000000000) (31999837985 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (893566925592887 / 4000000000000) 4 (IntervalRat.scale (413 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-48131308593 / 1000000000000) (-48131308592 / 1000000000000), orderedInterval (-22982611714 / 1000000000000) (-22982611713 / 1000000000000)))) (orderedInterval (4605589512 / 1000000000000) (4605589537 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (377834791006869 / 4000000000000) 4 (IntervalRat.scale (413 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (68857501555 / 1000000000000) (68857501556 / 1000000000000), orderedInterval (44337526203 / 1000000000000) (44337526204 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1535877448682549 / 4000000000000) 4 (IntervalRat.scale (413 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (40551240839 / 1000000000000) (40551240910 / 1000000000000), orderedInterval (3633894660 / 1000000000000) (3633894731 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1025894956917691 / 4000000000000) 4 (IntervalRat.scale (413 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-17174854585 / 1000000000000) (-17174854236 / 1000000000000), orderedInterval (46801318888 / 1000000000000) (46801319237 / 1000000000000)))) (orderedInterval (-31953364311 / 1000000000000) (-31953363791 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate334_chunkChecks4 :
    compactCertificate334.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate334.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate334_chunkChecks4_0
    compactCertificate334_chunkChecks4_1 compactCertificate334_chunkChecks4_2

theorem compactCertificate334_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate334.chunkCheck r b = true :=
  compactCertificate334.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate334_chunkChecks0
    · exact compactCertificate334_chunkChecks1
    · exact compactCertificate334_chunkChecks2
    · exact compactCertificate334_chunkChecks3
    · exact compactCertificate334_chunkChecks4)

theorem compactCertificate334_coefficient0 :
    compactCertificate334.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate334_coefficient1 :
    compactCertificate334.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate334_coefficient2 :
    compactCertificate334.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate334_coefficient3 :
    compactCertificate334.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate334_coefficient4 :
    compactCertificate334.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate334_coefficients : ∀ r : Fin 5,
    compactCertificate334.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate334_coefficient0
  · exact compactCertificate334_coefficient1
  · exact compactCertificate334_coefficient2
  · exact compactCertificate334_coefficient3
  · exact compactCertificate334_coefficient4

theorem compactCertificate334_lower : (1 : ℚ) ≤ compactCertificate334.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate334, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate334_proves {t : ℝ} (ht : t ∈ compactCertificate334.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate334.proves compactCertificate334_states compactCertificate334_chunks
    compactCertificate334_coefficients compactCertificate334_lower ht

end Erdos232
