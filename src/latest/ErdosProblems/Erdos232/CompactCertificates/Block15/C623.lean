/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate623 : CompactCertificate where
  left := 494
  right := 495
  center := 989 / 2
  grid := fun i =>
    match i.val with
    | 0 => 157
    | 1 => 116
    | 2 => 188
    | 3 => 34
    | 4 => 91
    | 5 => 247
    | 6 => 182
    | 7 => 312
    | 8 => 230
    | 9 => 352
    | 10 => 203
    | 11 => 361
    | 12 => 337
    | 13 => 241
    | 14 => 273
    | 15 => 227
    | 16 => 201
    | 17 => 291
    | 18 => 161
    | 19 => 137
    | 20 => 85
    | 21 => 46
    | 22 => 125
    | 23 => 170
    | 24 => 72
    | 25 => 293
    | _ => 196
  point := fun i =>
    match i.val with
    | 0 => 989 / 2
    | 1 => 1456985847474089 / 4000000000000
    | 2 => 471159287409737 / 800000000000
    | 3 => 425144836518523 / 4000000000000
    | 4 => 1141998832456831 / 4000000000000
    | 5 => 3100748980530627 / 4000000000000
    | 6 => 2283997664914651 / 4000000000000
    | 7 => 3913668928324423 / 4000000000000
    | 8 => 2882790819142357 / 4000000000000
    | 9 => 4422942459494011 / 4000000000000
    | 10 => 2553587019598819 / 4000000000000
    | 11 => 4531384977449471 / 4000000000000
    | 12 => 4233807641732699 / 4000000000000
    | 13 => 3021444908206667 / 4000000000000
    | 14 => 3425996497370493 / 4000000000000
    | 15 => 2856238701417517 / 4000000000000
    | 16 => 2523573513731857 / 4000000000000
    | 17 => 731429965281843 / 800000000000
    | 18 => 2023173777019721 / 4000000000000
    | 19 => 1715066816815681 / 4000000000000
    | 20 => 1073209180857643 / 4000000000000
    | 21 => 577175466797781 / 4000000000000
    | 22 => 1567143668976343 / 4000000000000
    | 23 => 2139800700753911 / 4000000000000
    | 24 => 904790819142357 / 4000000000000
    | 25 => 3677924447329397 / 4000000000000
    | _ => 2456683080851323 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-31754153333 / 1000000000000) (-31754079079 / 1000000000000), orderedInterval (16737655808 / 1000000000000) (16737730062 / 1000000000000))
    | 1 => (orderedInterval (23838655520 / 1000000000000) (23838655521 / 1000000000000), orderedInterval (34310996662 / 1000000000000) (34310996663 / 1000000000000))
    | 2 => (orderedInterval (-25447110057 / 1000000000000) (-25447090657 / 1000000000000), orderedInterval (20839540488 / 1000000000000) (20839559888 / 1000000000000))
    | 3 => (orderedInterval (19617839486 / 1000000000000) (19617839487 / 1000000000000), orderedInterval (74773409983 / 1000000000000) (74773409984 / 1000000000000))
    | 4 => (orderedInterval (-18377355587 / 1000000000000) (-18377355586 / 1000000000000), orderedInterval (-43466310352 / 1000000000000) (-43466310351 / 1000000000000))
    | 5 => (orderedInterval (25888853 / 1000000000000) (25888854 / 1000000000000), orderedInterval (-28657405791 / 1000000000000) (-28657405790 / 1000000000000))
    | 6 => (orderedInterval (491907690 / 1000000000000) (491907691 / 1000000000000), orderedInterval (33386398789 / 1000000000000) (33386398790 / 1000000000000))
    | 7 => (orderedInterval (-21104585184 / 1000000000000) (-21104578516 / 1000000000000), orderedInterval (14337660934 / 1000000000000) (14337667603 / 1000000000000))
    | 8 => (orderedInterval (-26259910109 / 1000000000000) (-26259846345 / 1000000000000), orderedInterval (13937840364 / 1000000000000) (13937904128 / 1000000000000))
    | 9 => (orderedInterval (15093001598 / 1000000000000) (15093001599 / 1000000000000), orderedInterval (18646446295 / 1000000000000) (18646446296 / 1000000000000))
    | 10 => (orderedInterval (-31303401002 / 1000000000000) (-31303400764 / 1000000000000), orderedInterval (-4136407070 / 1000000000000) (-4136406832 / 1000000000000))
    | 11 => (orderedInterval (11018602208 / 1000000000000) (11018602212 / 1000000000000), orderedInterval (-20994272204 / 1000000000000) (-20994272200 / 1000000000000))
    | 12 => (orderedInterval (-12195779548 / 1000000000000) (-12195779547 / 1000000000000), orderedInterval (-21271600070 / 1000000000000) (-21271600069 / 1000000000000))
    | 13 => (orderedInterval (24067579398 / 1000000000000) (24067600299 / 1000000000000), orderedInterval (-16250250783 / 1000000000000) (-16250229882 / 1000000000000))
    | 14 => (orderedInterval (9869408354 / 1000000000000) (9869408360 / 1000000000000), orderedInterval (-25419855214 / 1000000000000) (-25419855209 / 1000000000000))
    | 15 => (orderedInterval (-29596835081 / 1000000000000) (-29596827154 / 1000000000000), orderedInterval (3967514840 / 1000000000000) (3967522767 / 1000000000000))
    | 16 => (orderedInterval (-6884373004 / 1000000000000) (-6884373003 / 1000000000000), orderedInterval (-31005547458 / 1000000000000) (-31005547457 / 1000000000000))
    | 17 => (orderedInterval (-20156080961 / 1000000000000) (-20156080960 / 1000000000000), orderedInterval (-17019359784 / 1000000000000) (-17019359783 / 1000000000000))
    | 18 => (orderedInterval (-25005490102 / 1000000000000) (-25005490101 / 1000000000000), orderedInterval (-25142344961 / 1000000000000) (-25142344960 / 1000000000000))
    | 19 => (orderedInterval (28856663668 / 1000000000000) (28856692495 / 1000000000000), orderedInterval (-25569161559 / 1000000000000) (-25569132733 / 1000000000000))
    | 20 => (orderedInterval (-43182697908 / 1000000000000) (-43182671866 / 1000000000000), orderedInterval (22619844293 / 1000000000000) (22619870336 / 1000000000000))
    | 21 => (orderedInterval (35571283712 / 1000000000000) (35571283713 / 1000000000000), orderedInterval (55971857527 / 1000000000000) (55971857528 / 1000000000000))
    | 22 => (orderedInterval (5149045867 / 1000000000000) (5149045872 / 1000000000000), orderedInterval (-39986641946 / 1000000000000) (-39986641941 / 1000000000000))
    | 23 => (orderedInterval (34345531237 / 1000000000000) (34345533218 / 1000000000000), orderedInterval (-3262928071 / 1000000000000) (-3262926090 / 1000000000000))
    | 24 => (orderedInterval (37605840816 / 1000000000000) (37605840817 / 1000000000000), orderedInterval (37336658947 / 1000000000000) (37336658948 / 1000000000000))
    | 25 => (orderedInterval (5749274711 / 1000000000000) (5749274712 / 1000000000000), orderedInterval (-25680245528 / 1000000000000) (-25680245527 / 1000000000000))
    | _ => (orderedInterval (-23010143843 / 1000000000000) (-23010136717 / 1000000000000), orderedInterval (22537280505 / 1000000000000) (22537287631 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-13857370186 / 1000000000000) (-13857339582 / 1000000000000)
      | 1 => orderedInterval (-885669448 / 1000000000000) (-885669388 / 1000000000000)
      | 2 => orderedInterval (16299410 / 1000000000000) (16301185 / 1000000000000)
      | 3 => orderedInterval (-3434809442 / 1000000000000) (-3434809228 / 1000000000000)
      | 4 => orderedInterval (2446125822 / 1000000000000) (2446127858 / 1000000000000)
      | 5 => orderedInterval (-463880007 / 1000000000000) (-463879868 / 1000000000000)
      | 6 => orderedInterval (959076855 / 1000000000000) (959079459 / 1000000000000)
      | 7 => orderedInterval (-3405846494 / 1000000000000) (-3405846283 / 1000000000000)
      | _ => orderedInterval (4076011135 / 1000000000000) (4076012609 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (8326177798 / 1000000000000) (8326208625 / 1000000000000)
      | 1 => orderedInterval (2102984358 / 1000000000000) (2102984425 / 1000000000000)
      | 2 => orderedInterval (-384063459 / 1000000000000) (-384060758 / 1000000000000)
      | 3 => orderedInterval (-14641379944 / 1000000000000) (-14641379514 / 1000000000000)
      | 4 => orderedInterval (-1302522306 / 1000000000000) (-1302519191 / 1000000000000)
      | 5 => orderedInterval (1524215753 / 1000000000000) (1524215954 / 1000000000000)
      | 6 => orderedInterval (5766265390 / 1000000000000) (5766267380 / 1000000000000)
      | 7 => orderedInterval (687682008 / 1000000000000) (687682225 / 1000000000000)
      | _ => orderedInterval (-1262015594 / 1000000000000) (-1262013741 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (14567010162 / 1000000000000) (14567041315 / 1000000000000)
      | 1 => orderedInterval (233765760 / 1000000000000) (233765854 / 1000000000000)
      | 2 => orderedInterval (-1199543828 / 1000000000000) (-1199539658 / 1000000000000)
      | 3 => orderedInterval (9083822454 / 1000000000000) (9083823357 / 1000000000000)
      | 4 => orderedInterval (-6166687800 / 1000000000000) (-6166683023 / 1000000000000)
      | 5 => orderedInterval (1832487660 / 1000000000000) (1832487953 / 1000000000000)
      | 6 => orderedInterval (-2552778712 / 1000000000000) (-2552777122 / 1000000000000)
      | 7 => orderedInterval (3208307464 / 1000000000000) (3208307695 / 1000000000000)
      | _ => orderedInterval (-5086573342 / 1000000000000) (-5086570992 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-8857407462 / 1000000000000) (-8857375993 / 1000000000000)
      | 1 => orderedInterval (-7535078062 / 1000000000000) (-7535077922 / 1000000000000)
      | 2 => orderedInterval (2385116136 / 1000000000000) (2385122664 / 1000000000000)
      | 3 => orderedInterval (73566492145 / 1000000000000) (73566494099 / 1000000000000)
      | 4 => orderedInterval (1055192236 / 1000000000000) (1055199559 / 1000000000000)
      | 5 => orderedInterval (-1072163340 / 1000000000000) (-1072162906 / 1000000000000)
      | 6 => orderedInterval (-5357679101 / 1000000000000) (-5357677793 / 1000000000000)
      | 7 => orderedInterval (-748563857 / 1000000000000) (-748563609 / 1000000000000)
      | _ => orderedInterval (-5348648488 / 1000000000000) (-5348645484 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-15489533898 / 1000000000000) (-15489501989 / 1000000000000)
      | 1 => orderedInterval (-55646504 / 1000000000000) (-55646289 / 1000000000000)
      | 2 => orderedInterval (7103458343 / 1000000000000) (7103468762 / 1000000000000)
      | 3 => orderedInterval (-30643203033 / 1000000000000) (-30643198728 / 1000000000000)
      | 4 => orderedInterval (16558682349 / 1000000000000) (16558693604 / 1000000000000)
      | 5 => orderedInterval (-6468679826 / 1000000000000) (-6468679178 / 1000000000000)
      | 6 => orderedInterval (3352792940 / 1000000000000) (3352794046 / 1000000000000)
      | 7 => orderedInterval (-3652768793 / 1000000000000) (-3652768527 / 1000000000000)
      | _ => orderedInterval (4710321479 / 1000000000000) (4710325375 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-14550062355 / 1000000000000) (-14550023238 / 1000000000000)
    | 1 => orderedInterval (817344004 / 1000000000000) (817385405 / 1000000000000)
    | 2 => orderedInterval (13919809818 / 1000000000000) (13919855379 / 1000000000000)
    | 3 => orderedInterval (48087260207 / 1000000000000) (48087312615 / 1000000000000)
    | _ => orderedInterval (-24584576943 / 1000000000000) (-24584512924 / 1000000000000)

theorem compactCertificate623_stateChecks0 :
    compactCertificate623.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 157 12 (989 / 2)) (orderedInterval (-31754153333 / 1000000000000) (-31754079079 / 1000000000000), orderedInterval (16737655808 / 1000000000000) (16737730062 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 116 12 (1456985847474089 / 4000000000000)) (orderedInterval (23838655520 / 1000000000000) (23838655521 / 1000000000000), orderedInterval (34310996662 / 1000000000000) (34310996663 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 188 12 (471159287409737 / 800000000000)) (orderedInterval (-25447110057 / 1000000000000) (-25447090657 / 1000000000000), orderedInterval (20839540488 / 1000000000000) (20839559888 / 1000000000000))) = true
  rfl'

theorem compactCertificate623_stateChecks1 :
    compactCertificate623.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (425144836518523 / 4000000000000)) (orderedInterval (19617839486 / 1000000000000) (19617839487 / 1000000000000), orderedInterval (74773409983 / 1000000000000) (74773409984 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 91 12 (1141998832456831 / 4000000000000)) (orderedInterval (-18377355587 / 1000000000000) (-18377355586 / 1000000000000), orderedInterval (-43466310352 / 1000000000000) (-43466310351 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 247 12 (3100748980530627 / 4000000000000)) (orderedInterval (25888853 / 1000000000000) (25888854 / 1000000000000), orderedInterval (-28657405791 / 1000000000000) (-28657405790 / 1000000000000))) = true
  rfl'

theorem compactCertificate623_stateChecks2 :
    compactCertificate623.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 182 12 (2283997664914651 / 4000000000000)) (orderedInterval (491907690 / 1000000000000) (491907691 / 1000000000000), orderedInterval (33386398789 / 1000000000000) (33386398790 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 312 12 (3913668928324423 / 4000000000000)) (orderedInterval (-21104585184 / 1000000000000) (-21104578516 / 1000000000000), orderedInterval (14337660934 / 1000000000000) (14337667603 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 230 12 (2882790819142357 / 4000000000000)) (orderedInterval (-26259910109 / 1000000000000) (-26259846345 / 1000000000000), orderedInterval (13937840364 / 1000000000000) (13937904128 / 1000000000000))) = true
  rfl'

theorem compactCertificate623_stateChecks3 :
    compactCertificate623.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 352 12 (4422942459494011 / 4000000000000)) (orderedInterval (15093001598 / 1000000000000) (15093001599 / 1000000000000), orderedInterval (18646446295 / 1000000000000) (18646446296 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 203 12 (2553587019598819 / 4000000000000)) (orderedInterval (-31303401002 / 1000000000000) (-31303400764 / 1000000000000), orderedInterval (-4136407070 / 1000000000000) (-4136406832 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 361 12 (4531384977449471 / 4000000000000)) (orderedInterval (11018602208 / 1000000000000) (11018602212 / 1000000000000), orderedInterval (-20994272204 / 1000000000000) (-20994272200 / 1000000000000))) = true
  rfl'

theorem compactCertificate623_stateChecks4 :
    compactCertificate623.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 337 12 (4233807641732699 / 4000000000000)) (orderedInterval (-12195779548 / 1000000000000) (-12195779547 / 1000000000000), orderedInterval (-21271600070 / 1000000000000) (-21271600069 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 241 12 (3021444908206667 / 4000000000000)) (orderedInterval (24067579398 / 1000000000000) (24067600299 / 1000000000000), orderedInterval (-16250250783 / 1000000000000) (-16250229882 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 273 12 (3425996497370493 / 4000000000000)) (orderedInterval (9869408354 / 1000000000000) (9869408360 / 1000000000000), orderedInterval (-25419855214 / 1000000000000) (-25419855209 / 1000000000000))) = true
  rfl'

theorem compactCertificate623_stateChecks5 :
    compactCertificate623.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 227 12 (2856238701417517 / 4000000000000)) (orderedInterval (-29596835081 / 1000000000000) (-29596827154 / 1000000000000), orderedInterval (3967514840 / 1000000000000) (3967522767 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 201 12 (2523573513731857 / 4000000000000)) (orderedInterval (-6884373004 / 1000000000000) (-6884373003 / 1000000000000), orderedInterval (-31005547458 / 1000000000000) (-31005547457 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 291 12 (731429965281843 / 800000000000)) (orderedInterval (-20156080961 / 1000000000000) (-20156080960 / 1000000000000), orderedInterval (-17019359784 / 1000000000000) (-17019359783 / 1000000000000))) = true
  rfl'

theorem compactCertificate623_stateChecks6 :
    compactCertificate623.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 161 12 (2023173777019721 / 4000000000000)) (orderedInterval (-25005490102 / 1000000000000) (-25005490101 / 1000000000000), orderedInterval (-25142344961 / 1000000000000) (-25142344960 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 137 12 (1715066816815681 / 4000000000000)) (orderedInterval (28856663668 / 1000000000000) (28856692495 / 1000000000000), orderedInterval (-25569161559 / 1000000000000) (-25569132733 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 85 12 (1073209180857643 / 4000000000000)) (orderedInterval (-43182697908 / 1000000000000) (-43182671866 / 1000000000000), orderedInterval (22619844293 / 1000000000000) (22619870336 / 1000000000000))) = true
  rfl'

theorem compactCertificate623_stateChecks7 :
    compactCertificate623.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (577175466797781 / 4000000000000)) (orderedInterval (35571283712 / 1000000000000) (35571283713 / 1000000000000), orderedInterval (55971857527 / 1000000000000) (55971857528 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 125 12 (1567143668976343 / 4000000000000)) (orderedInterval (5149045867 / 1000000000000) (5149045872 / 1000000000000), orderedInterval (-39986641946 / 1000000000000) (-39986641941 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 170 12 (2139800700753911 / 4000000000000)) (orderedInterval (34345531237 / 1000000000000) (34345533218 / 1000000000000), orderedInterval (-3262928071 / 1000000000000) (-3262926090 / 1000000000000))) = true
  rfl'

theorem compactCertificate623_stateChecks8 :
    compactCertificate623.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 72 12 (904790819142357 / 4000000000000)) (orderedInterval (37605840816 / 1000000000000) (37605840817 / 1000000000000), orderedInterval (37336658947 / 1000000000000) (37336658948 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 293 12 (3677924447329397 / 4000000000000)) (orderedInterval (5749274711 / 1000000000000) (5749274712 / 1000000000000), orderedInterval (-25680245528 / 1000000000000) (-25680245527 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 196 12 (2456683080851323 / 4000000000000)) (orderedInterval (-23010143843 / 1000000000000) (-23010136717 / 1000000000000), orderedInterval (22537280505 / 1000000000000) (22537287631 / 1000000000000))) = true
  rfl'

theorem compactCertificate623_states : ∀ j,
    BesselStateValid (compactCertificate623.point j) (compactCertificate623.state j) :=
  compactCertificate623.statesValid_of_checks3 compactCertificate623_stateChecks0
    compactCertificate623_stateChecks1 compactCertificate623_stateChecks2
    compactCertificate623_stateChecks3 compactCertificate623_stateChecks4
    compactCertificate623_stateChecks5 compactCertificate623_stateChecks6
    compactCertificate623_stateChecks7 compactCertificate623_stateChecks8

theorem compactCertificate623_chunkChecks0_0 :
    compactCertificate623.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (989 / 2) 0 (IntervalRat.scale (989 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-31754153333 / 1000000000000) (-31754079079 / 1000000000000), orderedInterval (16737655808 / 1000000000000) (16737730062 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1456985847474089 / 4000000000000) 0 (IntervalRat.scale (989 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (23838655520 / 1000000000000) (23838655521 / 1000000000000), orderedInterval (34310996662 / 1000000000000) (34310996663 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (471159287409737 / 800000000000) 0 (IntervalRat.scale (989 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-25447110057 / 1000000000000) (-25447090657 / 1000000000000), orderedInterval (20839540488 / 1000000000000) (20839559888 / 1000000000000)))) (orderedInterval (-13857370186 / 1000000000000) (-13857339582 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (425144836518523 / 4000000000000) 0 (IntervalRat.scale (989 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (19617839486 / 1000000000000) (19617839487 / 1000000000000), orderedInterval (74773409983 / 1000000000000) (74773409984 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (1141998832456831 / 4000000000000) 0 (IntervalRat.scale (989 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-18377355587 / 1000000000000) (-18377355586 / 1000000000000), orderedInterval (-43466310352 / 1000000000000) (-43466310351 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (3100748980530627 / 4000000000000) 0 (IntervalRat.scale (989 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (25888853 / 1000000000000) (25888854 / 1000000000000), orderedInterval (-28657405791 / 1000000000000) (-28657405790 / 1000000000000)))) (orderedInterval (-885669448 / 1000000000000) (-885669388 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (2283997664914651 / 4000000000000) 0 (IntervalRat.scale (989 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (491907690 / 1000000000000) (491907691 / 1000000000000), orderedInterval (33386398789 / 1000000000000) (33386398790 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3913668928324423 / 4000000000000) 0 (IntervalRat.scale (989 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-21104585184 / 1000000000000) (-21104578516 / 1000000000000), orderedInterval (14337660934 / 1000000000000) (14337667603 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2882790819142357 / 4000000000000) 0 (IntervalRat.scale (989 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-26259910109 / 1000000000000) (-26259846345 / 1000000000000), orderedInterval (13937840364 / 1000000000000) (13937904128 / 1000000000000)))) (orderedInterval (16299410 / 1000000000000) (16301185 / 1000000000000))) = true
  rfl'

theorem compactCertificate623_chunkChecks0_1 :
    compactCertificate623.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (4422942459494011 / 4000000000000) 0 (IntervalRat.scale (989 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (15093001598 / 1000000000000) (15093001599 / 1000000000000), orderedInterval (18646446295 / 1000000000000) (18646446296 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2553587019598819 / 4000000000000) 0 (IntervalRat.scale (989 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-31303401002 / 1000000000000) (-31303400764 / 1000000000000), orderedInterval (-4136407070 / 1000000000000) (-4136406832 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (4531384977449471 / 4000000000000) 0 (IntervalRat.scale (989 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (11018602208 / 1000000000000) (11018602212 / 1000000000000), orderedInterval (-20994272204 / 1000000000000) (-20994272200 / 1000000000000)))) (orderedInterval (-3434809442 / 1000000000000) (-3434809228 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (4233807641732699 / 4000000000000) 0 (IntervalRat.scale (989 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-12195779548 / 1000000000000) (-12195779547 / 1000000000000), orderedInterval (-21271600070 / 1000000000000) (-21271600069 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (3021444908206667 / 4000000000000) 0 (IntervalRat.scale (989 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (24067579398 / 1000000000000) (24067600299 / 1000000000000), orderedInterval (-16250250783 / 1000000000000) (-16250229882 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (3425996497370493 / 4000000000000) 0 (IntervalRat.scale (989 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (9869408354 / 1000000000000) (9869408360 / 1000000000000), orderedInterval (-25419855214 / 1000000000000) (-25419855209 / 1000000000000)))) (orderedInterval (2446125822 / 1000000000000) (2446127858 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2856238701417517 / 4000000000000) 0 (IntervalRat.scale (989 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-29596835081 / 1000000000000) (-29596827154 / 1000000000000), orderedInterval (3967514840 / 1000000000000) (3967522767 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2523573513731857 / 4000000000000) 0 (IntervalRat.scale (989 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-6884373004 / 1000000000000) (-6884373003 / 1000000000000), orderedInterval (-31005547458 / 1000000000000) (-31005547457 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (731429965281843 / 800000000000) 0 (IntervalRat.scale (989 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-20156080961 / 1000000000000) (-20156080960 / 1000000000000), orderedInterval (-17019359784 / 1000000000000) (-17019359783 / 1000000000000)))) (orderedInterval (-463880007 / 1000000000000) (-463879868 / 1000000000000))) = true
  rfl'

theorem compactCertificate623_chunkChecks0_2 :
    compactCertificate623.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (2023173777019721 / 4000000000000) 0 (IntervalRat.scale (989 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-25005490102 / 1000000000000) (-25005490101 / 1000000000000), orderedInterval (-25142344961 / 1000000000000) (-25142344960 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1715066816815681 / 4000000000000) 0 (IntervalRat.scale (989 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (28856663668 / 1000000000000) (28856692495 / 1000000000000), orderedInterval (-25569161559 / 1000000000000) (-25569132733 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (1073209180857643 / 4000000000000) 0 (IntervalRat.scale (989 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-43182697908 / 1000000000000) (-43182671866 / 1000000000000), orderedInterval (22619844293 / 1000000000000) (22619870336 / 1000000000000)))) (orderedInterval (959076855 / 1000000000000) (959079459 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (577175466797781 / 4000000000000) 0 (IntervalRat.scale (989 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (35571283712 / 1000000000000) (35571283713 / 1000000000000), orderedInterval (55971857527 / 1000000000000) (55971857528 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1567143668976343 / 4000000000000) 0 (IntervalRat.scale (989 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (5149045867 / 1000000000000) (5149045872 / 1000000000000), orderedInterval (-39986641946 / 1000000000000) (-39986641941 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (2139800700753911 / 4000000000000) 0 (IntervalRat.scale (989 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (34345531237 / 1000000000000) (34345533218 / 1000000000000), orderedInterval (-3262928071 / 1000000000000) (-3262926090 / 1000000000000)))) (orderedInterval (-3405846494 / 1000000000000) (-3405846283 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (904790819142357 / 4000000000000) 0 (IntervalRat.scale (989 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (37605840816 / 1000000000000) (37605840817 / 1000000000000), orderedInterval (37336658947 / 1000000000000) (37336658948 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3677924447329397 / 4000000000000) 0 (IntervalRat.scale (989 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (5749274711 / 1000000000000) (5749274712 / 1000000000000), orderedInterval (-25680245528 / 1000000000000) (-25680245527 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2456683080851323 / 4000000000000) 0 (IntervalRat.scale (989 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-23010143843 / 1000000000000) (-23010136717 / 1000000000000), orderedInterval (22537280505 / 1000000000000) (22537287631 / 1000000000000)))) (orderedInterval (4076011135 / 1000000000000) (4076012609 / 1000000000000))) = true
  rfl'

theorem compactCertificate623_chunkChecks0 :
    compactCertificate623.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate623.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate623_chunkChecks0_0
    compactCertificate623_chunkChecks0_1 compactCertificate623_chunkChecks0_2

theorem compactCertificate623_chunkChecks1_0 :
    compactCertificate623.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (989 / 2) 1 (IntervalRat.scale (989 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-31754153333 / 1000000000000) (-31754079079 / 1000000000000), orderedInterval (16737655808 / 1000000000000) (16737730062 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1456985847474089 / 4000000000000) 1 (IntervalRat.scale (989 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (23838655520 / 1000000000000) (23838655521 / 1000000000000), orderedInterval (34310996662 / 1000000000000) (34310996663 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (471159287409737 / 800000000000) 1 (IntervalRat.scale (989 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-25447110057 / 1000000000000) (-25447090657 / 1000000000000), orderedInterval (20839540488 / 1000000000000) (20839559888 / 1000000000000)))) (orderedInterval (8326177798 / 1000000000000) (8326208625 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (425144836518523 / 4000000000000) 1 (IntervalRat.scale (989 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (19617839486 / 1000000000000) (19617839487 / 1000000000000), orderedInterval (74773409983 / 1000000000000) (74773409984 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (1141998832456831 / 4000000000000) 1 (IntervalRat.scale (989 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-18377355587 / 1000000000000) (-18377355586 / 1000000000000), orderedInterval (-43466310352 / 1000000000000) (-43466310351 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (3100748980530627 / 4000000000000) 1 (IntervalRat.scale (989 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (25888853 / 1000000000000) (25888854 / 1000000000000), orderedInterval (-28657405791 / 1000000000000) (-28657405790 / 1000000000000)))) (orderedInterval (2102984358 / 1000000000000) (2102984425 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (2283997664914651 / 4000000000000) 1 (IntervalRat.scale (989 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (491907690 / 1000000000000) (491907691 / 1000000000000), orderedInterval (33386398789 / 1000000000000) (33386398790 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3913668928324423 / 4000000000000) 1 (IntervalRat.scale (989 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-21104585184 / 1000000000000) (-21104578516 / 1000000000000), orderedInterval (14337660934 / 1000000000000) (14337667603 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2882790819142357 / 4000000000000) 1 (IntervalRat.scale (989 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-26259910109 / 1000000000000) (-26259846345 / 1000000000000), orderedInterval (13937840364 / 1000000000000) (13937904128 / 1000000000000)))) (orderedInterval (-384063459 / 1000000000000) (-384060758 / 1000000000000))) = true
  rfl'

theorem compactCertificate623_chunkChecks1_1 :
    compactCertificate623.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (4422942459494011 / 4000000000000) 1 (IntervalRat.scale (989 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (15093001598 / 1000000000000) (15093001599 / 1000000000000), orderedInterval (18646446295 / 1000000000000) (18646446296 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2553587019598819 / 4000000000000) 1 (IntervalRat.scale (989 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-31303401002 / 1000000000000) (-31303400764 / 1000000000000), orderedInterval (-4136407070 / 1000000000000) (-4136406832 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (4531384977449471 / 4000000000000) 1 (IntervalRat.scale (989 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (11018602208 / 1000000000000) (11018602212 / 1000000000000), orderedInterval (-20994272204 / 1000000000000) (-20994272200 / 1000000000000)))) (orderedInterval (-14641379944 / 1000000000000) (-14641379514 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (4233807641732699 / 4000000000000) 1 (IntervalRat.scale (989 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-12195779548 / 1000000000000) (-12195779547 / 1000000000000), orderedInterval (-21271600070 / 1000000000000) (-21271600069 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (3021444908206667 / 4000000000000) 1 (IntervalRat.scale (989 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (24067579398 / 1000000000000) (24067600299 / 1000000000000), orderedInterval (-16250250783 / 1000000000000) (-16250229882 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (3425996497370493 / 4000000000000) 1 (IntervalRat.scale (989 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (9869408354 / 1000000000000) (9869408360 / 1000000000000), orderedInterval (-25419855214 / 1000000000000) (-25419855209 / 1000000000000)))) (orderedInterval (-1302522306 / 1000000000000) (-1302519191 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2856238701417517 / 4000000000000) 1 (IntervalRat.scale (989 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-29596835081 / 1000000000000) (-29596827154 / 1000000000000), orderedInterval (3967514840 / 1000000000000) (3967522767 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2523573513731857 / 4000000000000) 1 (IntervalRat.scale (989 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-6884373004 / 1000000000000) (-6884373003 / 1000000000000), orderedInterval (-31005547458 / 1000000000000) (-31005547457 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (731429965281843 / 800000000000) 1 (IntervalRat.scale (989 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-20156080961 / 1000000000000) (-20156080960 / 1000000000000), orderedInterval (-17019359784 / 1000000000000) (-17019359783 / 1000000000000)))) (orderedInterval (1524215753 / 1000000000000) (1524215954 / 1000000000000))) = true
  rfl'

theorem compactCertificate623_chunkChecks1_2 :
    compactCertificate623.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (2023173777019721 / 4000000000000) 1 (IntervalRat.scale (989 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-25005490102 / 1000000000000) (-25005490101 / 1000000000000), orderedInterval (-25142344961 / 1000000000000) (-25142344960 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1715066816815681 / 4000000000000) 1 (IntervalRat.scale (989 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (28856663668 / 1000000000000) (28856692495 / 1000000000000), orderedInterval (-25569161559 / 1000000000000) (-25569132733 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (1073209180857643 / 4000000000000) 1 (IntervalRat.scale (989 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-43182697908 / 1000000000000) (-43182671866 / 1000000000000), orderedInterval (22619844293 / 1000000000000) (22619870336 / 1000000000000)))) (orderedInterval (5766265390 / 1000000000000) (5766267380 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (577175466797781 / 4000000000000) 1 (IntervalRat.scale (989 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (35571283712 / 1000000000000) (35571283713 / 1000000000000), orderedInterval (55971857527 / 1000000000000) (55971857528 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1567143668976343 / 4000000000000) 1 (IntervalRat.scale (989 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (5149045867 / 1000000000000) (5149045872 / 1000000000000), orderedInterval (-39986641946 / 1000000000000) (-39986641941 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (2139800700753911 / 4000000000000) 1 (IntervalRat.scale (989 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (34345531237 / 1000000000000) (34345533218 / 1000000000000), orderedInterval (-3262928071 / 1000000000000) (-3262926090 / 1000000000000)))) (orderedInterval (687682008 / 1000000000000) (687682225 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (904790819142357 / 4000000000000) 1 (IntervalRat.scale (989 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (37605840816 / 1000000000000) (37605840817 / 1000000000000), orderedInterval (37336658947 / 1000000000000) (37336658948 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3677924447329397 / 4000000000000) 1 (IntervalRat.scale (989 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (5749274711 / 1000000000000) (5749274712 / 1000000000000), orderedInterval (-25680245528 / 1000000000000) (-25680245527 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2456683080851323 / 4000000000000) 1 (IntervalRat.scale (989 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-23010143843 / 1000000000000) (-23010136717 / 1000000000000), orderedInterval (22537280505 / 1000000000000) (22537287631 / 1000000000000)))) (orderedInterval (-1262015594 / 1000000000000) (-1262013741 / 1000000000000))) = true
  rfl'

theorem compactCertificate623_chunkChecks1 :
    compactCertificate623.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate623.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate623_chunkChecks1_0
    compactCertificate623_chunkChecks1_1 compactCertificate623_chunkChecks1_2

theorem compactCertificate623_chunkChecks2_0 :
    compactCertificate623.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (989 / 2) 2 (IntervalRat.scale (989 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-31754153333 / 1000000000000) (-31754079079 / 1000000000000), orderedInterval (16737655808 / 1000000000000) (16737730062 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1456985847474089 / 4000000000000) 2 (IntervalRat.scale (989 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (23838655520 / 1000000000000) (23838655521 / 1000000000000), orderedInterval (34310996662 / 1000000000000) (34310996663 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (471159287409737 / 800000000000) 2 (IntervalRat.scale (989 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-25447110057 / 1000000000000) (-25447090657 / 1000000000000), orderedInterval (20839540488 / 1000000000000) (20839559888 / 1000000000000)))) (orderedInterval (14567010162 / 1000000000000) (14567041315 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (425144836518523 / 4000000000000) 2 (IntervalRat.scale (989 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (19617839486 / 1000000000000) (19617839487 / 1000000000000), orderedInterval (74773409983 / 1000000000000) (74773409984 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (1141998832456831 / 4000000000000) 2 (IntervalRat.scale (989 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-18377355587 / 1000000000000) (-18377355586 / 1000000000000), orderedInterval (-43466310352 / 1000000000000) (-43466310351 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (3100748980530627 / 4000000000000) 2 (IntervalRat.scale (989 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (25888853 / 1000000000000) (25888854 / 1000000000000), orderedInterval (-28657405791 / 1000000000000) (-28657405790 / 1000000000000)))) (orderedInterval (233765760 / 1000000000000) (233765854 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (2283997664914651 / 4000000000000) 2 (IntervalRat.scale (989 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (491907690 / 1000000000000) (491907691 / 1000000000000), orderedInterval (33386398789 / 1000000000000) (33386398790 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3913668928324423 / 4000000000000) 2 (IntervalRat.scale (989 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-21104585184 / 1000000000000) (-21104578516 / 1000000000000), orderedInterval (14337660934 / 1000000000000) (14337667603 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2882790819142357 / 4000000000000) 2 (IntervalRat.scale (989 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-26259910109 / 1000000000000) (-26259846345 / 1000000000000), orderedInterval (13937840364 / 1000000000000) (13937904128 / 1000000000000)))) (orderedInterval (-1199543828 / 1000000000000) (-1199539658 / 1000000000000))) = true
  rfl'

theorem compactCertificate623_chunkChecks2_1 :
    compactCertificate623.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (4422942459494011 / 4000000000000) 2 (IntervalRat.scale (989 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (15093001598 / 1000000000000) (15093001599 / 1000000000000), orderedInterval (18646446295 / 1000000000000) (18646446296 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2553587019598819 / 4000000000000) 2 (IntervalRat.scale (989 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-31303401002 / 1000000000000) (-31303400764 / 1000000000000), orderedInterval (-4136407070 / 1000000000000) (-4136406832 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (4531384977449471 / 4000000000000) 2 (IntervalRat.scale (989 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (11018602208 / 1000000000000) (11018602212 / 1000000000000), orderedInterval (-20994272204 / 1000000000000) (-20994272200 / 1000000000000)))) (orderedInterval (9083822454 / 1000000000000) (9083823357 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (4233807641732699 / 4000000000000) 2 (IntervalRat.scale (989 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-12195779548 / 1000000000000) (-12195779547 / 1000000000000), orderedInterval (-21271600070 / 1000000000000) (-21271600069 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (3021444908206667 / 4000000000000) 2 (IntervalRat.scale (989 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (24067579398 / 1000000000000) (24067600299 / 1000000000000), orderedInterval (-16250250783 / 1000000000000) (-16250229882 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (3425996497370493 / 4000000000000) 2 (IntervalRat.scale (989 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (9869408354 / 1000000000000) (9869408360 / 1000000000000), orderedInterval (-25419855214 / 1000000000000) (-25419855209 / 1000000000000)))) (orderedInterval (-6166687800 / 1000000000000) (-6166683023 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2856238701417517 / 4000000000000) 2 (IntervalRat.scale (989 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-29596835081 / 1000000000000) (-29596827154 / 1000000000000), orderedInterval (3967514840 / 1000000000000) (3967522767 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2523573513731857 / 4000000000000) 2 (IntervalRat.scale (989 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-6884373004 / 1000000000000) (-6884373003 / 1000000000000), orderedInterval (-31005547458 / 1000000000000) (-31005547457 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (731429965281843 / 800000000000) 2 (IntervalRat.scale (989 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-20156080961 / 1000000000000) (-20156080960 / 1000000000000), orderedInterval (-17019359784 / 1000000000000) (-17019359783 / 1000000000000)))) (orderedInterval (1832487660 / 1000000000000) (1832487953 / 1000000000000))) = true
  rfl'

theorem compactCertificate623_chunkChecks2_2 :
    compactCertificate623.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (2023173777019721 / 4000000000000) 2 (IntervalRat.scale (989 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-25005490102 / 1000000000000) (-25005490101 / 1000000000000), orderedInterval (-25142344961 / 1000000000000) (-25142344960 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1715066816815681 / 4000000000000) 2 (IntervalRat.scale (989 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (28856663668 / 1000000000000) (28856692495 / 1000000000000), orderedInterval (-25569161559 / 1000000000000) (-25569132733 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (1073209180857643 / 4000000000000) 2 (IntervalRat.scale (989 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-43182697908 / 1000000000000) (-43182671866 / 1000000000000), orderedInterval (22619844293 / 1000000000000) (22619870336 / 1000000000000)))) (orderedInterval (-2552778712 / 1000000000000) (-2552777122 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (577175466797781 / 4000000000000) 2 (IntervalRat.scale (989 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (35571283712 / 1000000000000) (35571283713 / 1000000000000), orderedInterval (55971857527 / 1000000000000) (55971857528 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1567143668976343 / 4000000000000) 2 (IntervalRat.scale (989 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (5149045867 / 1000000000000) (5149045872 / 1000000000000), orderedInterval (-39986641946 / 1000000000000) (-39986641941 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (2139800700753911 / 4000000000000) 2 (IntervalRat.scale (989 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (34345531237 / 1000000000000) (34345533218 / 1000000000000), orderedInterval (-3262928071 / 1000000000000) (-3262926090 / 1000000000000)))) (orderedInterval (3208307464 / 1000000000000) (3208307695 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (904790819142357 / 4000000000000) 2 (IntervalRat.scale (989 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (37605840816 / 1000000000000) (37605840817 / 1000000000000), orderedInterval (37336658947 / 1000000000000) (37336658948 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3677924447329397 / 4000000000000) 2 (IntervalRat.scale (989 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (5749274711 / 1000000000000) (5749274712 / 1000000000000), orderedInterval (-25680245528 / 1000000000000) (-25680245527 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2456683080851323 / 4000000000000) 2 (IntervalRat.scale (989 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-23010143843 / 1000000000000) (-23010136717 / 1000000000000), orderedInterval (22537280505 / 1000000000000) (22537287631 / 1000000000000)))) (orderedInterval (-5086573342 / 1000000000000) (-5086570992 / 1000000000000))) = true
  rfl'

theorem compactCertificate623_chunkChecks2 :
    compactCertificate623.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate623.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate623_chunkChecks2_0
    compactCertificate623_chunkChecks2_1 compactCertificate623_chunkChecks2_2

theorem compactCertificate623_chunkChecks3_0 :
    compactCertificate623.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (989 / 2) 3 (IntervalRat.scale (989 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-31754153333 / 1000000000000) (-31754079079 / 1000000000000), orderedInterval (16737655808 / 1000000000000) (16737730062 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1456985847474089 / 4000000000000) 3 (IntervalRat.scale (989 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (23838655520 / 1000000000000) (23838655521 / 1000000000000), orderedInterval (34310996662 / 1000000000000) (34310996663 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (471159287409737 / 800000000000) 3 (IntervalRat.scale (989 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-25447110057 / 1000000000000) (-25447090657 / 1000000000000), orderedInterval (20839540488 / 1000000000000) (20839559888 / 1000000000000)))) (orderedInterval (-8857407462 / 1000000000000) (-8857375993 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (425144836518523 / 4000000000000) 3 (IntervalRat.scale (989 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (19617839486 / 1000000000000) (19617839487 / 1000000000000), orderedInterval (74773409983 / 1000000000000) (74773409984 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (1141998832456831 / 4000000000000) 3 (IntervalRat.scale (989 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-18377355587 / 1000000000000) (-18377355586 / 1000000000000), orderedInterval (-43466310352 / 1000000000000) (-43466310351 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (3100748980530627 / 4000000000000) 3 (IntervalRat.scale (989 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (25888853 / 1000000000000) (25888854 / 1000000000000), orderedInterval (-28657405791 / 1000000000000) (-28657405790 / 1000000000000)))) (orderedInterval (-7535078062 / 1000000000000) (-7535077922 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (2283997664914651 / 4000000000000) 3 (IntervalRat.scale (989 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (491907690 / 1000000000000) (491907691 / 1000000000000), orderedInterval (33386398789 / 1000000000000) (33386398790 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3913668928324423 / 4000000000000) 3 (IntervalRat.scale (989 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-21104585184 / 1000000000000) (-21104578516 / 1000000000000), orderedInterval (14337660934 / 1000000000000) (14337667603 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2882790819142357 / 4000000000000) 3 (IntervalRat.scale (989 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-26259910109 / 1000000000000) (-26259846345 / 1000000000000), orderedInterval (13937840364 / 1000000000000) (13937904128 / 1000000000000)))) (orderedInterval (2385116136 / 1000000000000) (2385122664 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate623_chunkChecks3_1 :
    compactCertificate623.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (4422942459494011 / 4000000000000) 3 (IntervalRat.scale (989 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (15093001598 / 1000000000000) (15093001599 / 1000000000000), orderedInterval (18646446295 / 1000000000000) (18646446296 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2553587019598819 / 4000000000000) 3 (IntervalRat.scale (989 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-31303401002 / 1000000000000) (-31303400764 / 1000000000000), orderedInterval (-4136407070 / 1000000000000) (-4136406832 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (4531384977449471 / 4000000000000) 3 (IntervalRat.scale (989 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (11018602208 / 1000000000000) (11018602212 / 1000000000000), orderedInterval (-20994272204 / 1000000000000) (-20994272200 / 1000000000000)))) (orderedInterval (73566492145 / 1000000000000) (73566494099 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (4233807641732699 / 4000000000000) 3 (IntervalRat.scale (989 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-12195779548 / 1000000000000) (-12195779547 / 1000000000000), orderedInterval (-21271600070 / 1000000000000) (-21271600069 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (3021444908206667 / 4000000000000) 3 (IntervalRat.scale (989 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (24067579398 / 1000000000000) (24067600299 / 1000000000000), orderedInterval (-16250250783 / 1000000000000) (-16250229882 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (3425996497370493 / 4000000000000) 3 (IntervalRat.scale (989 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (9869408354 / 1000000000000) (9869408360 / 1000000000000), orderedInterval (-25419855214 / 1000000000000) (-25419855209 / 1000000000000)))) (orderedInterval (1055192236 / 1000000000000) (1055199559 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2856238701417517 / 4000000000000) 3 (IntervalRat.scale (989 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-29596835081 / 1000000000000) (-29596827154 / 1000000000000), orderedInterval (3967514840 / 1000000000000) (3967522767 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2523573513731857 / 4000000000000) 3 (IntervalRat.scale (989 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-6884373004 / 1000000000000) (-6884373003 / 1000000000000), orderedInterval (-31005547458 / 1000000000000) (-31005547457 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (731429965281843 / 800000000000) 3 (IntervalRat.scale (989 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-20156080961 / 1000000000000) (-20156080960 / 1000000000000), orderedInterval (-17019359784 / 1000000000000) (-17019359783 / 1000000000000)))) (orderedInterval (-1072163340 / 1000000000000) (-1072162906 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate623_chunkChecks3_2 :
    compactCertificate623.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (2023173777019721 / 4000000000000) 3 (IntervalRat.scale (989 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-25005490102 / 1000000000000) (-25005490101 / 1000000000000), orderedInterval (-25142344961 / 1000000000000) (-25142344960 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1715066816815681 / 4000000000000) 3 (IntervalRat.scale (989 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (28856663668 / 1000000000000) (28856692495 / 1000000000000), orderedInterval (-25569161559 / 1000000000000) (-25569132733 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (1073209180857643 / 4000000000000) 3 (IntervalRat.scale (989 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-43182697908 / 1000000000000) (-43182671866 / 1000000000000), orderedInterval (22619844293 / 1000000000000) (22619870336 / 1000000000000)))) (orderedInterval (-5357679101 / 1000000000000) (-5357677793 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (577175466797781 / 4000000000000) 3 (IntervalRat.scale (989 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (35571283712 / 1000000000000) (35571283713 / 1000000000000), orderedInterval (55971857527 / 1000000000000) (55971857528 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1567143668976343 / 4000000000000) 3 (IntervalRat.scale (989 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (5149045867 / 1000000000000) (5149045872 / 1000000000000), orderedInterval (-39986641946 / 1000000000000) (-39986641941 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (2139800700753911 / 4000000000000) 3 (IntervalRat.scale (989 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (34345531237 / 1000000000000) (34345533218 / 1000000000000), orderedInterval (-3262928071 / 1000000000000) (-3262926090 / 1000000000000)))) (orderedInterval (-748563857 / 1000000000000) (-748563609 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (904790819142357 / 4000000000000) 3 (IntervalRat.scale (989 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (37605840816 / 1000000000000) (37605840817 / 1000000000000), orderedInterval (37336658947 / 1000000000000) (37336658948 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3677924447329397 / 4000000000000) 3 (IntervalRat.scale (989 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (5749274711 / 1000000000000) (5749274712 / 1000000000000), orderedInterval (-25680245528 / 1000000000000) (-25680245527 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2456683080851323 / 4000000000000) 3 (IntervalRat.scale (989 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-23010143843 / 1000000000000) (-23010136717 / 1000000000000), orderedInterval (22537280505 / 1000000000000) (22537287631 / 1000000000000)))) (orderedInterval (-5348648488 / 1000000000000) (-5348645484 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate623_chunkChecks3 :
    compactCertificate623.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate623.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate623_chunkChecks3_0
    compactCertificate623_chunkChecks3_1 compactCertificate623_chunkChecks3_2

theorem compactCertificate623_chunkChecks4_0 :
    compactCertificate623.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (989 / 2) 4 (IntervalRat.scale (989 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-31754153333 / 1000000000000) (-31754079079 / 1000000000000), orderedInterval (16737655808 / 1000000000000) (16737730062 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1456985847474089 / 4000000000000) 4 (IntervalRat.scale (989 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (23838655520 / 1000000000000) (23838655521 / 1000000000000), orderedInterval (34310996662 / 1000000000000) (34310996663 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (471159287409737 / 800000000000) 4 (IntervalRat.scale (989 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-25447110057 / 1000000000000) (-25447090657 / 1000000000000), orderedInterval (20839540488 / 1000000000000) (20839559888 / 1000000000000)))) (orderedInterval (-15489533898 / 1000000000000) (-15489501989 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (425144836518523 / 4000000000000) 4 (IntervalRat.scale (989 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (19617839486 / 1000000000000) (19617839487 / 1000000000000), orderedInterval (74773409983 / 1000000000000) (74773409984 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (1141998832456831 / 4000000000000) 4 (IntervalRat.scale (989 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-18377355587 / 1000000000000) (-18377355586 / 1000000000000), orderedInterval (-43466310352 / 1000000000000) (-43466310351 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (3100748980530627 / 4000000000000) 4 (IntervalRat.scale (989 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (25888853 / 1000000000000) (25888854 / 1000000000000), orderedInterval (-28657405791 / 1000000000000) (-28657405790 / 1000000000000)))) (orderedInterval (-55646504 / 1000000000000) (-55646289 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (2283997664914651 / 4000000000000) 4 (IntervalRat.scale (989 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (491907690 / 1000000000000) (491907691 / 1000000000000), orderedInterval (33386398789 / 1000000000000) (33386398790 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3913668928324423 / 4000000000000) 4 (IntervalRat.scale (989 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-21104585184 / 1000000000000) (-21104578516 / 1000000000000), orderedInterval (14337660934 / 1000000000000) (14337667603 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2882790819142357 / 4000000000000) 4 (IntervalRat.scale (989 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-26259910109 / 1000000000000) (-26259846345 / 1000000000000), orderedInterval (13937840364 / 1000000000000) (13937904128 / 1000000000000)))) (orderedInterval (7103458343 / 1000000000000) (7103468762 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate623_chunkChecks4_1 :
    compactCertificate623.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (4422942459494011 / 4000000000000) 4 (IntervalRat.scale (989 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (15093001598 / 1000000000000) (15093001599 / 1000000000000), orderedInterval (18646446295 / 1000000000000) (18646446296 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2553587019598819 / 4000000000000) 4 (IntervalRat.scale (989 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-31303401002 / 1000000000000) (-31303400764 / 1000000000000), orderedInterval (-4136407070 / 1000000000000) (-4136406832 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (4531384977449471 / 4000000000000) 4 (IntervalRat.scale (989 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (11018602208 / 1000000000000) (11018602212 / 1000000000000), orderedInterval (-20994272204 / 1000000000000) (-20994272200 / 1000000000000)))) (orderedInterval (-30643203033 / 1000000000000) (-30643198728 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (4233807641732699 / 4000000000000) 4 (IntervalRat.scale (989 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-12195779548 / 1000000000000) (-12195779547 / 1000000000000), orderedInterval (-21271600070 / 1000000000000) (-21271600069 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (3021444908206667 / 4000000000000) 4 (IntervalRat.scale (989 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (24067579398 / 1000000000000) (24067600299 / 1000000000000), orderedInterval (-16250250783 / 1000000000000) (-16250229882 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (3425996497370493 / 4000000000000) 4 (IntervalRat.scale (989 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (9869408354 / 1000000000000) (9869408360 / 1000000000000), orderedInterval (-25419855214 / 1000000000000) (-25419855209 / 1000000000000)))) (orderedInterval (16558682349 / 1000000000000) (16558693604 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2856238701417517 / 4000000000000) 4 (IntervalRat.scale (989 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-29596835081 / 1000000000000) (-29596827154 / 1000000000000), orderedInterval (3967514840 / 1000000000000) (3967522767 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2523573513731857 / 4000000000000) 4 (IntervalRat.scale (989 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-6884373004 / 1000000000000) (-6884373003 / 1000000000000), orderedInterval (-31005547458 / 1000000000000) (-31005547457 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (731429965281843 / 800000000000) 4 (IntervalRat.scale (989 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-20156080961 / 1000000000000) (-20156080960 / 1000000000000), orderedInterval (-17019359784 / 1000000000000) (-17019359783 / 1000000000000)))) (orderedInterval (-6468679826 / 1000000000000) (-6468679178 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate623_chunkChecks4_2 :
    compactCertificate623.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (2023173777019721 / 4000000000000) 4 (IntervalRat.scale (989 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-25005490102 / 1000000000000) (-25005490101 / 1000000000000), orderedInterval (-25142344961 / 1000000000000) (-25142344960 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1715066816815681 / 4000000000000) 4 (IntervalRat.scale (989 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (28856663668 / 1000000000000) (28856692495 / 1000000000000), orderedInterval (-25569161559 / 1000000000000) (-25569132733 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (1073209180857643 / 4000000000000) 4 (IntervalRat.scale (989 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-43182697908 / 1000000000000) (-43182671866 / 1000000000000), orderedInterval (22619844293 / 1000000000000) (22619870336 / 1000000000000)))) (orderedInterval (3352792940 / 1000000000000) (3352794046 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (577175466797781 / 4000000000000) 4 (IntervalRat.scale (989 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (35571283712 / 1000000000000) (35571283713 / 1000000000000), orderedInterval (55971857527 / 1000000000000) (55971857528 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1567143668976343 / 4000000000000) 4 (IntervalRat.scale (989 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (5149045867 / 1000000000000) (5149045872 / 1000000000000), orderedInterval (-39986641946 / 1000000000000) (-39986641941 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (2139800700753911 / 4000000000000) 4 (IntervalRat.scale (989 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (34345531237 / 1000000000000) (34345533218 / 1000000000000), orderedInterval (-3262928071 / 1000000000000) (-3262926090 / 1000000000000)))) (orderedInterval (-3652768793 / 1000000000000) (-3652768527 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (904790819142357 / 4000000000000) 4 (IntervalRat.scale (989 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (37605840816 / 1000000000000) (37605840817 / 1000000000000), orderedInterval (37336658947 / 1000000000000) (37336658948 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3677924447329397 / 4000000000000) 4 (IntervalRat.scale (989 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (5749274711 / 1000000000000) (5749274712 / 1000000000000), orderedInterval (-25680245528 / 1000000000000) (-25680245527 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2456683080851323 / 4000000000000) 4 (IntervalRat.scale (989 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-23010143843 / 1000000000000) (-23010136717 / 1000000000000), orderedInterval (22537280505 / 1000000000000) (22537287631 / 1000000000000)))) (orderedInterval (4710321479 / 1000000000000) (4710325375 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate623_chunkChecks4 :
    compactCertificate623.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate623.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate623_chunkChecks4_0
    compactCertificate623_chunkChecks4_1 compactCertificate623_chunkChecks4_2

theorem compactCertificate623_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate623.chunkCheck r b = true :=
  compactCertificate623.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate623_chunkChecks0
    · exact compactCertificate623_chunkChecks1
    · exact compactCertificate623_chunkChecks2
    · exact compactCertificate623_chunkChecks3
    · exact compactCertificate623_chunkChecks4)

theorem compactCertificate623_coefficient0 :
    compactCertificate623.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate623_coefficient1 :
    compactCertificate623.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate623_coefficient2 :
    compactCertificate623.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate623_coefficient3 :
    compactCertificate623.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate623_coefficient4 :
    compactCertificate623.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate623_coefficients : ∀ r : Fin 5,
    compactCertificate623.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate623_coefficient0
  · exact compactCertificate623_coefficient1
  · exact compactCertificate623_coefficient2
  · exact compactCertificate623_coefficient3
  · exact compactCertificate623_coefficient4

theorem compactCertificate623_lower : (1 : ℚ) ≤ compactCertificate623.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate623, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate623_proves {t : ℝ} (ht : t ∈ compactCertificate623.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate623.proves compactCertificate623_states compactCertificate623_chunks
    compactCertificate623_coefficients compactCertificate623_lower ht

end Erdos232
