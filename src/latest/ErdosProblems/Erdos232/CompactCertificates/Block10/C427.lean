/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate427 : CompactCertificate where
  left := 298
  right := 299
  center := 597 / 2
  grid := fun i =>
    match i.val with
    | 0 => 95
    | 1 => 70
    | 2 => 113
    | 3 => 20
    | 4 => 55
    | 5 => 149
    | 6 => 110
    | 7 => 188
    | 8 => 139
    | 9 => 213
    | 10 => 123
    | 11 => 218
    | 12 => 203
    | 13 => 145
    | 14 => 165
    | 15 => 137
    | 16 => 121
    | 17 => 176
    | 18 => 97
    | 19 => 82
    | 20 => 52
    | 21 => 28
    | 22 => 75
    | 23 => 103
    | 24 => 43
    | 25 => 177
    | _ => 118
  point := fun i =>
    match i.val with
    | 0 => 597 / 2
    | 1 => 879494995896897 / 4000000000000
    | 2 => 284410611308001 / 800000000000
    | 3 => 256634446310979 / 4000000000000
    | 4 => 689356221412263 / 4000000000000
    | 5 => 1871736240016971 / 4000000000000
    | 6 => 1378712442825123 / 4000000000000
    | 7 => 2362447270181679 / 4000000000000
    | 8 => 1740167966661261 / 4000000000000
    | 9 => 2669865165134403 / 4000000000000
    | 10 => 1541447371790187 / 4000000000000
    | 11 => 2735325411058983 / 4000000000000
    | 12 => 2555695816091427 / 4000000000000
    | 13 => 1823865126591891 / 4000000000000
    | 14 => 2068068664236789 / 4000000000000
    | 15 => 1724140045243941 / 4000000000000
    | 16 => 1523330017894761 / 4000000000000
    | 17 => 441520413825339 / 800000000000
    | 18 => 1221268700587233 / 4000000000000
    | 19 => 1035283002668313 / 4000000000000
    | 20 => 647832033338739 / 4000000000000
    | 21 => 348406222121613 / 4000000000000
    | 22 => 945990667723839 / 4000000000000
    | 23 => 1291669381547103 / 4000000000000
    | 24 => 546167966661261 / 4000000000000
    | 25 => 2220142462139181 / 4000000000000
    | _ => 1482952274285379 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-34193121869 / 1000000000000) (-34193121868 / 1000000000000), orderedInterval (-30983983023 / 1000000000000) (-30983983022 / 1000000000000))
    | 1 => (orderedInterval (36563510072 / 1000000000000) (36563510073 / 1000000000000), orderedInterval (39394671820 / 1000000000000) (39394671821 / 1000000000000))
    | 2 => (orderedInterval (-40755779463 / 1000000000000) (-40755779459 / 1000000000000), orderedInterval (-11329999335 / 1000000000000) (-11329999331 / 1000000000000))
    | 3 => (orderedInterval (85467036684 / 1000000000000) (85467053943 / 1000000000000), orderedInterval (-51830806339 / 1000000000000) (-51830789080 / 1000000000000))
    | 4 => (orderedInterval (-20046952242 / 1000000000000) (-20046952241 / 1000000000000), orderedInterval (-57318906124 / 1000000000000) (-57318906123 / 1000000000000))
    | 5 => (orderedInterval (-21487943031 / 1000000000000) (-21487943030 / 1000000000000), orderedInterval (-29956347490 / 1000000000000) (-29956347489 / 1000000000000))
    | 6 => (orderedInterval (-4805283497 / 1000000000000) (-4805283492 / 1000000000000), orderedInterval (42714219697 / 1000000000000) (42714219703 / 1000000000000))
    | 7 => (orderedInterval (23033192563 / 1000000000000) (23033192564 / 1000000000000), orderedInterval (23376458593 / 1000000000000) (23376458594 / 1000000000000))
    | 8 => (orderedInterval (28846999190 / 1000000000000) (28847029291 / 1000000000000), orderedInterval (-25156904338 / 1000000000000) (-25156874237 / 1000000000000))
    | 9 => (orderedInterval (24339532170 / 1000000000000) (24339548637 / 1000000000000), orderedInterval (-19028037064 / 1000000000000) (-19028020597 / 1000000000000))
    | 10 => (orderedInterval (10801284053 / 1000000000000) (10801284098 / 1000000000000), orderedInterval (-39197412313 / 1000000000000) (-39197412268 / 1000000000000))
    | 11 => (orderedInterval (-7567333165 / 1000000000000) (-7567333162 / 1000000000000), orderedInterval (29563880185 / 1000000000000) (29563880189 / 1000000000000))
    | 12 => (orderedInterval (-29134437061 / 1000000000000) (-29134372375 / 1000000000000), orderedInterval (12171011410 / 1000000000000) (12171076095 / 1000000000000))
    | 13 => (orderedInterval (-35096183430 / 1000000000000) (-35096183428 / 1000000000000), orderedInterval (-12785573936 / 1000000000000) (-12785573934 / 1000000000000))
    | 14 => (orderedInterval (18653333891 / 1000000000000) (18653334796 / 1000000000000), orderedInterval (-29739839057 / 1000000000000) (-29739838152 / 1000000000000))
    | 15 => (orderedInterval (-38006095670 / 1000000000000) (-38006095627 / 1000000000000), orderedInterval (-5656071335 / 1000000000000) (-5656071292 / 1000000000000))
    | 16 => (orderedInterval (-40734967419 / 1000000000000) (-40734967345 / 1000000000000), orderedInterval (-3455641612 / 1000000000000) (-3455641538 / 1000000000000))
    | 17 => (orderedInterval (-7895495113 / 1000000000000) (-7895495106 / 1000000000000), orderedInterval (33039957229 / 1000000000000) (33039957237 / 1000000000000))
    | 18 => (orderedInterval (-44724230198 / 1000000000000) (-44724230191 / 1000000000000), orderedInterval (-9138178217 / 1000000000000) (-9138178210 / 1000000000000))
    | 19 => (orderedInterval (45198064892 / 1000000000000) (45198079424 / 1000000000000), orderedInterval (-20503612775 / 1000000000000) (-20503598243 / 1000000000000))
    | 20 => (orderedInterval (-36437768147 / 1000000000000) (-36437756048 / 1000000000000), orderedInterval (51132736062 / 1000000000000) (51132748161 / 1000000000000))
    | 21 => (orderedInterval (-6753259027 / 1000000000000) (-6753259002 / 1000000000000), orderedInterval (85264637413 / 1000000000000) (85264637437 / 1000000000000))
    | 22 => (orderedInterval (-51662322667 / 1000000000000) (-51662322355 / 1000000000000), orderedInterval (4890795506 / 1000000000000) (4890795819 / 1000000000000))
    | 23 => (orderedInterval (-5240990828 / 1000000000000) (-5240990827 / 1000000000000), orderedInterval (-44082675954 / 1000000000000) (-44082675953 / 1000000000000))
    | 24 => (orderedInterval (-53639626748 / 1000000000000) (-53639551219 / 1000000000000), orderedInterval (42448406355 / 1000000000000) (42448481884 / 1000000000000))
    | 25 => (orderedInterval (8086876665 / 1000000000000) (8086876673 / 1000000000000), orderedInterval (-32894849315 / 1000000000000) (-32894849307 / 1000000000000))
    | _ => (orderedInterval (30161595923 / 1000000000000) (30161595924 / 1000000000000), orderedInterval (28374927950 / 1000000000000) (28374927951 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-15603851141 / 1000000000000) (-15603851119 / 1000000000000)
      | 1 => orderedInterval (-131636030 / 1000000000000) (-131635806 / 1000000000000)
      | 2 => orderedInterval (-13260768 / 1000000000000) (-13260023 / 1000000000000)
      | 3 => orderedInterval (-4600298708 / 1000000000000) (-4600295660 / 1000000000000)
      | 4 => orderedInterval (-2887226997 / 1000000000000) (-2887225789 / 1000000000000)
      | 5 => orderedInterval (1690089091 / 1000000000000) (1690089125 / 1000000000000)
      | 6 => orderedInterval (3406615621 / 1000000000000) (3406616914 / 1000000000000)
      | 7 => orderedInterval (1698419292 / 1000000000000) (1698419336 / 1000000000000)
      | _ => orderedInterval (-6640758929 / 1000000000000) (-6640758390 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-12802419840 / 1000000000000) (-12802419815 / 1000000000000)
      | 1 => orderedInterval (2250956372 / 1000000000000) (2250956454 / 1000000000000)
      | 2 => orderedInterval (-2312721559 / 1000000000000) (-2312720469 / 1000000000000)
      | 3 => orderedInterval (13438829713 / 1000000000000) (13438836507 / 1000000000000)
      | 4 => orderedInterval (-2056476181 / 1000000000000) (-2056473615 / 1000000000000)
      | 5 => orderedInterval (1722079713 / 1000000000000) (1722079761 / 1000000000000)
      | 6 => orderedInterval (3403922031 / 1000000000000) (3403923029 / 1000000000000)
      | 7 => orderedInterval (3107481984 / 1000000000000) (3107482023 / 1000000000000)
      | _ => orderedInterval (-1516280958 / 1000000000000) (-1516280631 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (16803418976 / 1000000000000) (16803419004 / 1000000000000)
      | 1 => orderedInterval (-3474612938 / 1000000000000) (-3474612872 / 1000000000000)
      | 2 => orderedInterval (1308133684 / 1000000000000) (1308135286 / 1000000000000)
      | 3 => orderedInterval (25891063518 / 1000000000000) (25891078704 / 1000000000000)
      | 4 => orderedInterval (5624209271 / 1000000000000) (5624214740 / 1000000000000)
      | 5 => orderedInterval (-2193989578 / 1000000000000) (-2193989507 / 1000000000000)
      | 6 => orderedInterval (-5220328377 / 1000000000000) (-5220327572 / 1000000000000)
      | 7 => orderedInterval (-1226812970 / 1000000000000) (-1226812933 / 1000000000000)
      | _ => orderedInterval (11078313083 / 1000000000000) (11078313353 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (13201037770 / 1000000000000) (13201037802 / 1000000000000)
      | 1 => orderedInterval (-7794976577 / 1000000000000) (-7794976490 / 1000000000000)
      | 2 => orderedInterval (7462755100 / 1000000000000) (7462757452 / 1000000000000)
      | 3 => orderedInterval (-82168001984 / 1000000000000) (-82167968056 / 1000000000000)
      | 4 => orderedInterval (5663132520 / 1000000000000) (5663144176 / 1000000000000)
      | 5 => orderedInterval (-5553468185 / 1000000000000) (-5553468078 / 1000000000000)
      | 6 => orderedInterval (-2568399362 / 1000000000000) (-2568398695 / 1000000000000)
      | 7 => orderedInterval (-4178741878 / 1000000000000) (-4178741841 / 1000000000000)
      | _ => orderedInterval (-7076062065 / 1000000000000) (-7076061752 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-18353008120 / 1000000000000) (-18353008082 / 1000000000000)
      | 1 => orderedInterval (9193798547 / 1000000000000) (9193798679 / 1000000000000)
      | 2 => orderedInterval (-7792689138 / 1000000000000) (-7792685665 / 1000000000000)
      | 3 => orderedInterval (-134976895174 / 1000000000000) (-134976819227 / 1000000000000)
      | 4 => orderedInterval (-7916261547 / 1000000000000) (-7916236634 / 1000000000000)
      | 5 => orderedInterval (1942852257 / 1000000000000) (1942852423 / 1000000000000)
      | 6 => orderedInterval (6295446389 / 1000000000000) (6295446957 / 1000000000000)
      | 7 => orderedInterval (1040825897 / 1000000000000) (1040825935 / 1000000000000)
      | _ => orderedInterval (-21301685671 / 1000000000000) (-21301685217 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-23081908569 / 1000000000000) (-23081901412 / 1000000000000)
    | 1 => orderedInterval (5235371275 / 1000000000000) (5235383244 / 1000000000000)
    | 2 => orderedInterval (48589394669 / 1000000000000) (48589418203 / 1000000000000)
    | 3 => orderedInterval (-83012724661 / 1000000000000) (-83012675482 / 1000000000000)
    | _ => orderedInterval (-171867616560 / 1000000000000) (-171867510831 / 1000000000000)

theorem compactCertificate427_stateChecks0 :
    compactCertificate427.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 95 12 (597 / 2)) (orderedInterval (-34193121869 / 1000000000000) (-34193121868 / 1000000000000), orderedInterval (-30983983023 / 1000000000000) (-30983983022 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (879494995896897 / 4000000000000)) (orderedInterval (36563510072 / 1000000000000) (36563510073 / 1000000000000), orderedInterval (39394671820 / 1000000000000) (39394671821 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 113 12 (284410611308001 / 800000000000)) (orderedInterval (-40755779463 / 1000000000000) (-40755779459 / 1000000000000), orderedInterval (-11329999335 / 1000000000000) (-11329999331 / 1000000000000))) = true
  rfl'

theorem compactCertificate427_stateChecks1 :
    compactCertificate427.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 20 12 (256634446310979 / 4000000000000)) (orderedInterval (85467036684 / 1000000000000) (85467053943 / 1000000000000), orderedInterval (-51830806339 / 1000000000000) (-51830789080 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (689356221412263 / 4000000000000)) (orderedInterval (-20046952242 / 1000000000000) (-20046952241 / 1000000000000), orderedInterval (-57318906124 / 1000000000000) (-57318906123 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 149 12 (1871736240016971 / 4000000000000)) (orderedInterval (-21487943031 / 1000000000000) (-21487943030 / 1000000000000), orderedInterval (-29956347490 / 1000000000000) (-29956347489 / 1000000000000))) = true
  rfl'

theorem compactCertificate427_stateChecks2 :
    compactCertificate427.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 110 12 (1378712442825123 / 4000000000000)) (orderedInterval (-4805283497 / 1000000000000) (-4805283492 / 1000000000000), orderedInterval (42714219697 / 1000000000000) (42714219703 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 188 12 (2362447270181679 / 4000000000000)) (orderedInterval (23033192563 / 1000000000000) (23033192564 / 1000000000000), orderedInterval (23376458593 / 1000000000000) (23376458594 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 139 12 (1740167966661261 / 4000000000000)) (orderedInterval (28846999190 / 1000000000000) (28847029291 / 1000000000000), orderedInterval (-25156904338 / 1000000000000) (-25156874237 / 1000000000000))) = true
  rfl'

theorem compactCertificate427_stateChecks3 :
    compactCertificate427.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 213 12 (2669865165134403 / 4000000000000)) (orderedInterval (24339532170 / 1000000000000) (24339548637 / 1000000000000), orderedInterval (-19028037064 / 1000000000000) (-19028020597 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 123 12 (1541447371790187 / 4000000000000)) (orderedInterval (10801284053 / 1000000000000) (10801284098 / 1000000000000), orderedInterval (-39197412313 / 1000000000000) (-39197412268 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 218 12 (2735325411058983 / 4000000000000)) (orderedInterval (-7567333165 / 1000000000000) (-7567333162 / 1000000000000), orderedInterval (29563880185 / 1000000000000) (29563880189 / 1000000000000))) = true
  rfl'

theorem compactCertificate427_stateChecks4 :
    compactCertificate427.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 203 12 (2555695816091427 / 4000000000000)) (orderedInterval (-29134437061 / 1000000000000) (-29134372375 / 1000000000000), orderedInterval (12171011410 / 1000000000000) (12171076095 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 145 12 (1823865126591891 / 4000000000000)) (orderedInterval (-35096183430 / 1000000000000) (-35096183428 / 1000000000000), orderedInterval (-12785573936 / 1000000000000) (-12785573934 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 165 12 (2068068664236789 / 4000000000000)) (orderedInterval (18653333891 / 1000000000000) (18653334796 / 1000000000000), orderedInterval (-29739839057 / 1000000000000) (-29739838152 / 1000000000000))) = true
  rfl'

theorem compactCertificate427_stateChecks5 :
    compactCertificate427.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 137 12 (1724140045243941 / 4000000000000)) (orderedInterval (-38006095670 / 1000000000000) (-38006095627 / 1000000000000), orderedInterval (-5656071335 / 1000000000000) (-5656071292 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 121 12 (1523330017894761 / 4000000000000)) (orderedInterval (-40734967419 / 1000000000000) (-40734967345 / 1000000000000), orderedInterval (-3455641612 / 1000000000000) (-3455641538 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 176 12 (441520413825339 / 800000000000)) (orderedInterval (-7895495113 / 1000000000000) (-7895495106 / 1000000000000), orderedInterval (33039957229 / 1000000000000) (33039957237 / 1000000000000))) = true
  rfl'

theorem compactCertificate427_stateChecks6 :
    compactCertificate427.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 97 12 (1221268700587233 / 4000000000000)) (orderedInterval (-44724230198 / 1000000000000) (-44724230191 / 1000000000000), orderedInterval (-9138178217 / 1000000000000) (-9138178210 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 82 12 (1035283002668313 / 4000000000000)) (orderedInterval (45198064892 / 1000000000000) (45198079424 / 1000000000000), orderedInterval (-20503612775 / 1000000000000) (-20503598243 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 52 12 (647832033338739 / 4000000000000)) (orderedInterval (-36437768147 / 1000000000000) (-36437756048 / 1000000000000), orderedInterval (51132736062 / 1000000000000) (51132748161 / 1000000000000))) = true
  rfl'

theorem compactCertificate427_stateChecks7 :
    compactCertificate427.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 28 12 (348406222121613 / 4000000000000)) (orderedInterval (-6753259027 / 1000000000000) (-6753259002 / 1000000000000), orderedInterval (85264637413 / 1000000000000) (85264637437 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 75 12 (945990667723839 / 4000000000000)) (orderedInterval (-51662322667 / 1000000000000) (-51662322355 / 1000000000000), orderedInterval (4890795506 / 1000000000000) (4890795819 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 103 12 (1291669381547103 / 4000000000000)) (orderedInterval (-5240990828 / 1000000000000) (-5240990827 / 1000000000000), orderedInterval (-44082675954 / 1000000000000) (-44082675953 / 1000000000000))) = true
  rfl'

theorem compactCertificate427_stateChecks8 :
    compactCertificate427.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (546167966661261 / 4000000000000)) (orderedInterval (-53639626748 / 1000000000000) (-53639551219 / 1000000000000), orderedInterval (42448406355 / 1000000000000) (42448481884 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 177 12 (2220142462139181 / 4000000000000)) (orderedInterval (8086876665 / 1000000000000) (8086876673 / 1000000000000), orderedInterval (-32894849315 / 1000000000000) (-32894849307 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 118 12 (1482952274285379 / 4000000000000)) (orderedInterval (30161595923 / 1000000000000) (30161595924 / 1000000000000), orderedInterval (28374927950 / 1000000000000) (28374927951 / 1000000000000))) = true
  rfl'

theorem compactCertificate427_states : ∀ j,
    BesselStateValid (compactCertificate427.point j) (compactCertificate427.state j) :=
  compactCertificate427.statesValid_of_checks3 compactCertificate427_stateChecks0
    compactCertificate427_stateChecks1 compactCertificate427_stateChecks2
    compactCertificate427_stateChecks3 compactCertificate427_stateChecks4
    compactCertificate427_stateChecks5 compactCertificate427_stateChecks6
    compactCertificate427_stateChecks7 compactCertificate427_stateChecks8

theorem compactCertificate427_chunkChecks0_0 :
    compactCertificate427.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (597 / 2) 0 (IntervalRat.scale (597 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-34193121869 / 1000000000000) (-34193121868 / 1000000000000), orderedInterval (-30983983023 / 1000000000000) (-30983983022 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (879494995896897 / 4000000000000) 0 (IntervalRat.scale (597 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (36563510072 / 1000000000000) (36563510073 / 1000000000000), orderedInterval (39394671820 / 1000000000000) (39394671821 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (284410611308001 / 800000000000) 0 (IntervalRat.scale (597 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-40755779463 / 1000000000000) (-40755779459 / 1000000000000), orderedInterval (-11329999335 / 1000000000000) (-11329999331 / 1000000000000)))) (orderedInterval (-15603851141 / 1000000000000) (-15603851119 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (256634446310979 / 4000000000000) 0 (IntervalRat.scale (597 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (85467036684 / 1000000000000) (85467053943 / 1000000000000), orderedInterval (-51830806339 / 1000000000000) (-51830789080 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (689356221412263 / 4000000000000) 0 (IntervalRat.scale (597 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-20046952242 / 1000000000000) (-20046952241 / 1000000000000), orderedInterval (-57318906124 / 1000000000000) (-57318906123 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1871736240016971 / 4000000000000) 0 (IntervalRat.scale (597 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-21487943031 / 1000000000000) (-21487943030 / 1000000000000), orderedInterval (-29956347490 / 1000000000000) (-29956347489 / 1000000000000)))) (orderedInterval (-131636030 / 1000000000000) (-131635806 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1378712442825123 / 4000000000000) 0 (IntervalRat.scale (597 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-4805283497 / 1000000000000) (-4805283492 / 1000000000000), orderedInterval (42714219697 / 1000000000000) (42714219703 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2362447270181679 / 4000000000000) 0 (IntervalRat.scale (597 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (23033192563 / 1000000000000) (23033192564 / 1000000000000), orderedInterval (23376458593 / 1000000000000) (23376458594 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1740167966661261 / 4000000000000) 0 (IntervalRat.scale (597 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (28846999190 / 1000000000000) (28847029291 / 1000000000000), orderedInterval (-25156904338 / 1000000000000) (-25156874237 / 1000000000000)))) (orderedInterval (-13260768 / 1000000000000) (-13260023 / 1000000000000))) = true
  rfl'

theorem compactCertificate427_chunkChecks0_1 :
    compactCertificate427.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2669865165134403 / 4000000000000) 0 (IntervalRat.scale (597 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (24339532170 / 1000000000000) (24339548637 / 1000000000000), orderedInterval (-19028037064 / 1000000000000) (-19028020597 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1541447371790187 / 4000000000000) 0 (IntervalRat.scale (597 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (10801284053 / 1000000000000) (10801284098 / 1000000000000), orderedInterval (-39197412313 / 1000000000000) (-39197412268 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2735325411058983 / 4000000000000) 0 (IntervalRat.scale (597 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-7567333165 / 1000000000000) (-7567333162 / 1000000000000), orderedInterval (29563880185 / 1000000000000) (29563880189 / 1000000000000)))) (orderedInterval (-4600298708 / 1000000000000) (-4600295660 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2555695816091427 / 4000000000000) 0 (IntervalRat.scale (597 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-29134437061 / 1000000000000) (-29134372375 / 1000000000000), orderedInterval (12171011410 / 1000000000000) (12171076095 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1823865126591891 / 4000000000000) 0 (IntervalRat.scale (597 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-35096183430 / 1000000000000) (-35096183428 / 1000000000000), orderedInterval (-12785573936 / 1000000000000) (-12785573934 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2068068664236789 / 4000000000000) 0 (IntervalRat.scale (597 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (18653333891 / 1000000000000) (18653334796 / 1000000000000), orderedInterval (-29739839057 / 1000000000000) (-29739838152 / 1000000000000)))) (orderedInterval (-2887226997 / 1000000000000) (-2887225789 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1724140045243941 / 4000000000000) 0 (IntervalRat.scale (597 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-38006095670 / 1000000000000) (-38006095627 / 1000000000000), orderedInterval (-5656071335 / 1000000000000) (-5656071292 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1523330017894761 / 4000000000000) 0 (IntervalRat.scale (597 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-40734967419 / 1000000000000) (-40734967345 / 1000000000000), orderedInterval (-3455641612 / 1000000000000) (-3455641538 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (441520413825339 / 800000000000) 0 (IntervalRat.scale (597 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-7895495113 / 1000000000000) (-7895495106 / 1000000000000), orderedInterval (33039957229 / 1000000000000) (33039957237 / 1000000000000)))) (orderedInterval (1690089091 / 1000000000000) (1690089125 / 1000000000000))) = true
  rfl'

theorem compactCertificate427_chunkChecks0_2 :
    compactCertificate427.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1221268700587233 / 4000000000000) 0 (IntervalRat.scale (597 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-44724230198 / 1000000000000) (-44724230191 / 1000000000000), orderedInterval (-9138178217 / 1000000000000) (-9138178210 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1035283002668313 / 4000000000000) 0 (IntervalRat.scale (597 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (45198064892 / 1000000000000) (45198079424 / 1000000000000), orderedInterval (-20503612775 / 1000000000000) (-20503598243 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (647832033338739 / 4000000000000) 0 (IntervalRat.scale (597 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-36437768147 / 1000000000000) (-36437756048 / 1000000000000), orderedInterval (51132736062 / 1000000000000) (51132748161 / 1000000000000)))) (orderedInterval (3406615621 / 1000000000000) (3406616914 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (348406222121613 / 4000000000000) 0 (IntervalRat.scale (597 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-6753259027 / 1000000000000) (-6753259002 / 1000000000000), orderedInterval (85264637413 / 1000000000000) (85264637437 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (945990667723839 / 4000000000000) 0 (IntervalRat.scale (597 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-51662322667 / 1000000000000) (-51662322355 / 1000000000000), orderedInterval (4890795506 / 1000000000000) (4890795819 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1291669381547103 / 4000000000000) 0 (IntervalRat.scale (597 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-5240990828 / 1000000000000) (-5240990827 / 1000000000000), orderedInterval (-44082675954 / 1000000000000) (-44082675953 / 1000000000000)))) (orderedInterval (1698419292 / 1000000000000) (1698419336 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (546167966661261 / 4000000000000) 0 (IntervalRat.scale (597 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-53639626748 / 1000000000000) (-53639551219 / 1000000000000), orderedInterval (42448406355 / 1000000000000) (42448481884 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2220142462139181 / 4000000000000) 0 (IntervalRat.scale (597 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (8086876665 / 1000000000000) (8086876673 / 1000000000000), orderedInterval (-32894849315 / 1000000000000) (-32894849307 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1482952274285379 / 4000000000000) 0 (IntervalRat.scale (597 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (30161595923 / 1000000000000) (30161595924 / 1000000000000), orderedInterval (28374927950 / 1000000000000) (28374927951 / 1000000000000)))) (orderedInterval (-6640758929 / 1000000000000) (-6640758390 / 1000000000000))) = true
  rfl'

theorem compactCertificate427_chunkChecks0 :
    compactCertificate427.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate427.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate427_chunkChecks0_0
    compactCertificate427_chunkChecks0_1 compactCertificate427_chunkChecks0_2

theorem compactCertificate427_chunkChecks1_0 :
    compactCertificate427.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (597 / 2) 1 (IntervalRat.scale (597 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-34193121869 / 1000000000000) (-34193121868 / 1000000000000), orderedInterval (-30983983023 / 1000000000000) (-30983983022 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (879494995896897 / 4000000000000) 1 (IntervalRat.scale (597 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (36563510072 / 1000000000000) (36563510073 / 1000000000000), orderedInterval (39394671820 / 1000000000000) (39394671821 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (284410611308001 / 800000000000) 1 (IntervalRat.scale (597 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-40755779463 / 1000000000000) (-40755779459 / 1000000000000), orderedInterval (-11329999335 / 1000000000000) (-11329999331 / 1000000000000)))) (orderedInterval (-12802419840 / 1000000000000) (-12802419815 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (256634446310979 / 4000000000000) 1 (IntervalRat.scale (597 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (85467036684 / 1000000000000) (85467053943 / 1000000000000), orderedInterval (-51830806339 / 1000000000000) (-51830789080 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (689356221412263 / 4000000000000) 1 (IntervalRat.scale (597 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-20046952242 / 1000000000000) (-20046952241 / 1000000000000), orderedInterval (-57318906124 / 1000000000000) (-57318906123 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1871736240016971 / 4000000000000) 1 (IntervalRat.scale (597 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-21487943031 / 1000000000000) (-21487943030 / 1000000000000), orderedInterval (-29956347490 / 1000000000000) (-29956347489 / 1000000000000)))) (orderedInterval (2250956372 / 1000000000000) (2250956454 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1378712442825123 / 4000000000000) 1 (IntervalRat.scale (597 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-4805283497 / 1000000000000) (-4805283492 / 1000000000000), orderedInterval (42714219697 / 1000000000000) (42714219703 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2362447270181679 / 4000000000000) 1 (IntervalRat.scale (597 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (23033192563 / 1000000000000) (23033192564 / 1000000000000), orderedInterval (23376458593 / 1000000000000) (23376458594 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1740167966661261 / 4000000000000) 1 (IntervalRat.scale (597 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (28846999190 / 1000000000000) (28847029291 / 1000000000000), orderedInterval (-25156904338 / 1000000000000) (-25156874237 / 1000000000000)))) (orderedInterval (-2312721559 / 1000000000000) (-2312720469 / 1000000000000))) = true
  rfl'

theorem compactCertificate427_chunkChecks1_1 :
    compactCertificate427.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2669865165134403 / 4000000000000) 1 (IntervalRat.scale (597 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (24339532170 / 1000000000000) (24339548637 / 1000000000000), orderedInterval (-19028037064 / 1000000000000) (-19028020597 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1541447371790187 / 4000000000000) 1 (IntervalRat.scale (597 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (10801284053 / 1000000000000) (10801284098 / 1000000000000), orderedInterval (-39197412313 / 1000000000000) (-39197412268 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2735325411058983 / 4000000000000) 1 (IntervalRat.scale (597 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-7567333165 / 1000000000000) (-7567333162 / 1000000000000), orderedInterval (29563880185 / 1000000000000) (29563880189 / 1000000000000)))) (orderedInterval (13438829713 / 1000000000000) (13438836507 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2555695816091427 / 4000000000000) 1 (IntervalRat.scale (597 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-29134437061 / 1000000000000) (-29134372375 / 1000000000000), orderedInterval (12171011410 / 1000000000000) (12171076095 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1823865126591891 / 4000000000000) 1 (IntervalRat.scale (597 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-35096183430 / 1000000000000) (-35096183428 / 1000000000000), orderedInterval (-12785573936 / 1000000000000) (-12785573934 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2068068664236789 / 4000000000000) 1 (IntervalRat.scale (597 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (18653333891 / 1000000000000) (18653334796 / 1000000000000), orderedInterval (-29739839057 / 1000000000000) (-29739838152 / 1000000000000)))) (orderedInterval (-2056476181 / 1000000000000) (-2056473615 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1724140045243941 / 4000000000000) 1 (IntervalRat.scale (597 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-38006095670 / 1000000000000) (-38006095627 / 1000000000000), orderedInterval (-5656071335 / 1000000000000) (-5656071292 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1523330017894761 / 4000000000000) 1 (IntervalRat.scale (597 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-40734967419 / 1000000000000) (-40734967345 / 1000000000000), orderedInterval (-3455641612 / 1000000000000) (-3455641538 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (441520413825339 / 800000000000) 1 (IntervalRat.scale (597 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-7895495113 / 1000000000000) (-7895495106 / 1000000000000), orderedInterval (33039957229 / 1000000000000) (33039957237 / 1000000000000)))) (orderedInterval (1722079713 / 1000000000000) (1722079761 / 1000000000000))) = true
  rfl'

theorem compactCertificate427_chunkChecks1_2 :
    compactCertificate427.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1221268700587233 / 4000000000000) 1 (IntervalRat.scale (597 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-44724230198 / 1000000000000) (-44724230191 / 1000000000000), orderedInterval (-9138178217 / 1000000000000) (-9138178210 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1035283002668313 / 4000000000000) 1 (IntervalRat.scale (597 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (45198064892 / 1000000000000) (45198079424 / 1000000000000), orderedInterval (-20503612775 / 1000000000000) (-20503598243 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (647832033338739 / 4000000000000) 1 (IntervalRat.scale (597 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-36437768147 / 1000000000000) (-36437756048 / 1000000000000), orderedInterval (51132736062 / 1000000000000) (51132748161 / 1000000000000)))) (orderedInterval (3403922031 / 1000000000000) (3403923029 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (348406222121613 / 4000000000000) 1 (IntervalRat.scale (597 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-6753259027 / 1000000000000) (-6753259002 / 1000000000000), orderedInterval (85264637413 / 1000000000000) (85264637437 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (945990667723839 / 4000000000000) 1 (IntervalRat.scale (597 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-51662322667 / 1000000000000) (-51662322355 / 1000000000000), orderedInterval (4890795506 / 1000000000000) (4890795819 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1291669381547103 / 4000000000000) 1 (IntervalRat.scale (597 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-5240990828 / 1000000000000) (-5240990827 / 1000000000000), orderedInterval (-44082675954 / 1000000000000) (-44082675953 / 1000000000000)))) (orderedInterval (3107481984 / 1000000000000) (3107482023 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (546167966661261 / 4000000000000) 1 (IntervalRat.scale (597 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-53639626748 / 1000000000000) (-53639551219 / 1000000000000), orderedInterval (42448406355 / 1000000000000) (42448481884 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2220142462139181 / 4000000000000) 1 (IntervalRat.scale (597 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (8086876665 / 1000000000000) (8086876673 / 1000000000000), orderedInterval (-32894849315 / 1000000000000) (-32894849307 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1482952274285379 / 4000000000000) 1 (IntervalRat.scale (597 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (30161595923 / 1000000000000) (30161595924 / 1000000000000), orderedInterval (28374927950 / 1000000000000) (28374927951 / 1000000000000)))) (orderedInterval (-1516280958 / 1000000000000) (-1516280631 / 1000000000000))) = true
  rfl'

theorem compactCertificate427_chunkChecks1 :
    compactCertificate427.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate427.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate427_chunkChecks1_0
    compactCertificate427_chunkChecks1_1 compactCertificate427_chunkChecks1_2

theorem compactCertificate427_chunkChecks2_0 :
    compactCertificate427.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (597 / 2) 2 (IntervalRat.scale (597 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-34193121869 / 1000000000000) (-34193121868 / 1000000000000), orderedInterval (-30983983023 / 1000000000000) (-30983983022 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (879494995896897 / 4000000000000) 2 (IntervalRat.scale (597 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (36563510072 / 1000000000000) (36563510073 / 1000000000000), orderedInterval (39394671820 / 1000000000000) (39394671821 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (284410611308001 / 800000000000) 2 (IntervalRat.scale (597 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-40755779463 / 1000000000000) (-40755779459 / 1000000000000), orderedInterval (-11329999335 / 1000000000000) (-11329999331 / 1000000000000)))) (orderedInterval (16803418976 / 1000000000000) (16803419004 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (256634446310979 / 4000000000000) 2 (IntervalRat.scale (597 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (85467036684 / 1000000000000) (85467053943 / 1000000000000), orderedInterval (-51830806339 / 1000000000000) (-51830789080 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (689356221412263 / 4000000000000) 2 (IntervalRat.scale (597 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-20046952242 / 1000000000000) (-20046952241 / 1000000000000), orderedInterval (-57318906124 / 1000000000000) (-57318906123 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1871736240016971 / 4000000000000) 2 (IntervalRat.scale (597 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-21487943031 / 1000000000000) (-21487943030 / 1000000000000), orderedInterval (-29956347490 / 1000000000000) (-29956347489 / 1000000000000)))) (orderedInterval (-3474612938 / 1000000000000) (-3474612872 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1378712442825123 / 4000000000000) 2 (IntervalRat.scale (597 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-4805283497 / 1000000000000) (-4805283492 / 1000000000000), orderedInterval (42714219697 / 1000000000000) (42714219703 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2362447270181679 / 4000000000000) 2 (IntervalRat.scale (597 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (23033192563 / 1000000000000) (23033192564 / 1000000000000), orderedInterval (23376458593 / 1000000000000) (23376458594 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1740167966661261 / 4000000000000) 2 (IntervalRat.scale (597 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (28846999190 / 1000000000000) (28847029291 / 1000000000000), orderedInterval (-25156904338 / 1000000000000) (-25156874237 / 1000000000000)))) (orderedInterval (1308133684 / 1000000000000) (1308135286 / 1000000000000))) = true
  rfl'

theorem compactCertificate427_chunkChecks2_1 :
    compactCertificate427.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2669865165134403 / 4000000000000) 2 (IntervalRat.scale (597 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (24339532170 / 1000000000000) (24339548637 / 1000000000000), orderedInterval (-19028037064 / 1000000000000) (-19028020597 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1541447371790187 / 4000000000000) 2 (IntervalRat.scale (597 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (10801284053 / 1000000000000) (10801284098 / 1000000000000), orderedInterval (-39197412313 / 1000000000000) (-39197412268 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2735325411058983 / 4000000000000) 2 (IntervalRat.scale (597 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-7567333165 / 1000000000000) (-7567333162 / 1000000000000), orderedInterval (29563880185 / 1000000000000) (29563880189 / 1000000000000)))) (orderedInterval (25891063518 / 1000000000000) (25891078704 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2555695816091427 / 4000000000000) 2 (IntervalRat.scale (597 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-29134437061 / 1000000000000) (-29134372375 / 1000000000000), orderedInterval (12171011410 / 1000000000000) (12171076095 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1823865126591891 / 4000000000000) 2 (IntervalRat.scale (597 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-35096183430 / 1000000000000) (-35096183428 / 1000000000000), orderedInterval (-12785573936 / 1000000000000) (-12785573934 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2068068664236789 / 4000000000000) 2 (IntervalRat.scale (597 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (18653333891 / 1000000000000) (18653334796 / 1000000000000), orderedInterval (-29739839057 / 1000000000000) (-29739838152 / 1000000000000)))) (orderedInterval (5624209271 / 1000000000000) (5624214740 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1724140045243941 / 4000000000000) 2 (IntervalRat.scale (597 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-38006095670 / 1000000000000) (-38006095627 / 1000000000000), orderedInterval (-5656071335 / 1000000000000) (-5656071292 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1523330017894761 / 4000000000000) 2 (IntervalRat.scale (597 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-40734967419 / 1000000000000) (-40734967345 / 1000000000000), orderedInterval (-3455641612 / 1000000000000) (-3455641538 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (441520413825339 / 800000000000) 2 (IntervalRat.scale (597 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-7895495113 / 1000000000000) (-7895495106 / 1000000000000), orderedInterval (33039957229 / 1000000000000) (33039957237 / 1000000000000)))) (orderedInterval (-2193989578 / 1000000000000) (-2193989507 / 1000000000000))) = true
  rfl'

theorem compactCertificate427_chunkChecks2_2 :
    compactCertificate427.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1221268700587233 / 4000000000000) 2 (IntervalRat.scale (597 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-44724230198 / 1000000000000) (-44724230191 / 1000000000000), orderedInterval (-9138178217 / 1000000000000) (-9138178210 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1035283002668313 / 4000000000000) 2 (IntervalRat.scale (597 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (45198064892 / 1000000000000) (45198079424 / 1000000000000), orderedInterval (-20503612775 / 1000000000000) (-20503598243 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (647832033338739 / 4000000000000) 2 (IntervalRat.scale (597 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-36437768147 / 1000000000000) (-36437756048 / 1000000000000), orderedInterval (51132736062 / 1000000000000) (51132748161 / 1000000000000)))) (orderedInterval (-5220328377 / 1000000000000) (-5220327572 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (348406222121613 / 4000000000000) 2 (IntervalRat.scale (597 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-6753259027 / 1000000000000) (-6753259002 / 1000000000000), orderedInterval (85264637413 / 1000000000000) (85264637437 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (945990667723839 / 4000000000000) 2 (IntervalRat.scale (597 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-51662322667 / 1000000000000) (-51662322355 / 1000000000000), orderedInterval (4890795506 / 1000000000000) (4890795819 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1291669381547103 / 4000000000000) 2 (IntervalRat.scale (597 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-5240990828 / 1000000000000) (-5240990827 / 1000000000000), orderedInterval (-44082675954 / 1000000000000) (-44082675953 / 1000000000000)))) (orderedInterval (-1226812970 / 1000000000000) (-1226812933 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (546167966661261 / 4000000000000) 2 (IntervalRat.scale (597 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-53639626748 / 1000000000000) (-53639551219 / 1000000000000), orderedInterval (42448406355 / 1000000000000) (42448481884 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2220142462139181 / 4000000000000) 2 (IntervalRat.scale (597 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (8086876665 / 1000000000000) (8086876673 / 1000000000000), orderedInterval (-32894849315 / 1000000000000) (-32894849307 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1482952274285379 / 4000000000000) 2 (IntervalRat.scale (597 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (30161595923 / 1000000000000) (30161595924 / 1000000000000), orderedInterval (28374927950 / 1000000000000) (28374927951 / 1000000000000)))) (orderedInterval (11078313083 / 1000000000000) (11078313353 / 1000000000000))) = true
  rfl'

theorem compactCertificate427_chunkChecks2 :
    compactCertificate427.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate427.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate427_chunkChecks2_0
    compactCertificate427_chunkChecks2_1 compactCertificate427_chunkChecks2_2

theorem compactCertificate427_chunkChecks3_0 :
    compactCertificate427.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (597 / 2) 3 (IntervalRat.scale (597 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-34193121869 / 1000000000000) (-34193121868 / 1000000000000), orderedInterval (-30983983023 / 1000000000000) (-30983983022 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (879494995896897 / 4000000000000) 3 (IntervalRat.scale (597 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (36563510072 / 1000000000000) (36563510073 / 1000000000000), orderedInterval (39394671820 / 1000000000000) (39394671821 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (284410611308001 / 800000000000) 3 (IntervalRat.scale (597 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-40755779463 / 1000000000000) (-40755779459 / 1000000000000), orderedInterval (-11329999335 / 1000000000000) (-11329999331 / 1000000000000)))) (orderedInterval (13201037770 / 1000000000000) (13201037802 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (256634446310979 / 4000000000000) 3 (IntervalRat.scale (597 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (85467036684 / 1000000000000) (85467053943 / 1000000000000), orderedInterval (-51830806339 / 1000000000000) (-51830789080 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (689356221412263 / 4000000000000) 3 (IntervalRat.scale (597 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-20046952242 / 1000000000000) (-20046952241 / 1000000000000), orderedInterval (-57318906124 / 1000000000000) (-57318906123 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1871736240016971 / 4000000000000) 3 (IntervalRat.scale (597 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-21487943031 / 1000000000000) (-21487943030 / 1000000000000), orderedInterval (-29956347490 / 1000000000000) (-29956347489 / 1000000000000)))) (orderedInterval (-7794976577 / 1000000000000) (-7794976490 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1378712442825123 / 4000000000000) 3 (IntervalRat.scale (597 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-4805283497 / 1000000000000) (-4805283492 / 1000000000000), orderedInterval (42714219697 / 1000000000000) (42714219703 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2362447270181679 / 4000000000000) 3 (IntervalRat.scale (597 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (23033192563 / 1000000000000) (23033192564 / 1000000000000), orderedInterval (23376458593 / 1000000000000) (23376458594 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1740167966661261 / 4000000000000) 3 (IntervalRat.scale (597 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (28846999190 / 1000000000000) (28847029291 / 1000000000000), orderedInterval (-25156904338 / 1000000000000) (-25156874237 / 1000000000000)))) (orderedInterval (7462755100 / 1000000000000) (7462757452 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate427_chunkChecks3_1 :
    compactCertificate427.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2669865165134403 / 4000000000000) 3 (IntervalRat.scale (597 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (24339532170 / 1000000000000) (24339548637 / 1000000000000), orderedInterval (-19028037064 / 1000000000000) (-19028020597 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1541447371790187 / 4000000000000) 3 (IntervalRat.scale (597 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (10801284053 / 1000000000000) (10801284098 / 1000000000000), orderedInterval (-39197412313 / 1000000000000) (-39197412268 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2735325411058983 / 4000000000000) 3 (IntervalRat.scale (597 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-7567333165 / 1000000000000) (-7567333162 / 1000000000000), orderedInterval (29563880185 / 1000000000000) (29563880189 / 1000000000000)))) (orderedInterval (-82168001984 / 1000000000000) (-82167968056 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2555695816091427 / 4000000000000) 3 (IntervalRat.scale (597 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-29134437061 / 1000000000000) (-29134372375 / 1000000000000), orderedInterval (12171011410 / 1000000000000) (12171076095 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1823865126591891 / 4000000000000) 3 (IntervalRat.scale (597 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-35096183430 / 1000000000000) (-35096183428 / 1000000000000), orderedInterval (-12785573936 / 1000000000000) (-12785573934 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2068068664236789 / 4000000000000) 3 (IntervalRat.scale (597 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (18653333891 / 1000000000000) (18653334796 / 1000000000000), orderedInterval (-29739839057 / 1000000000000) (-29739838152 / 1000000000000)))) (orderedInterval (5663132520 / 1000000000000) (5663144176 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1724140045243941 / 4000000000000) 3 (IntervalRat.scale (597 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-38006095670 / 1000000000000) (-38006095627 / 1000000000000), orderedInterval (-5656071335 / 1000000000000) (-5656071292 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1523330017894761 / 4000000000000) 3 (IntervalRat.scale (597 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-40734967419 / 1000000000000) (-40734967345 / 1000000000000), orderedInterval (-3455641612 / 1000000000000) (-3455641538 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (441520413825339 / 800000000000) 3 (IntervalRat.scale (597 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-7895495113 / 1000000000000) (-7895495106 / 1000000000000), orderedInterval (33039957229 / 1000000000000) (33039957237 / 1000000000000)))) (orderedInterval (-5553468185 / 1000000000000) (-5553468078 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate427_chunkChecks3_2 :
    compactCertificate427.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1221268700587233 / 4000000000000) 3 (IntervalRat.scale (597 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-44724230198 / 1000000000000) (-44724230191 / 1000000000000), orderedInterval (-9138178217 / 1000000000000) (-9138178210 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1035283002668313 / 4000000000000) 3 (IntervalRat.scale (597 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (45198064892 / 1000000000000) (45198079424 / 1000000000000), orderedInterval (-20503612775 / 1000000000000) (-20503598243 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (647832033338739 / 4000000000000) 3 (IntervalRat.scale (597 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-36437768147 / 1000000000000) (-36437756048 / 1000000000000), orderedInterval (51132736062 / 1000000000000) (51132748161 / 1000000000000)))) (orderedInterval (-2568399362 / 1000000000000) (-2568398695 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (348406222121613 / 4000000000000) 3 (IntervalRat.scale (597 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-6753259027 / 1000000000000) (-6753259002 / 1000000000000), orderedInterval (85264637413 / 1000000000000) (85264637437 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (945990667723839 / 4000000000000) 3 (IntervalRat.scale (597 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-51662322667 / 1000000000000) (-51662322355 / 1000000000000), orderedInterval (4890795506 / 1000000000000) (4890795819 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1291669381547103 / 4000000000000) 3 (IntervalRat.scale (597 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-5240990828 / 1000000000000) (-5240990827 / 1000000000000), orderedInterval (-44082675954 / 1000000000000) (-44082675953 / 1000000000000)))) (orderedInterval (-4178741878 / 1000000000000) (-4178741841 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (546167966661261 / 4000000000000) 3 (IntervalRat.scale (597 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-53639626748 / 1000000000000) (-53639551219 / 1000000000000), orderedInterval (42448406355 / 1000000000000) (42448481884 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2220142462139181 / 4000000000000) 3 (IntervalRat.scale (597 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (8086876665 / 1000000000000) (8086876673 / 1000000000000), orderedInterval (-32894849315 / 1000000000000) (-32894849307 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1482952274285379 / 4000000000000) 3 (IntervalRat.scale (597 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (30161595923 / 1000000000000) (30161595924 / 1000000000000), orderedInterval (28374927950 / 1000000000000) (28374927951 / 1000000000000)))) (orderedInterval (-7076062065 / 1000000000000) (-7076061752 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate427_chunkChecks3 :
    compactCertificate427.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate427.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate427_chunkChecks3_0
    compactCertificate427_chunkChecks3_1 compactCertificate427_chunkChecks3_2

theorem compactCertificate427_chunkChecks4_0 :
    compactCertificate427.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (597 / 2) 4 (IntervalRat.scale (597 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-34193121869 / 1000000000000) (-34193121868 / 1000000000000), orderedInterval (-30983983023 / 1000000000000) (-30983983022 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (879494995896897 / 4000000000000) 4 (IntervalRat.scale (597 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (36563510072 / 1000000000000) (36563510073 / 1000000000000), orderedInterval (39394671820 / 1000000000000) (39394671821 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (284410611308001 / 800000000000) 4 (IntervalRat.scale (597 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-40755779463 / 1000000000000) (-40755779459 / 1000000000000), orderedInterval (-11329999335 / 1000000000000) (-11329999331 / 1000000000000)))) (orderedInterval (-18353008120 / 1000000000000) (-18353008082 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (256634446310979 / 4000000000000) 4 (IntervalRat.scale (597 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (85467036684 / 1000000000000) (85467053943 / 1000000000000), orderedInterval (-51830806339 / 1000000000000) (-51830789080 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (689356221412263 / 4000000000000) 4 (IntervalRat.scale (597 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-20046952242 / 1000000000000) (-20046952241 / 1000000000000), orderedInterval (-57318906124 / 1000000000000) (-57318906123 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1871736240016971 / 4000000000000) 4 (IntervalRat.scale (597 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-21487943031 / 1000000000000) (-21487943030 / 1000000000000), orderedInterval (-29956347490 / 1000000000000) (-29956347489 / 1000000000000)))) (orderedInterval (9193798547 / 1000000000000) (9193798679 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1378712442825123 / 4000000000000) 4 (IntervalRat.scale (597 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-4805283497 / 1000000000000) (-4805283492 / 1000000000000), orderedInterval (42714219697 / 1000000000000) (42714219703 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2362447270181679 / 4000000000000) 4 (IntervalRat.scale (597 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (23033192563 / 1000000000000) (23033192564 / 1000000000000), orderedInterval (23376458593 / 1000000000000) (23376458594 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1740167966661261 / 4000000000000) 4 (IntervalRat.scale (597 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (28846999190 / 1000000000000) (28847029291 / 1000000000000), orderedInterval (-25156904338 / 1000000000000) (-25156874237 / 1000000000000)))) (orderedInterval (-7792689138 / 1000000000000) (-7792685665 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate427_chunkChecks4_1 :
    compactCertificate427.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2669865165134403 / 4000000000000) 4 (IntervalRat.scale (597 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (24339532170 / 1000000000000) (24339548637 / 1000000000000), orderedInterval (-19028037064 / 1000000000000) (-19028020597 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1541447371790187 / 4000000000000) 4 (IntervalRat.scale (597 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (10801284053 / 1000000000000) (10801284098 / 1000000000000), orderedInterval (-39197412313 / 1000000000000) (-39197412268 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2735325411058983 / 4000000000000) 4 (IntervalRat.scale (597 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-7567333165 / 1000000000000) (-7567333162 / 1000000000000), orderedInterval (29563880185 / 1000000000000) (29563880189 / 1000000000000)))) (orderedInterval (-134976895174 / 1000000000000) (-134976819227 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2555695816091427 / 4000000000000) 4 (IntervalRat.scale (597 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-29134437061 / 1000000000000) (-29134372375 / 1000000000000), orderedInterval (12171011410 / 1000000000000) (12171076095 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1823865126591891 / 4000000000000) 4 (IntervalRat.scale (597 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-35096183430 / 1000000000000) (-35096183428 / 1000000000000), orderedInterval (-12785573936 / 1000000000000) (-12785573934 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2068068664236789 / 4000000000000) 4 (IntervalRat.scale (597 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (18653333891 / 1000000000000) (18653334796 / 1000000000000), orderedInterval (-29739839057 / 1000000000000) (-29739838152 / 1000000000000)))) (orderedInterval (-7916261547 / 1000000000000) (-7916236634 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1724140045243941 / 4000000000000) 4 (IntervalRat.scale (597 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-38006095670 / 1000000000000) (-38006095627 / 1000000000000), orderedInterval (-5656071335 / 1000000000000) (-5656071292 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1523330017894761 / 4000000000000) 4 (IntervalRat.scale (597 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-40734967419 / 1000000000000) (-40734967345 / 1000000000000), orderedInterval (-3455641612 / 1000000000000) (-3455641538 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (441520413825339 / 800000000000) 4 (IntervalRat.scale (597 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-7895495113 / 1000000000000) (-7895495106 / 1000000000000), orderedInterval (33039957229 / 1000000000000) (33039957237 / 1000000000000)))) (orderedInterval (1942852257 / 1000000000000) (1942852423 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate427_chunkChecks4_2 :
    compactCertificate427.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1221268700587233 / 4000000000000) 4 (IntervalRat.scale (597 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-44724230198 / 1000000000000) (-44724230191 / 1000000000000), orderedInterval (-9138178217 / 1000000000000) (-9138178210 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1035283002668313 / 4000000000000) 4 (IntervalRat.scale (597 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (45198064892 / 1000000000000) (45198079424 / 1000000000000), orderedInterval (-20503612775 / 1000000000000) (-20503598243 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (647832033338739 / 4000000000000) 4 (IntervalRat.scale (597 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-36437768147 / 1000000000000) (-36437756048 / 1000000000000), orderedInterval (51132736062 / 1000000000000) (51132748161 / 1000000000000)))) (orderedInterval (6295446389 / 1000000000000) (6295446957 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (348406222121613 / 4000000000000) 4 (IntervalRat.scale (597 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-6753259027 / 1000000000000) (-6753259002 / 1000000000000), orderedInterval (85264637413 / 1000000000000) (85264637437 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (945990667723839 / 4000000000000) 4 (IntervalRat.scale (597 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-51662322667 / 1000000000000) (-51662322355 / 1000000000000), orderedInterval (4890795506 / 1000000000000) (4890795819 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1291669381547103 / 4000000000000) 4 (IntervalRat.scale (597 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-5240990828 / 1000000000000) (-5240990827 / 1000000000000), orderedInterval (-44082675954 / 1000000000000) (-44082675953 / 1000000000000)))) (orderedInterval (1040825897 / 1000000000000) (1040825935 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (546167966661261 / 4000000000000) 4 (IntervalRat.scale (597 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-53639626748 / 1000000000000) (-53639551219 / 1000000000000), orderedInterval (42448406355 / 1000000000000) (42448481884 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2220142462139181 / 4000000000000) 4 (IntervalRat.scale (597 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (8086876665 / 1000000000000) (8086876673 / 1000000000000), orderedInterval (-32894849315 / 1000000000000) (-32894849307 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1482952274285379 / 4000000000000) 4 (IntervalRat.scale (597 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (30161595923 / 1000000000000) (30161595924 / 1000000000000), orderedInterval (28374927950 / 1000000000000) (28374927951 / 1000000000000)))) (orderedInterval (-21301685671 / 1000000000000) (-21301685217 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate427_chunkChecks4 :
    compactCertificate427.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate427.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate427_chunkChecks4_0
    compactCertificate427_chunkChecks4_1 compactCertificate427_chunkChecks4_2

theorem compactCertificate427_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate427.chunkCheck r b = true :=
  compactCertificate427.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate427_chunkChecks0
    · exact compactCertificate427_chunkChecks1
    · exact compactCertificate427_chunkChecks2
    · exact compactCertificate427_chunkChecks3
    · exact compactCertificate427_chunkChecks4)

theorem compactCertificate427_coefficient0 :
    compactCertificate427.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate427_coefficient1 :
    compactCertificate427.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate427_coefficient2 :
    compactCertificate427.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate427_coefficient3 :
    compactCertificate427.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate427_coefficient4 :
    compactCertificate427.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate427_coefficients : ∀ r : Fin 5,
    compactCertificate427.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate427_coefficient0
  · exact compactCertificate427_coefficient1
  · exact compactCertificate427_coefficient2
  · exact compactCertificate427_coefficient3
  · exact compactCertificate427_coefficient4

theorem compactCertificate427_lower : (1 : ℚ) ≤ compactCertificate427.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate427, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate427_proves {t : ℝ} (ht : t ∈ compactCertificate427.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate427.proves compactCertificate427_states compactCertificate427_chunks
    compactCertificate427_coefficients compactCertificate427_lower ht

end Erdos232
