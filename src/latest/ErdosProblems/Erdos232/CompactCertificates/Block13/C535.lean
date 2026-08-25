/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate535 : CompactCertificate where
  left := 406
  right := 407
  center := 813 / 2
  grid := fun i =>
    match i.val with
    | 0 => 129
    | 1 => 95
    | 2 => 154
    | 3 => 28
    | 4 => 75
    | 5 => 203
    | 6 => 149
    | 7 => 256
    | 8 => 189
    | 9 => 289
    | 10 => 167
    | 11 => 297
    | 12 => 277
    | 13 => 198
    | 14 => 224
    | 15 => 187
    | 16 => 165
    | 17 => 239
    | 18 => 132
    | 19 => 112
    | 20 => 70
    | 21 => 38
    | 22 => 103
    | 23 => 140
    | 24 => 59
    | 25 => 241
    | _ => 161
  point := fun i =>
    match i.val with
    | 0 => 813 / 2
    | 1 => 1197704240643513 / 4000000000000
    | 2 => 387312943037529 / 800000000000
    | 3 => 349487110302891 / 4000000000000
    | 4 => 938771537702127 / 4000000000000
    | 5 => 2548947341932659 / 4000000000000
    | 6 => 1877543075405067 / 4000000000000
    | 7 => 3217202061403191 / 4000000000000
    | 8 => 2369776477212069 / 4000000000000
    | 9 => 3635846531414187 / 4000000000000
    | 10 => 2099156973643923 / 4000000000000
    | 11 => 3724990886417007 / 4000000000000
    | 12 => 3480369679199883 / 4000000000000
    | 13 => 2483756026665339 / 4000000000000
    | 14 => 2816314613106381 / 4000000000000
    | 15 => 2347949508849789 / 4000000000000
    | 16 => 2074484597233569 / 4000000000000
    | 17 => 601266493199331 / 800000000000
    | 18 => 1663134763111257 / 4000000000000
    | 19 => 1409857757402577 / 4000000000000
    | 20 => 882223522787931 / 4000000000000
    | 21 => 474462744698277 / 4000000000000
    | 22 => 1288258648005831 / 4000000000000
    | 23 => 1759007047232487 / 4000000000000
    | 24 => 743776477212069 / 4000000000000
    | 25 => 3023410086631749 / 4000000000000
    | _ => 2019497820760491 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-35654193364 / 1000000000000) (-35654156596 / 1000000000000), orderedInterval (17215886977 / 1000000000000) (17215923745 / 1000000000000))
    | 1 => (orderedInterval (-45289383351 / 1000000000000) (-45289381847 / 1000000000000), orderedInterval (8736027260 / 1000000000000) (8736028764 / 1000000000000))
    | 2 => (orderedInterval (32656178723 / 1000000000000) (32656178724 / 1000000000000), orderedInterval (15730794574 / 1000000000000) (15730794576 / 1000000000000))
    | 3 => (orderedInterval (16217324662 / 1000000000000) (16217324663 / 1000000000000), orderedInterval (83713168839 / 1000000000000) (83713168840 / 1000000000000))
    | 4 => (orderedInterval (7355330477 / 1000000000000) (7355330497 / 1000000000000), orderedInterval (-51576026095 / 1000000000000) (-51576026074 / 1000000000000))
    | 5 => (orderedInterval (-8696277920 / 1000000000000) (-8696277919 / 1000000000000), orderedInterval (-30380783746 / 1000000000000) (-30380783745 / 1000000000000))
    | 6 => (orderedInterval (-32269867573 / 1000000000000) (-32269789571 / 1000000000000), orderedInterval (17780892716 / 1000000000000) (17780970719 / 1000000000000))
    | 7 => (orderedInterval (20912890035 / 1000000000000) (20912890036 / 1000000000000), orderedInterval (18806425496 / 1000000000000) (18806425497 / 1000000000000))
    | 8 => (orderedInterval (16619863114 / 1000000000000) (16619863509 / 1000000000000), orderedInterval (-28269033805 / 1000000000000) (-28269033410 / 1000000000000))
    | 9 => (orderedInterval (-25603481618 / 1000000000000) (-25603418218 / 1000000000000), orderedInterval (6710660515 / 1000000000000) (6710723914 / 1000000000000))
    | 10 => (orderedInterval (-27887318017 / 1000000000000) (-27887318016 / 1000000000000), orderedInterval (-20839512902 / 1000000000000) (-20839512901 / 1000000000000))
    | 11 => (orderedInterval (22279766149 / 1000000000000) (22279779531 / 1000000000000), orderedInterval (-13695239419 / 1000000000000) (-13695226037 / 1000000000000))
    | 12 => (orderedInterval (-16509737500 / 1000000000000) (-16509737499 / 1000000000000), orderedInterval (-21417078838 / 1000000000000) (-21417078837 / 1000000000000))
    | 13 => (orderedInterval (-9802660517 / 1000000000000) (-9802660503 / 1000000000000), orderedInterval (30490042734 / 1000000000000) (30490042748 / 1000000000000))
    | 14 => (orderedInterval (27411062946 / 1000000000000) (27411062951 / 1000000000000), orderedInterval (12342649915 / 1000000000000) (12342649921 / 1000000000000))
    | 15 => (orderedInterval (-9566497422 / 1000000000000) (-9566497421 / 1000000000000), orderedInterval (-31504339271 / 1000000000000) (-31504339270 / 1000000000000))
    | 16 => (orderedInterval (-30277436195 / 1000000000000) (-30277436194 / 1000000000000), orderedInterval (-17600339336 / 1000000000000) (-17600339335 / 1000000000000))
    | 17 => (orderedInterval (-29076904007 / 1000000000000) (-29076902553 / 1000000000000), orderedInterval (-1234420774 / 1000000000000) (-1234419320 / 1000000000000))
    | 18 => (orderedInterval (37291117435 / 1000000000000) (37291127529 / 1000000000000), orderedInterval (-11898262627 / 1000000000000) (-11898252533 / 1000000000000))
    | 19 => (orderedInterval (41815059635 / 1000000000000) (41815059649 / 1000000000000), orderedInterval (7536393661 / 1000000000000) (7536393675 / 1000000000000))
    | 20 => (orderedInterval (53187979195 / 1000000000000) (53187979204 / 1000000000000), orderedInterval (7459974086 / 1000000000000) (7459974095 / 1000000000000))
    | 21 => (orderedInterval (1429191710 / 1000000000000) (1429191714 / 1000000000000), orderedInterval (73240710523 / 1000000000000) (73240710527 / 1000000000000))
    | 22 => (orderedInterval (29793471790 / 1000000000000) (29793488516 / 1000000000000), orderedInterval (-33046744628 / 1000000000000) (-33046727902 / 1000000000000))
    | 23 => (orderedInterval (24913681265 / 1000000000000) (24913681266 / 1000000000000), orderedInterval (28729080567 / 1000000000000) (28729080568 / 1000000000000))
    | 24 => (orderedInterval (-57393043917 / 1000000000000) (-57393043914 / 1000000000000), orderedInterval (-11236134144 / 1000000000000) (-11236134141 / 1000000000000))
    | 25 => (orderedInterval (13557710763 / 1000000000000) (13557710832 / 1000000000000), orderedInterval (-25669103598 / 1000000000000) (-25669103529 / 1000000000000))
    | _ => (orderedInterval (4843006805 / 1000000000000) (4843006808 / 1000000000000), orderedInterval (-35182808823 / 1000000000000) (-35182808820 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-12637781513 / 1000000000000) (-12637766897 / 1000000000000)
      | 1 => orderedInterval (710824734 / 1000000000000) (710824784 / 1000000000000)
      | 2 => orderedInterval (-243367912 / 1000000000000) (-243367879 / 1000000000000)
      | 3 => orderedInterval (5650397451 / 1000000000000) (5650410780 / 1000000000000)
      | 4 => orderedInterval (-767631754 / 1000000000000) (-767631704 / 1000000000000)
      | 5 => orderedInterval (877722690 / 1000000000000) (877722767 / 1000000000000)
      | 6 => orderedInterval (-6597750956 / 1000000000000) (-6597749239 / 1000000000000)
      | 7 => orderedInterval (-2611667359 / 1000000000000) (-2611666930 / 1000000000000)
      | _ => orderedInterval (-2358282451 / 1000000000000) (-2358282332 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (7983148371 / 1000000000000) (7983162987 / 1000000000000)
      | 1 => orderedInterval (2103239984 / 1000000000000) (2103240040 / 1000000000000)
      | 2 => orderedInterval (-2143440955 / 1000000000000) (-2143440901 / 1000000000000)
      | 3 => orderedInterval (-9119706990 / 1000000000000) (-9119677109 / 1000000000000)
      | 4 => orderedInterval (5123607127 / 1000000000000) (5123607208 / 1000000000000)
      | 5 => orderedInterval (701250327 / 1000000000000) (701250453 / 1000000000000)
      | 6 => orderedInterval (1707801307 / 1000000000000) (1707803053 / 1000000000000)
      | 7 => orderedInterval (-2182496796 / 1000000000000) (-2182496451 / 1000000000000)
      | _ => orderedInterval (12053034236 / 1000000000000) (12053034405 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (11623157393 / 1000000000000) (11623172047 / 1000000000000)
      | 1 => orderedInterval (-1605783351 / 1000000000000) (-1605783273 / 1000000000000)
      | 2 => orderedInterval (1677316207 / 1000000000000) (1677316299 / 1000000000000)
      | 3 => orderedInterval (-35903081911 / 1000000000000) (-35903014811 / 1000000000000)
      | 4 => orderedInterval (1200937466 / 1000000000000) (1200937600 / 1000000000000)
      | 5 => orderedInterval (-46686819 / 1000000000000) (-46686607 / 1000000000000)
      | 6 => orderedInterval (7503418848 / 1000000000000) (7503420632 / 1000000000000)
      | 7 => orderedInterval (2666407508 / 1000000000000) (2666407791 / 1000000000000)
      | _ => orderedInterval (5260134240 / 1000000000000) (5260134493 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-8444361378 / 1000000000000) (-8444346720 / 1000000000000)
      | 1 => orderedInterval (-7944666259 / 1000000000000) (-7944666144 / 1000000000000)
      | 2 => orderedInterval (6604016201 / 1000000000000) (6604016359 / 1000000000000)
      | 3 => orderedInterval (40149104258 / 1000000000000) (40149254811 / 1000000000000)
      | 4 => orderedInterval (-13746466225 / 1000000000000) (-13746466000 / 1000000000000)
      | 5 => orderedInterval (-796372544 / 1000000000000) (-796372179 / 1000000000000)
      | 6 => orderedInterval (-1814962305 / 1000000000000) (-1814960485 / 1000000000000)
      | 7 => orderedInterval (2441645036 / 1000000000000) (2441645271 / 1000000000000)
      | _ => orderedInterval (-26086587074 / 1000000000000) (-26086586676 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-10358932346 / 1000000000000) (-10358917646 / 1000000000000)
      | 1 => orderedInterval (3801912245 / 1000000000000) (3801912422 / 1000000000000)
      | 2 => orderedInterval (-8106134794 / 1000000000000) (-8106134512 / 1000000000000)
      | 3 => orderedInterval (195033886782 / 1000000000000) (195034225028 / 1000000000000)
      | 4 => orderedInterval (28579227 / 1000000000000) (28579618 / 1000000000000)
      | 5 => orderedInterval (-4585752927 / 1000000000000) (-4585752286 / 1000000000000)
      | 6 => orderedInterval (-7704902364 / 1000000000000) (-7704900503 / 1000000000000)
      | 7 => orderedInterval (-2893542559 / 1000000000000) (-2893542362 / 1000000000000)
      | _ => orderedInterval (-15241469226 / 1000000000000) (-15241468579 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-17977537070 / 1000000000000) (-17977506650 / 1000000000000)
    | 1 => orderedInterval (16226436611 / 1000000000000) (16226483685 / 1000000000000)
    | 2 => orderedInterval (-7624180419 / 1000000000000) (-7624095829 / 1000000000000)
    | 3 => orderedInterval (-9638650290 / 1000000000000) (-9638481763 / 1000000000000)
    | _ => orderedInterval (149973644038 / 1000000000000) (149974001180 / 1000000000000)

theorem compactCertificate535_stateChecks0 :
    compactCertificate535.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 129 12 (813 / 2)) (orderedInterval (-35654193364 / 1000000000000) (-35654156596 / 1000000000000), orderedInterval (17215886977 / 1000000000000) (17215923745 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 95 12 (1197704240643513 / 4000000000000)) (orderedInterval (-45289383351 / 1000000000000) (-45289381847 / 1000000000000), orderedInterval (8736027260 / 1000000000000) (8736028764 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 154 12 (387312943037529 / 800000000000)) (orderedInterval (32656178723 / 1000000000000) (32656178724 / 1000000000000), orderedInterval (15730794574 / 1000000000000) (15730794576 / 1000000000000))) = true
  rfl'

theorem compactCertificate535_stateChecks1 :
    compactCertificate535.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 28 12 (349487110302891 / 4000000000000)) (orderedInterval (16217324662 / 1000000000000) (16217324663 / 1000000000000), orderedInterval (83713168839 / 1000000000000) (83713168840 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 75 12 (938771537702127 / 4000000000000)) (orderedInterval (7355330477 / 1000000000000) (7355330497 / 1000000000000), orderedInterval (-51576026095 / 1000000000000) (-51576026074 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 203 12 (2548947341932659 / 4000000000000)) (orderedInterval (-8696277920 / 1000000000000) (-8696277919 / 1000000000000), orderedInterval (-30380783746 / 1000000000000) (-30380783745 / 1000000000000))) = true
  rfl'

theorem compactCertificate535_stateChecks2 :
    compactCertificate535.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 149 12 (1877543075405067 / 4000000000000)) (orderedInterval (-32269867573 / 1000000000000) (-32269789571 / 1000000000000), orderedInterval (17780892716 / 1000000000000) (17780970719 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 256 12 (3217202061403191 / 4000000000000)) (orderedInterval (20912890035 / 1000000000000) (20912890036 / 1000000000000), orderedInterval (18806425496 / 1000000000000) (18806425497 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 189 12 (2369776477212069 / 4000000000000)) (orderedInterval (16619863114 / 1000000000000) (16619863509 / 1000000000000), orderedInterval (-28269033805 / 1000000000000) (-28269033410 / 1000000000000))) = true
  rfl'

theorem compactCertificate535_stateChecks3 :
    compactCertificate535.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 289 12 (3635846531414187 / 4000000000000)) (orderedInterval (-25603481618 / 1000000000000) (-25603418218 / 1000000000000), orderedInterval (6710660515 / 1000000000000) (6710723914 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 167 12 (2099156973643923 / 4000000000000)) (orderedInterval (-27887318017 / 1000000000000) (-27887318016 / 1000000000000), orderedInterval (-20839512902 / 1000000000000) (-20839512901 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 297 12 (3724990886417007 / 4000000000000)) (orderedInterval (22279766149 / 1000000000000) (22279779531 / 1000000000000), orderedInterval (-13695239419 / 1000000000000) (-13695226037 / 1000000000000))) = true
  rfl'

theorem compactCertificate535_stateChecks4 :
    compactCertificate535.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 277 12 (3480369679199883 / 4000000000000)) (orderedInterval (-16509737500 / 1000000000000) (-16509737499 / 1000000000000), orderedInterval (-21417078838 / 1000000000000) (-21417078837 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 198 12 (2483756026665339 / 4000000000000)) (orderedInterval (-9802660517 / 1000000000000) (-9802660503 / 1000000000000), orderedInterval (30490042734 / 1000000000000) (30490042748 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 224 12 (2816314613106381 / 4000000000000)) (orderedInterval (27411062946 / 1000000000000) (27411062951 / 1000000000000), orderedInterval (12342649915 / 1000000000000) (12342649921 / 1000000000000))) = true
  rfl'

theorem compactCertificate535_stateChecks5 :
    compactCertificate535.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 187 12 (2347949508849789 / 4000000000000)) (orderedInterval (-9566497422 / 1000000000000) (-9566497421 / 1000000000000), orderedInterval (-31504339271 / 1000000000000) (-31504339270 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 165 12 (2074484597233569 / 4000000000000)) (orderedInterval (-30277436195 / 1000000000000) (-30277436194 / 1000000000000), orderedInterval (-17600339336 / 1000000000000) (-17600339335 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 239 12 (601266493199331 / 800000000000)) (orderedInterval (-29076904007 / 1000000000000) (-29076902553 / 1000000000000), orderedInterval (-1234420774 / 1000000000000) (-1234419320 / 1000000000000))) = true
  rfl'

theorem compactCertificate535_stateChecks6 :
    compactCertificate535.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 132 12 (1663134763111257 / 4000000000000)) (orderedInterval (37291117435 / 1000000000000) (37291127529 / 1000000000000), orderedInterval (-11898262627 / 1000000000000) (-11898252533 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 112 12 (1409857757402577 / 4000000000000)) (orderedInterval (41815059635 / 1000000000000) (41815059649 / 1000000000000), orderedInterval (7536393661 / 1000000000000) (7536393675 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (882223522787931 / 4000000000000)) (orderedInterval (53187979195 / 1000000000000) (53187979204 / 1000000000000), orderedInterval (7459974086 / 1000000000000) (7459974095 / 1000000000000))) = true
  rfl'

theorem compactCertificate535_stateChecks7 :
    compactCertificate535.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (474462744698277 / 4000000000000)) (orderedInterval (1429191710 / 1000000000000) (1429191714 / 1000000000000), orderedInterval (73240710523 / 1000000000000) (73240710527 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 103 12 (1288258648005831 / 4000000000000)) (orderedInterval (29793471790 / 1000000000000) (29793488516 / 1000000000000), orderedInterval (-33046744628 / 1000000000000) (-33046727902 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 140 12 (1759007047232487 / 4000000000000)) (orderedInterval (24913681265 / 1000000000000) (24913681266 / 1000000000000), orderedInterval (28729080567 / 1000000000000) (28729080568 / 1000000000000))) = true
  rfl'

theorem compactCertificate535_stateChecks8 :
    compactCertificate535.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 59 12 (743776477212069 / 4000000000000)) (orderedInterval (-57393043917 / 1000000000000) (-57393043914 / 1000000000000), orderedInterval (-11236134144 / 1000000000000) (-11236134141 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 241 12 (3023410086631749 / 4000000000000)) (orderedInterval (13557710763 / 1000000000000) (13557710832 / 1000000000000), orderedInterval (-25669103598 / 1000000000000) (-25669103529 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 161 12 (2019497820760491 / 4000000000000)) (orderedInterval (4843006805 / 1000000000000) (4843006808 / 1000000000000), orderedInterval (-35182808823 / 1000000000000) (-35182808820 / 1000000000000))) = true
  rfl'

theorem compactCertificate535_states : ∀ j,
    BesselStateValid (compactCertificate535.point j) (compactCertificate535.state j) :=
  compactCertificate535.statesValid_of_checks3 compactCertificate535_stateChecks0
    compactCertificate535_stateChecks1 compactCertificate535_stateChecks2
    compactCertificate535_stateChecks3 compactCertificate535_stateChecks4
    compactCertificate535_stateChecks5 compactCertificate535_stateChecks6
    compactCertificate535_stateChecks7 compactCertificate535_stateChecks8

theorem compactCertificate535_chunkChecks0_0 :
    compactCertificate535.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (813 / 2) 0 (IntervalRat.scale (813 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-35654193364 / 1000000000000) (-35654156596 / 1000000000000), orderedInterval (17215886977 / 1000000000000) (17215923745 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1197704240643513 / 4000000000000) 0 (IntervalRat.scale (813 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-45289383351 / 1000000000000) (-45289381847 / 1000000000000), orderedInterval (8736027260 / 1000000000000) (8736028764 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (387312943037529 / 800000000000) 0 (IntervalRat.scale (813 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (32656178723 / 1000000000000) (32656178724 / 1000000000000), orderedInterval (15730794574 / 1000000000000) (15730794576 / 1000000000000)))) (orderedInterval (-12637781513 / 1000000000000) (-12637766897 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (349487110302891 / 4000000000000) 0 (IntervalRat.scale (813 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (16217324662 / 1000000000000) (16217324663 / 1000000000000), orderedInterval (83713168839 / 1000000000000) (83713168840 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (938771537702127 / 4000000000000) 0 (IntervalRat.scale (813 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (7355330477 / 1000000000000) (7355330497 / 1000000000000), orderedInterval (-51576026095 / 1000000000000) (-51576026074 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2548947341932659 / 4000000000000) 0 (IntervalRat.scale (813 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-8696277920 / 1000000000000) (-8696277919 / 1000000000000), orderedInterval (-30380783746 / 1000000000000) (-30380783745 / 1000000000000)))) (orderedInterval (710824734 / 1000000000000) (710824784 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1877543075405067 / 4000000000000) 0 (IntervalRat.scale (813 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-32269867573 / 1000000000000) (-32269789571 / 1000000000000), orderedInterval (17780892716 / 1000000000000) (17780970719 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3217202061403191 / 4000000000000) 0 (IntervalRat.scale (813 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (20912890035 / 1000000000000) (20912890036 / 1000000000000), orderedInterval (18806425496 / 1000000000000) (18806425497 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2369776477212069 / 4000000000000) 0 (IntervalRat.scale (813 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (16619863114 / 1000000000000) (16619863509 / 1000000000000), orderedInterval (-28269033805 / 1000000000000) (-28269033410 / 1000000000000)))) (orderedInterval (-243367912 / 1000000000000) (-243367879 / 1000000000000))) = true
  rfl'

theorem compactCertificate535_chunkChecks0_1 :
    compactCertificate535.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3635846531414187 / 4000000000000) 0 (IntervalRat.scale (813 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-25603481618 / 1000000000000) (-25603418218 / 1000000000000), orderedInterval (6710660515 / 1000000000000) (6710723914 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2099156973643923 / 4000000000000) 0 (IntervalRat.scale (813 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-27887318017 / 1000000000000) (-27887318016 / 1000000000000), orderedInterval (-20839512902 / 1000000000000) (-20839512901 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3724990886417007 / 4000000000000) 0 (IntervalRat.scale (813 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (22279766149 / 1000000000000) (22279779531 / 1000000000000), orderedInterval (-13695239419 / 1000000000000) (-13695226037 / 1000000000000)))) (orderedInterval (5650397451 / 1000000000000) (5650410780 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3480369679199883 / 4000000000000) 0 (IntervalRat.scale (813 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-16509737500 / 1000000000000) (-16509737499 / 1000000000000), orderedInterval (-21417078838 / 1000000000000) (-21417078837 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2483756026665339 / 4000000000000) 0 (IntervalRat.scale (813 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-9802660517 / 1000000000000) (-9802660503 / 1000000000000), orderedInterval (30490042734 / 1000000000000) (30490042748 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2816314613106381 / 4000000000000) 0 (IntervalRat.scale (813 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (27411062946 / 1000000000000) (27411062951 / 1000000000000), orderedInterval (12342649915 / 1000000000000) (12342649921 / 1000000000000)))) (orderedInterval (-767631754 / 1000000000000) (-767631704 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2347949508849789 / 4000000000000) 0 (IntervalRat.scale (813 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-9566497422 / 1000000000000) (-9566497421 / 1000000000000), orderedInterval (-31504339271 / 1000000000000) (-31504339270 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2074484597233569 / 4000000000000) 0 (IntervalRat.scale (813 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-30277436195 / 1000000000000) (-30277436194 / 1000000000000), orderedInterval (-17600339336 / 1000000000000) (-17600339335 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (601266493199331 / 800000000000) 0 (IntervalRat.scale (813 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-29076904007 / 1000000000000) (-29076902553 / 1000000000000), orderedInterval (-1234420774 / 1000000000000) (-1234419320 / 1000000000000)))) (orderedInterval (877722690 / 1000000000000) (877722767 / 1000000000000))) = true
  rfl'

theorem compactCertificate535_chunkChecks0_2 :
    compactCertificate535.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1663134763111257 / 4000000000000) 0 (IntervalRat.scale (813 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (37291117435 / 1000000000000) (37291127529 / 1000000000000), orderedInterval (-11898262627 / 1000000000000) (-11898252533 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1409857757402577 / 4000000000000) 0 (IntervalRat.scale (813 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (41815059635 / 1000000000000) (41815059649 / 1000000000000), orderedInterval (7536393661 / 1000000000000) (7536393675 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (882223522787931 / 4000000000000) 0 (IntervalRat.scale (813 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (53187979195 / 1000000000000) (53187979204 / 1000000000000), orderedInterval (7459974086 / 1000000000000) (7459974095 / 1000000000000)))) (orderedInterval (-6597750956 / 1000000000000) (-6597749239 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (474462744698277 / 4000000000000) 0 (IntervalRat.scale (813 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (1429191710 / 1000000000000) (1429191714 / 1000000000000), orderedInterval (73240710523 / 1000000000000) (73240710527 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1288258648005831 / 4000000000000) 0 (IntervalRat.scale (813 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (29793471790 / 1000000000000) (29793488516 / 1000000000000), orderedInterval (-33046744628 / 1000000000000) (-33046727902 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1759007047232487 / 4000000000000) 0 (IntervalRat.scale (813 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (24913681265 / 1000000000000) (24913681266 / 1000000000000), orderedInterval (28729080567 / 1000000000000) (28729080568 / 1000000000000)))) (orderedInterval (-2611667359 / 1000000000000) (-2611666930 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (743776477212069 / 4000000000000) 0 (IntervalRat.scale (813 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-57393043917 / 1000000000000) (-57393043914 / 1000000000000), orderedInterval (-11236134144 / 1000000000000) (-11236134141 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3023410086631749 / 4000000000000) 0 (IntervalRat.scale (813 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (13557710763 / 1000000000000) (13557710832 / 1000000000000), orderedInterval (-25669103598 / 1000000000000) (-25669103529 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2019497820760491 / 4000000000000) 0 (IntervalRat.scale (813 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (4843006805 / 1000000000000) (4843006808 / 1000000000000), orderedInterval (-35182808823 / 1000000000000) (-35182808820 / 1000000000000)))) (orderedInterval (-2358282451 / 1000000000000) (-2358282332 / 1000000000000))) = true
  rfl'

theorem compactCertificate535_chunkChecks0 :
    compactCertificate535.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate535.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate535_chunkChecks0_0
    compactCertificate535_chunkChecks0_1 compactCertificate535_chunkChecks0_2

theorem compactCertificate535_chunkChecks1_0 :
    compactCertificate535.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (813 / 2) 1 (IntervalRat.scale (813 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-35654193364 / 1000000000000) (-35654156596 / 1000000000000), orderedInterval (17215886977 / 1000000000000) (17215923745 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1197704240643513 / 4000000000000) 1 (IntervalRat.scale (813 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-45289383351 / 1000000000000) (-45289381847 / 1000000000000), orderedInterval (8736027260 / 1000000000000) (8736028764 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (387312943037529 / 800000000000) 1 (IntervalRat.scale (813 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (32656178723 / 1000000000000) (32656178724 / 1000000000000), orderedInterval (15730794574 / 1000000000000) (15730794576 / 1000000000000)))) (orderedInterval (7983148371 / 1000000000000) (7983162987 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (349487110302891 / 4000000000000) 1 (IntervalRat.scale (813 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (16217324662 / 1000000000000) (16217324663 / 1000000000000), orderedInterval (83713168839 / 1000000000000) (83713168840 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (938771537702127 / 4000000000000) 1 (IntervalRat.scale (813 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (7355330477 / 1000000000000) (7355330497 / 1000000000000), orderedInterval (-51576026095 / 1000000000000) (-51576026074 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2548947341932659 / 4000000000000) 1 (IntervalRat.scale (813 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-8696277920 / 1000000000000) (-8696277919 / 1000000000000), orderedInterval (-30380783746 / 1000000000000) (-30380783745 / 1000000000000)))) (orderedInterval (2103239984 / 1000000000000) (2103240040 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1877543075405067 / 4000000000000) 1 (IntervalRat.scale (813 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-32269867573 / 1000000000000) (-32269789571 / 1000000000000), orderedInterval (17780892716 / 1000000000000) (17780970719 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3217202061403191 / 4000000000000) 1 (IntervalRat.scale (813 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (20912890035 / 1000000000000) (20912890036 / 1000000000000), orderedInterval (18806425496 / 1000000000000) (18806425497 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2369776477212069 / 4000000000000) 1 (IntervalRat.scale (813 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (16619863114 / 1000000000000) (16619863509 / 1000000000000), orderedInterval (-28269033805 / 1000000000000) (-28269033410 / 1000000000000)))) (orderedInterval (-2143440955 / 1000000000000) (-2143440901 / 1000000000000))) = true
  rfl'

theorem compactCertificate535_chunkChecks1_1 :
    compactCertificate535.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3635846531414187 / 4000000000000) 1 (IntervalRat.scale (813 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-25603481618 / 1000000000000) (-25603418218 / 1000000000000), orderedInterval (6710660515 / 1000000000000) (6710723914 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2099156973643923 / 4000000000000) 1 (IntervalRat.scale (813 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-27887318017 / 1000000000000) (-27887318016 / 1000000000000), orderedInterval (-20839512902 / 1000000000000) (-20839512901 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3724990886417007 / 4000000000000) 1 (IntervalRat.scale (813 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (22279766149 / 1000000000000) (22279779531 / 1000000000000), orderedInterval (-13695239419 / 1000000000000) (-13695226037 / 1000000000000)))) (orderedInterval (-9119706990 / 1000000000000) (-9119677109 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3480369679199883 / 4000000000000) 1 (IntervalRat.scale (813 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-16509737500 / 1000000000000) (-16509737499 / 1000000000000), orderedInterval (-21417078838 / 1000000000000) (-21417078837 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2483756026665339 / 4000000000000) 1 (IntervalRat.scale (813 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-9802660517 / 1000000000000) (-9802660503 / 1000000000000), orderedInterval (30490042734 / 1000000000000) (30490042748 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2816314613106381 / 4000000000000) 1 (IntervalRat.scale (813 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (27411062946 / 1000000000000) (27411062951 / 1000000000000), orderedInterval (12342649915 / 1000000000000) (12342649921 / 1000000000000)))) (orderedInterval (5123607127 / 1000000000000) (5123607208 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2347949508849789 / 4000000000000) 1 (IntervalRat.scale (813 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-9566497422 / 1000000000000) (-9566497421 / 1000000000000), orderedInterval (-31504339271 / 1000000000000) (-31504339270 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2074484597233569 / 4000000000000) 1 (IntervalRat.scale (813 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-30277436195 / 1000000000000) (-30277436194 / 1000000000000), orderedInterval (-17600339336 / 1000000000000) (-17600339335 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (601266493199331 / 800000000000) 1 (IntervalRat.scale (813 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-29076904007 / 1000000000000) (-29076902553 / 1000000000000), orderedInterval (-1234420774 / 1000000000000) (-1234419320 / 1000000000000)))) (orderedInterval (701250327 / 1000000000000) (701250453 / 1000000000000))) = true
  rfl'

theorem compactCertificate535_chunkChecks1_2 :
    compactCertificate535.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1663134763111257 / 4000000000000) 1 (IntervalRat.scale (813 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (37291117435 / 1000000000000) (37291127529 / 1000000000000), orderedInterval (-11898262627 / 1000000000000) (-11898252533 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1409857757402577 / 4000000000000) 1 (IntervalRat.scale (813 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (41815059635 / 1000000000000) (41815059649 / 1000000000000), orderedInterval (7536393661 / 1000000000000) (7536393675 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (882223522787931 / 4000000000000) 1 (IntervalRat.scale (813 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (53187979195 / 1000000000000) (53187979204 / 1000000000000), orderedInterval (7459974086 / 1000000000000) (7459974095 / 1000000000000)))) (orderedInterval (1707801307 / 1000000000000) (1707803053 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (474462744698277 / 4000000000000) 1 (IntervalRat.scale (813 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (1429191710 / 1000000000000) (1429191714 / 1000000000000), orderedInterval (73240710523 / 1000000000000) (73240710527 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1288258648005831 / 4000000000000) 1 (IntervalRat.scale (813 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (29793471790 / 1000000000000) (29793488516 / 1000000000000), orderedInterval (-33046744628 / 1000000000000) (-33046727902 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1759007047232487 / 4000000000000) 1 (IntervalRat.scale (813 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (24913681265 / 1000000000000) (24913681266 / 1000000000000), orderedInterval (28729080567 / 1000000000000) (28729080568 / 1000000000000)))) (orderedInterval (-2182496796 / 1000000000000) (-2182496451 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (743776477212069 / 4000000000000) 1 (IntervalRat.scale (813 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-57393043917 / 1000000000000) (-57393043914 / 1000000000000), orderedInterval (-11236134144 / 1000000000000) (-11236134141 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3023410086631749 / 4000000000000) 1 (IntervalRat.scale (813 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (13557710763 / 1000000000000) (13557710832 / 1000000000000), orderedInterval (-25669103598 / 1000000000000) (-25669103529 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2019497820760491 / 4000000000000) 1 (IntervalRat.scale (813 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (4843006805 / 1000000000000) (4843006808 / 1000000000000), orderedInterval (-35182808823 / 1000000000000) (-35182808820 / 1000000000000)))) (orderedInterval (12053034236 / 1000000000000) (12053034405 / 1000000000000))) = true
  rfl'

theorem compactCertificate535_chunkChecks1 :
    compactCertificate535.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate535.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate535_chunkChecks1_0
    compactCertificate535_chunkChecks1_1 compactCertificate535_chunkChecks1_2

theorem compactCertificate535_chunkChecks2_0 :
    compactCertificate535.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (813 / 2) 2 (IntervalRat.scale (813 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-35654193364 / 1000000000000) (-35654156596 / 1000000000000), orderedInterval (17215886977 / 1000000000000) (17215923745 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1197704240643513 / 4000000000000) 2 (IntervalRat.scale (813 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-45289383351 / 1000000000000) (-45289381847 / 1000000000000), orderedInterval (8736027260 / 1000000000000) (8736028764 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (387312943037529 / 800000000000) 2 (IntervalRat.scale (813 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (32656178723 / 1000000000000) (32656178724 / 1000000000000), orderedInterval (15730794574 / 1000000000000) (15730794576 / 1000000000000)))) (orderedInterval (11623157393 / 1000000000000) (11623172047 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (349487110302891 / 4000000000000) 2 (IntervalRat.scale (813 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (16217324662 / 1000000000000) (16217324663 / 1000000000000), orderedInterval (83713168839 / 1000000000000) (83713168840 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (938771537702127 / 4000000000000) 2 (IntervalRat.scale (813 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (7355330477 / 1000000000000) (7355330497 / 1000000000000), orderedInterval (-51576026095 / 1000000000000) (-51576026074 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2548947341932659 / 4000000000000) 2 (IntervalRat.scale (813 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-8696277920 / 1000000000000) (-8696277919 / 1000000000000), orderedInterval (-30380783746 / 1000000000000) (-30380783745 / 1000000000000)))) (orderedInterval (-1605783351 / 1000000000000) (-1605783273 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1877543075405067 / 4000000000000) 2 (IntervalRat.scale (813 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-32269867573 / 1000000000000) (-32269789571 / 1000000000000), orderedInterval (17780892716 / 1000000000000) (17780970719 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3217202061403191 / 4000000000000) 2 (IntervalRat.scale (813 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (20912890035 / 1000000000000) (20912890036 / 1000000000000), orderedInterval (18806425496 / 1000000000000) (18806425497 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2369776477212069 / 4000000000000) 2 (IntervalRat.scale (813 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (16619863114 / 1000000000000) (16619863509 / 1000000000000), orderedInterval (-28269033805 / 1000000000000) (-28269033410 / 1000000000000)))) (orderedInterval (1677316207 / 1000000000000) (1677316299 / 1000000000000))) = true
  rfl'

theorem compactCertificate535_chunkChecks2_1 :
    compactCertificate535.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3635846531414187 / 4000000000000) 2 (IntervalRat.scale (813 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-25603481618 / 1000000000000) (-25603418218 / 1000000000000), orderedInterval (6710660515 / 1000000000000) (6710723914 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2099156973643923 / 4000000000000) 2 (IntervalRat.scale (813 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-27887318017 / 1000000000000) (-27887318016 / 1000000000000), orderedInterval (-20839512902 / 1000000000000) (-20839512901 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3724990886417007 / 4000000000000) 2 (IntervalRat.scale (813 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (22279766149 / 1000000000000) (22279779531 / 1000000000000), orderedInterval (-13695239419 / 1000000000000) (-13695226037 / 1000000000000)))) (orderedInterval (-35903081911 / 1000000000000) (-35903014811 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3480369679199883 / 4000000000000) 2 (IntervalRat.scale (813 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-16509737500 / 1000000000000) (-16509737499 / 1000000000000), orderedInterval (-21417078838 / 1000000000000) (-21417078837 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2483756026665339 / 4000000000000) 2 (IntervalRat.scale (813 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-9802660517 / 1000000000000) (-9802660503 / 1000000000000), orderedInterval (30490042734 / 1000000000000) (30490042748 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2816314613106381 / 4000000000000) 2 (IntervalRat.scale (813 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (27411062946 / 1000000000000) (27411062951 / 1000000000000), orderedInterval (12342649915 / 1000000000000) (12342649921 / 1000000000000)))) (orderedInterval (1200937466 / 1000000000000) (1200937600 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2347949508849789 / 4000000000000) 2 (IntervalRat.scale (813 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-9566497422 / 1000000000000) (-9566497421 / 1000000000000), orderedInterval (-31504339271 / 1000000000000) (-31504339270 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2074484597233569 / 4000000000000) 2 (IntervalRat.scale (813 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-30277436195 / 1000000000000) (-30277436194 / 1000000000000), orderedInterval (-17600339336 / 1000000000000) (-17600339335 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (601266493199331 / 800000000000) 2 (IntervalRat.scale (813 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-29076904007 / 1000000000000) (-29076902553 / 1000000000000), orderedInterval (-1234420774 / 1000000000000) (-1234419320 / 1000000000000)))) (orderedInterval (-46686819 / 1000000000000) (-46686607 / 1000000000000))) = true
  rfl'

theorem compactCertificate535_chunkChecks2_2 :
    compactCertificate535.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1663134763111257 / 4000000000000) 2 (IntervalRat.scale (813 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (37291117435 / 1000000000000) (37291127529 / 1000000000000), orderedInterval (-11898262627 / 1000000000000) (-11898252533 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1409857757402577 / 4000000000000) 2 (IntervalRat.scale (813 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (41815059635 / 1000000000000) (41815059649 / 1000000000000), orderedInterval (7536393661 / 1000000000000) (7536393675 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (882223522787931 / 4000000000000) 2 (IntervalRat.scale (813 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (53187979195 / 1000000000000) (53187979204 / 1000000000000), orderedInterval (7459974086 / 1000000000000) (7459974095 / 1000000000000)))) (orderedInterval (7503418848 / 1000000000000) (7503420632 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (474462744698277 / 4000000000000) 2 (IntervalRat.scale (813 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (1429191710 / 1000000000000) (1429191714 / 1000000000000), orderedInterval (73240710523 / 1000000000000) (73240710527 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1288258648005831 / 4000000000000) 2 (IntervalRat.scale (813 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (29793471790 / 1000000000000) (29793488516 / 1000000000000), orderedInterval (-33046744628 / 1000000000000) (-33046727902 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1759007047232487 / 4000000000000) 2 (IntervalRat.scale (813 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (24913681265 / 1000000000000) (24913681266 / 1000000000000), orderedInterval (28729080567 / 1000000000000) (28729080568 / 1000000000000)))) (orderedInterval (2666407508 / 1000000000000) (2666407791 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (743776477212069 / 4000000000000) 2 (IntervalRat.scale (813 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-57393043917 / 1000000000000) (-57393043914 / 1000000000000), orderedInterval (-11236134144 / 1000000000000) (-11236134141 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3023410086631749 / 4000000000000) 2 (IntervalRat.scale (813 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (13557710763 / 1000000000000) (13557710832 / 1000000000000), orderedInterval (-25669103598 / 1000000000000) (-25669103529 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2019497820760491 / 4000000000000) 2 (IntervalRat.scale (813 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (4843006805 / 1000000000000) (4843006808 / 1000000000000), orderedInterval (-35182808823 / 1000000000000) (-35182808820 / 1000000000000)))) (orderedInterval (5260134240 / 1000000000000) (5260134493 / 1000000000000))) = true
  rfl'

theorem compactCertificate535_chunkChecks2 :
    compactCertificate535.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate535.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate535_chunkChecks2_0
    compactCertificate535_chunkChecks2_1 compactCertificate535_chunkChecks2_2

theorem compactCertificate535_chunkChecks3_0 :
    compactCertificate535.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (813 / 2) 3 (IntervalRat.scale (813 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-35654193364 / 1000000000000) (-35654156596 / 1000000000000), orderedInterval (17215886977 / 1000000000000) (17215923745 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1197704240643513 / 4000000000000) 3 (IntervalRat.scale (813 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-45289383351 / 1000000000000) (-45289381847 / 1000000000000), orderedInterval (8736027260 / 1000000000000) (8736028764 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (387312943037529 / 800000000000) 3 (IntervalRat.scale (813 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (32656178723 / 1000000000000) (32656178724 / 1000000000000), orderedInterval (15730794574 / 1000000000000) (15730794576 / 1000000000000)))) (orderedInterval (-8444361378 / 1000000000000) (-8444346720 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (349487110302891 / 4000000000000) 3 (IntervalRat.scale (813 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (16217324662 / 1000000000000) (16217324663 / 1000000000000), orderedInterval (83713168839 / 1000000000000) (83713168840 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (938771537702127 / 4000000000000) 3 (IntervalRat.scale (813 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (7355330477 / 1000000000000) (7355330497 / 1000000000000), orderedInterval (-51576026095 / 1000000000000) (-51576026074 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2548947341932659 / 4000000000000) 3 (IntervalRat.scale (813 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-8696277920 / 1000000000000) (-8696277919 / 1000000000000), orderedInterval (-30380783746 / 1000000000000) (-30380783745 / 1000000000000)))) (orderedInterval (-7944666259 / 1000000000000) (-7944666144 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1877543075405067 / 4000000000000) 3 (IntervalRat.scale (813 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-32269867573 / 1000000000000) (-32269789571 / 1000000000000), orderedInterval (17780892716 / 1000000000000) (17780970719 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3217202061403191 / 4000000000000) 3 (IntervalRat.scale (813 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (20912890035 / 1000000000000) (20912890036 / 1000000000000), orderedInterval (18806425496 / 1000000000000) (18806425497 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2369776477212069 / 4000000000000) 3 (IntervalRat.scale (813 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (16619863114 / 1000000000000) (16619863509 / 1000000000000), orderedInterval (-28269033805 / 1000000000000) (-28269033410 / 1000000000000)))) (orderedInterval (6604016201 / 1000000000000) (6604016359 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate535_chunkChecks3_1 :
    compactCertificate535.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3635846531414187 / 4000000000000) 3 (IntervalRat.scale (813 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-25603481618 / 1000000000000) (-25603418218 / 1000000000000), orderedInterval (6710660515 / 1000000000000) (6710723914 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2099156973643923 / 4000000000000) 3 (IntervalRat.scale (813 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-27887318017 / 1000000000000) (-27887318016 / 1000000000000), orderedInterval (-20839512902 / 1000000000000) (-20839512901 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3724990886417007 / 4000000000000) 3 (IntervalRat.scale (813 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (22279766149 / 1000000000000) (22279779531 / 1000000000000), orderedInterval (-13695239419 / 1000000000000) (-13695226037 / 1000000000000)))) (orderedInterval (40149104258 / 1000000000000) (40149254811 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3480369679199883 / 4000000000000) 3 (IntervalRat.scale (813 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-16509737500 / 1000000000000) (-16509737499 / 1000000000000), orderedInterval (-21417078838 / 1000000000000) (-21417078837 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2483756026665339 / 4000000000000) 3 (IntervalRat.scale (813 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-9802660517 / 1000000000000) (-9802660503 / 1000000000000), orderedInterval (30490042734 / 1000000000000) (30490042748 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2816314613106381 / 4000000000000) 3 (IntervalRat.scale (813 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (27411062946 / 1000000000000) (27411062951 / 1000000000000), orderedInterval (12342649915 / 1000000000000) (12342649921 / 1000000000000)))) (orderedInterval (-13746466225 / 1000000000000) (-13746466000 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2347949508849789 / 4000000000000) 3 (IntervalRat.scale (813 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-9566497422 / 1000000000000) (-9566497421 / 1000000000000), orderedInterval (-31504339271 / 1000000000000) (-31504339270 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2074484597233569 / 4000000000000) 3 (IntervalRat.scale (813 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-30277436195 / 1000000000000) (-30277436194 / 1000000000000), orderedInterval (-17600339336 / 1000000000000) (-17600339335 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (601266493199331 / 800000000000) 3 (IntervalRat.scale (813 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-29076904007 / 1000000000000) (-29076902553 / 1000000000000), orderedInterval (-1234420774 / 1000000000000) (-1234419320 / 1000000000000)))) (orderedInterval (-796372544 / 1000000000000) (-796372179 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate535_chunkChecks3_2 :
    compactCertificate535.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1663134763111257 / 4000000000000) 3 (IntervalRat.scale (813 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (37291117435 / 1000000000000) (37291127529 / 1000000000000), orderedInterval (-11898262627 / 1000000000000) (-11898252533 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1409857757402577 / 4000000000000) 3 (IntervalRat.scale (813 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (41815059635 / 1000000000000) (41815059649 / 1000000000000), orderedInterval (7536393661 / 1000000000000) (7536393675 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (882223522787931 / 4000000000000) 3 (IntervalRat.scale (813 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (53187979195 / 1000000000000) (53187979204 / 1000000000000), orderedInterval (7459974086 / 1000000000000) (7459974095 / 1000000000000)))) (orderedInterval (-1814962305 / 1000000000000) (-1814960485 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (474462744698277 / 4000000000000) 3 (IntervalRat.scale (813 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (1429191710 / 1000000000000) (1429191714 / 1000000000000), orderedInterval (73240710523 / 1000000000000) (73240710527 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1288258648005831 / 4000000000000) 3 (IntervalRat.scale (813 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (29793471790 / 1000000000000) (29793488516 / 1000000000000), orderedInterval (-33046744628 / 1000000000000) (-33046727902 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1759007047232487 / 4000000000000) 3 (IntervalRat.scale (813 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (24913681265 / 1000000000000) (24913681266 / 1000000000000), orderedInterval (28729080567 / 1000000000000) (28729080568 / 1000000000000)))) (orderedInterval (2441645036 / 1000000000000) (2441645271 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (743776477212069 / 4000000000000) 3 (IntervalRat.scale (813 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-57393043917 / 1000000000000) (-57393043914 / 1000000000000), orderedInterval (-11236134144 / 1000000000000) (-11236134141 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3023410086631749 / 4000000000000) 3 (IntervalRat.scale (813 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (13557710763 / 1000000000000) (13557710832 / 1000000000000), orderedInterval (-25669103598 / 1000000000000) (-25669103529 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2019497820760491 / 4000000000000) 3 (IntervalRat.scale (813 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (4843006805 / 1000000000000) (4843006808 / 1000000000000), orderedInterval (-35182808823 / 1000000000000) (-35182808820 / 1000000000000)))) (orderedInterval (-26086587074 / 1000000000000) (-26086586676 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate535_chunkChecks3 :
    compactCertificate535.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate535.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate535_chunkChecks3_0
    compactCertificate535_chunkChecks3_1 compactCertificate535_chunkChecks3_2

theorem compactCertificate535_chunkChecks4_0 :
    compactCertificate535.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (813 / 2) 4 (IntervalRat.scale (813 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-35654193364 / 1000000000000) (-35654156596 / 1000000000000), orderedInterval (17215886977 / 1000000000000) (17215923745 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1197704240643513 / 4000000000000) 4 (IntervalRat.scale (813 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-45289383351 / 1000000000000) (-45289381847 / 1000000000000), orderedInterval (8736027260 / 1000000000000) (8736028764 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (387312943037529 / 800000000000) 4 (IntervalRat.scale (813 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (32656178723 / 1000000000000) (32656178724 / 1000000000000), orderedInterval (15730794574 / 1000000000000) (15730794576 / 1000000000000)))) (orderedInterval (-10358932346 / 1000000000000) (-10358917646 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (349487110302891 / 4000000000000) 4 (IntervalRat.scale (813 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (16217324662 / 1000000000000) (16217324663 / 1000000000000), orderedInterval (83713168839 / 1000000000000) (83713168840 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (938771537702127 / 4000000000000) 4 (IntervalRat.scale (813 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (7355330477 / 1000000000000) (7355330497 / 1000000000000), orderedInterval (-51576026095 / 1000000000000) (-51576026074 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2548947341932659 / 4000000000000) 4 (IntervalRat.scale (813 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-8696277920 / 1000000000000) (-8696277919 / 1000000000000), orderedInterval (-30380783746 / 1000000000000) (-30380783745 / 1000000000000)))) (orderedInterval (3801912245 / 1000000000000) (3801912422 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1877543075405067 / 4000000000000) 4 (IntervalRat.scale (813 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-32269867573 / 1000000000000) (-32269789571 / 1000000000000), orderedInterval (17780892716 / 1000000000000) (17780970719 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3217202061403191 / 4000000000000) 4 (IntervalRat.scale (813 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (20912890035 / 1000000000000) (20912890036 / 1000000000000), orderedInterval (18806425496 / 1000000000000) (18806425497 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2369776477212069 / 4000000000000) 4 (IntervalRat.scale (813 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (16619863114 / 1000000000000) (16619863509 / 1000000000000), orderedInterval (-28269033805 / 1000000000000) (-28269033410 / 1000000000000)))) (orderedInterval (-8106134794 / 1000000000000) (-8106134512 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate535_chunkChecks4_1 :
    compactCertificate535.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3635846531414187 / 4000000000000) 4 (IntervalRat.scale (813 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-25603481618 / 1000000000000) (-25603418218 / 1000000000000), orderedInterval (6710660515 / 1000000000000) (6710723914 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2099156973643923 / 4000000000000) 4 (IntervalRat.scale (813 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-27887318017 / 1000000000000) (-27887318016 / 1000000000000), orderedInterval (-20839512902 / 1000000000000) (-20839512901 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3724990886417007 / 4000000000000) 4 (IntervalRat.scale (813 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (22279766149 / 1000000000000) (22279779531 / 1000000000000), orderedInterval (-13695239419 / 1000000000000) (-13695226037 / 1000000000000)))) (orderedInterval (195033886782 / 1000000000000) (195034225028 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3480369679199883 / 4000000000000) 4 (IntervalRat.scale (813 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-16509737500 / 1000000000000) (-16509737499 / 1000000000000), orderedInterval (-21417078838 / 1000000000000) (-21417078837 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2483756026665339 / 4000000000000) 4 (IntervalRat.scale (813 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-9802660517 / 1000000000000) (-9802660503 / 1000000000000), orderedInterval (30490042734 / 1000000000000) (30490042748 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2816314613106381 / 4000000000000) 4 (IntervalRat.scale (813 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (27411062946 / 1000000000000) (27411062951 / 1000000000000), orderedInterval (12342649915 / 1000000000000) (12342649921 / 1000000000000)))) (orderedInterval (28579227 / 1000000000000) (28579618 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2347949508849789 / 4000000000000) 4 (IntervalRat.scale (813 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-9566497422 / 1000000000000) (-9566497421 / 1000000000000), orderedInterval (-31504339271 / 1000000000000) (-31504339270 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2074484597233569 / 4000000000000) 4 (IntervalRat.scale (813 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-30277436195 / 1000000000000) (-30277436194 / 1000000000000), orderedInterval (-17600339336 / 1000000000000) (-17600339335 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (601266493199331 / 800000000000) 4 (IntervalRat.scale (813 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-29076904007 / 1000000000000) (-29076902553 / 1000000000000), orderedInterval (-1234420774 / 1000000000000) (-1234419320 / 1000000000000)))) (orderedInterval (-4585752927 / 1000000000000) (-4585752286 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate535_chunkChecks4_2 :
    compactCertificate535.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1663134763111257 / 4000000000000) 4 (IntervalRat.scale (813 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (37291117435 / 1000000000000) (37291127529 / 1000000000000), orderedInterval (-11898262627 / 1000000000000) (-11898252533 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1409857757402577 / 4000000000000) 4 (IntervalRat.scale (813 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (41815059635 / 1000000000000) (41815059649 / 1000000000000), orderedInterval (7536393661 / 1000000000000) (7536393675 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (882223522787931 / 4000000000000) 4 (IntervalRat.scale (813 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (53187979195 / 1000000000000) (53187979204 / 1000000000000), orderedInterval (7459974086 / 1000000000000) (7459974095 / 1000000000000)))) (orderedInterval (-7704902364 / 1000000000000) (-7704900503 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (474462744698277 / 4000000000000) 4 (IntervalRat.scale (813 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (1429191710 / 1000000000000) (1429191714 / 1000000000000), orderedInterval (73240710523 / 1000000000000) (73240710527 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1288258648005831 / 4000000000000) 4 (IntervalRat.scale (813 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (29793471790 / 1000000000000) (29793488516 / 1000000000000), orderedInterval (-33046744628 / 1000000000000) (-33046727902 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1759007047232487 / 4000000000000) 4 (IntervalRat.scale (813 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (24913681265 / 1000000000000) (24913681266 / 1000000000000), orderedInterval (28729080567 / 1000000000000) (28729080568 / 1000000000000)))) (orderedInterval (-2893542559 / 1000000000000) (-2893542362 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (743776477212069 / 4000000000000) 4 (IntervalRat.scale (813 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-57393043917 / 1000000000000) (-57393043914 / 1000000000000), orderedInterval (-11236134144 / 1000000000000) (-11236134141 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3023410086631749 / 4000000000000) 4 (IntervalRat.scale (813 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (13557710763 / 1000000000000) (13557710832 / 1000000000000), orderedInterval (-25669103598 / 1000000000000) (-25669103529 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2019497820760491 / 4000000000000) 4 (IntervalRat.scale (813 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (4843006805 / 1000000000000) (4843006808 / 1000000000000), orderedInterval (-35182808823 / 1000000000000) (-35182808820 / 1000000000000)))) (orderedInterval (-15241469226 / 1000000000000) (-15241468579 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate535_chunkChecks4 :
    compactCertificate535.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate535.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate535_chunkChecks4_0
    compactCertificate535_chunkChecks4_1 compactCertificate535_chunkChecks4_2

theorem compactCertificate535_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate535.chunkCheck r b = true :=
  compactCertificate535.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate535_chunkChecks0
    · exact compactCertificate535_chunkChecks1
    · exact compactCertificate535_chunkChecks2
    · exact compactCertificate535_chunkChecks3
    · exact compactCertificate535_chunkChecks4)

theorem compactCertificate535_coefficient0 :
    compactCertificate535.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate535_coefficient1 :
    compactCertificate535.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate535_coefficient2 :
    compactCertificate535.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate535_coefficient3 :
    compactCertificate535.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate535_coefficient4 :
    compactCertificate535.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate535_coefficients : ∀ r : Fin 5,
    compactCertificate535.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate535_coefficient0
  · exact compactCertificate535_coefficient1
  · exact compactCertificate535_coefficient2
  · exact compactCertificate535_coefficient3
  · exact compactCertificate535_coefficient4

theorem compactCertificate535_lower : (1 : ℚ) ≤ compactCertificate535.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate535, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate535_proves {t : ℝ} (ht : t ∈ compactCertificate535.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate535.proves compactCertificate535_states compactCertificate535_chunks
    compactCertificate535_coefficients compactCertificate535_lower ht

end Erdos232
