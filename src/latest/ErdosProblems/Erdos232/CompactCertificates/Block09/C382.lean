/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate382 : CompactCertificate where
  left := 253
  right := 254
  center := 507 / 2
  grid := fun i =>
    match i.val with
    | 0 => 81
    | 1 => 59
    | 2 => 96
    | 3 => 17
    | 4 => 47
    | 5 => 127
    | 6 => 93
    | 7 => 160
    | 8 => 118
    | 9 => 181
    | 10 => 104
    | 11 => 185
    | 12 => 173
    | 13 => 123
    | 14 => 140
    | 15 => 117
    | 16 => 103
    | 17 => 149
    | 18 => 83
    | 19 => 70
    | 20 => 44
    | 21 => 24
    | 22 => 64
    | 23 => 87
    | 24 => 37
    | 25 => 150
    | _ => 100
  point := fun i =>
    match i.val with
    | 0 => 507 / 2
    | 1 => 746907810585807 / 4000000000000
    | 2 => 241534639754031 / 800000000000
    | 3 => 217945836314349 / 4000000000000
    | 4 => 585433172958153 / 4000000000000
    | 5 => 1589564947552101 / 4000000000000
    | 6 => 1170866345916813 / 4000000000000
    | 7 => 2006299440506049 / 4000000000000
    | 8 => 1477831087265091 / 4000000000000
    | 9 => 2267372929184493 / 4000000000000
    | 10 => 1309068371017797 / 4000000000000
    | 11 => 2322964796326473 / 4000000000000
    | 12 => 2170415039796237 / 4000000000000
    | 13 => 1548910584894621 / 4000000000000
    | 14 => 1756299518874459 / 4000000000000
    | 15 => 1464219435408171 / 4000000000000
    | 16 => 1293682276503591 / 4000000000000
    | 17 => 374959547419509 / 800000000000
    | 18 => 1037157841202223 / 4000000000000
    | 19 => 879210188195703 / 4000000000000
    | 20 => 550168912734909 / 4000000000000
    | 21 => 295882671048003 / 4000000000000
    | 22 => 803379009273009 / 4000000000000
    | 23 => 1096945354178193 / 4000000000000
    | 24 => 463831087265091 / 4000000000000
    | 25 => 1885447618600611 / 4000000000000
    | _ => 1259391629920749 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (9173775773 / 1000000000000) (9173775808 / 1000000000000), orderedInterval (-49284380787 / 1000000000000) (-49284380753 / 1000000000000))
    | 1 => (orderedInterval (-48618221499 / 1000000000000) (-48618174707 / 1000000000000), orderedInterval (32466331249 / 1000000000000) (32466378041 / 1000000000000))
    | 2 => (orderedInterval (41137778034 / 1000000000000) (41137778035 / 1000000000000), orderedInterval (20334431430 / 1000000000000) (20334431431 / 1000000000000))
    | 3 => (orderedInterval (-103524399267 / 1000000000000) (-103524398069 / 1000000000000), orderedInterval (32035097716 / 1000000000000) (32035098913 / 1000000000000))
    | 4 => (orderedInterval (32312476254 / 1000000000000) (32312480594 / 1000000000000), orderedInterval (-57605187111 / 1000000000000) (-57605182772 / 1000000000000))
    | 5 => (orderedInterval (28877439912 / 1000000000000) (28877462870 / 1000000000000), orderedInterval (-27750785927 / 1000000000000) (-27750762969 / 1000000000000))
    | 6 => (orderedInterval (-45327930682 / 1000000000000) (-45327930678 / 1000000000000), orderedInterval (-10888125244 / 1000000000000) (-10888125240 / 1000000000000))
    | 7 => (orderedInterval (-10351728054 / 1000000000000) (-10351728026 / 1000000000000), orderedInterval (34099672948 / 1000000000000) (34099672976 / 1000000000000))
    | 8 => (orderedInterval (-18617998356 / 1000000000000) (-18617997651 / 1000000000000), orderedInterval (37126277789 / 1000000000000) (37126278494 / 1000000000000))
    | 9 => (orderedInterval (28197344565 / 1000000000000) (28197405346 / 1000000000000), orderedInterval (-18135797514 / 1000000000000) (-18135736734 / 1000000000000))
    | 10 => (orderedInterval (42795215937 / 1000000000000) (42795215942 / 1000000000000), orderedInterval (10603640881 / 1000000000000) (10603640886 / 1000000000000))
    | 11 => (orderedInterval (-10783324152 / 1000000000000) (-10783324151 / 1000000000000), orderedInterval (-31294703611 / 1000000000000) (-31294703610 / 1000000000000))
    | 12 => (orderedInterval (3644503185 / 1000000000000) (3644503186 / 1000000000000), orderedInterval (-34061930673 / 1000000000000) (-34061930671 / 1000000000000))
    | 13 => (orderedInterval (-40533076645 / 1000000000000) (-40533076289 / 1000000000000), orderedInterval (1107606332 / 1000000000000) (1107606687 / 1000000000000))
    | 14 => (orderedInterval (1409378562 / 1000000000000) (1409378563 / 1000000000000), orderedInterval (38050020711 / 1000000000000) (38050020712 / 1000000000000))
    | 15 => (orderedInterval (27699147982 / 1000000000000) (27699160461 / 1000000000000), orderedInterval (-31213065585 / 1000000000000) (-31213053106 / 1000000000000))
    | 16 => (orderedInterval (-25834031085 / 1000000000000) (-25834031084 / 1000000000000), orderedInterval (-36029434082 / 1000000000000) (-36029434081 / 1000000000000))
    | 17 => (orderedInterval (-36235693818 / 1000000000000) (-36235693784 / 1000000000000), orderedInterval (-6687597206 / 1000000000000) (-6687597172 / 1000000000000))
    | 18 => (orderedInterval (31072639394 / 1000000000000) (31072652551 / 1000000000000), orderedInterval (-38657062560 / 1000000000000) (-38657049404 / 1000000000000))
    | 19 => (orderedInterval (33667795055 / 1000000000000) (33667795056 / 1000000000000), orderedInterval (41909208367 / 1000000000000) (41909208368 / 1000000000000))
    | 20 => (orderedInterval (6564549145 / 1000000000000) (6564549146 / 1000000000000), orderedInterval (67692288223 / 1000000000000) (67692288225 / 1000000000000))
    | 21 => (orderedInterval (-55687426975 / 1000000000000) (-55687403895 / 1000000000000), orderedInterval (74574417672 / 1000000000000) (74574440753 / 1000000000000))
    | 22 => (orderedInterval (30267410276 / 1000000000000) (30267410277 / 1000000000000), orderedInterval (47396734407 / 1000000000000) (47396734408 / 1000000000000))
    | 23 => (orderedInterval (-47762493095 / 1000000000000) (-47762492439 / 1000000000000), orderedInterval (6424908136 / 1000000000000) (6424908792 / 1000000000000))
    | 24 => (orderedInterval (-35728520496 / 1000000000000) (-35728520495 / 1000000000000), orderedInterval (-64758194568 / 1000000000000) (-64758194567 / 1000000000000))
    | 25 => (orderedInterval (28972607632 / 1000000000000) (28972607633 / 1000000000000), orderedInterval (22578654460 / 1000000000000) (22578654461 / 1000000000000))
    | _ => (orderedInterval (44754484406 / 1000000000000) (44754484444 / 1000000000000), orderedInterval (4290699268 / 1000000000000) (4290699307 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (5597147768 / 1000000000000) (5597148236 / 1000000000000)
      | 1 => orderedInterval (250062762 / 1000000000000) (250064596 / 1000000000000)
      | 2 => orderedInterval (-130671585 / 1000000000000) (-130671552 / 1000000000000)
      | 3 => orderedInterval (-3372478249 / 1000000000000) (-3372467348 / 1000000000000)
      | 4 => orderedInterval (-3905850708 / 1000000000000) (-3905850643 / 1000000000000)
      | 5 => orderedInterval (870479467 / 1000000000000) (870479637 / 1000000000000)
      | 6 => orderedInterval (-6660167370 / 1000000000000) (-6660165202 / 1000000000000)
      | 7 => orderedInterval (4002065302 / 1000000000000) (4002065809 / 1000000000000)
      | _ => orderedInterval (-10970933505 / 1000000000000) (-10970933427 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-17890609050 / 1000000000000) (-17890608695 / 1000000000000)
      | 1 => orderedInterval (1803560288 / 1000000000000) (1803562976 / 1000000000000)
      | 2 => orderedInterval (-773327832 / 1000000000000) (-773327780 / 1000000000000)
      | 3 => orderedInterval (-1971560981 / 1000000000000) (-1971536623 / 1000000000000)
      | 4 => orderedInterval (1142686581 / 1000000000000) (1142686682 / 1000000000000)
      | 5 => orderedInterval (1793483123 / 1000000000000) (1793483368 / 1000000000000)
      | 6 => orderedInterval (5461077346 / 1000000000000) (5461079557 / 1000000000000)
      | 7 => orderedInterval (-1786421531 / 1000000000000) (-1786421324 / 1000000000000)
      | _ => orderedInterval (-4595945356 / 1000000000000) (-4595945248 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-6744014199 / 1000000000000) (-6744013924 / 1000000000000)
      | 1 => orderedInterval (4592555588 / 1000000000000) (4592559711 / 1000000000000)
      | 2 => orderedInterval (-291160366 / 1000000000000) (-291160281 / 1000000000000)
      | 3 => orderedInterval (27819808435 / 1000000000000) (27819862978 / 1000000000000)
      | 4 => orderedInterval (9261817143 / 1000000000000) (9261817303 / 1000000000000)
      | 5 => orderedInterval (91142317 / 1000000000000) (91142674 / 1000000000000)
      | 6 => orderedInterval (6545998329 / 1000000000000) (6546000595 / 1000000000000)
      | 7 => orderedInterval (-3933278637 / 1000000000000) (-3933278513 / 1000000000000)
      | _ => orderedInterval (21170450619 / 1000000000000) (21170450776 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (17424141321 / 1000000000000) (17424141537 / 1000000000000)
      | 1 => orderedInterval (-7209670979 / 1000000000000) (-7209664573 / 1000000000000)
      | 2 => orderedInterval (5370386684 / 1000000000000) (5370386824 / 1000000000000)
      | 3 => orderedInterval (15658193215 / 1000000000000) (15658315155 / 1000000000000)
      | 4 => orderedInterval (-5439532928 / 1000000000000) (-5439532670 / 1000000000000)
      | 5 => orderedInterval (-2114607133 / 1000000000000) (-2114606611 / 1000000000000)
      | 6 => orderedInterval (-5445647636 / 1000000000000) (-5445645321 / 1000000000000)
      | 7 => orderedInterval (1207861020 / 1000000000000) (1207861123 / 1000000000000)
      | _ => orderedInterval (13311913612 / 1000000000000) (13311913852 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (8222418424 / 1000000000000) (8222418599 / 1000000000000)
      | 1 => orderedInterval (-12206850091 / 1000000000000) (-12206840057 / 1000000000000)
      | 2 => orderedInterval (2820951673 / 1000000000000) (2820951912 / 1000000000000)
      | 3 => orderedInterval (-158795612079 / 1000000000000) (-158795338950 / 1000000000000)
      | 4 => orderedInterval (-22270321354 / 1000000000000) (-22270320931 / 1000000000000)
      | 5 => orderedInterval (-5517652841 / 1000000000000) (-5517652073 / 1000000000000)
      | 6 => orderedInterval (-6453431780 / 1000000000000) (-6453429406 / 1000000000000)
      | 7 => orderedInterval (4740600261 / 1000000000000) (4740600364 / 1000000000000)
      | _ => orderedInterval (-48287460833 / 1000000000000) (-48287460453 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-14320346118 / 1000000000000) (-14320329894 / 1000000000000)
    | 1 => orderedInterval (-16817057412 / 1000000000000) (-16817027087 / 1000000000000)
    | 2 => orderedInterval (58513319229 / 1000000000000) (58513381319 / 1000000000000)
    | 3 => orderedInterval (32763037176 / 1000000000000) (32763169316 / 1000000000000)
    | _ => orderedInterval (-237747358620 / 1000000000000) (-237747070995 / 1000000000000)

theorem compactCertificate382_stateChecks0 :
    compactCertificate382.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 81 12 (507 / 2)) (orderedInterval (9173775773 / 1000000000000) (9173775808 / 1000000000000), orderedInterval (-49284380787 / 1000000000000) (-49284380753 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 59 12 (746907810585807 / 4000000000000)) (orderedInterval (-48618221499 / 1000000000000) (-48618174707 / 1000000000000), orderedInterval (32466331249 / 1000000000000) (32466378041 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 96 12 (241534639754031 / 800000000000)) (orderedInterval (41137778034 / 1000000000000) (41137778035 / 1000000000000), orderedInterval (20334431430 / 1000000000000) (20334431431 / 1000000000000))) = true
  rfl'

theorem compactCertificate382_stateChecks1 :
    compactCertificate382.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 17 12 (217945836314349 / 4000000000000)) (orderedInterval (-103524399267 / 1000000000000) (-103524398069 / 1000000000000), orderedInterval (32035097716 / 1000000000000) (32035098913 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 47 12 (585433172958153 / 4000000000000)) (orderedInterval (32312476254 / 1000000000000) (32312480594 / 1000000000000), orderedInterval (-57605187111 / 1000000000000) (-57605182772 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 127 12 (1589564947552101 / 4000000000000)) (orderedInterval (28877439912 / 1000000000000) (28877462870 / 1000000000000), orderedInterval (-27750785927 / 1000000000000) (-27750762969 / 1000000000000))) = true
  rfl'

theorem compactCertificate382_stateChecks2 :
    compactCertificate382.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 93 12 (1170866345916813 / 4000000000000)) (orderedInterval (-45327930682 / 1000000000000) (-45327930678 / 1000000000000), orderedInterval (-10888125244 / 1000000000000) (-10888125240 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 160 12 (2006299440506049 / 4000000000000)) (orderedInterval (-10351728054 / 1000000000000) (-10351728026 / 1000000000000), orderedInterval (34099672948 / 1000000000000) (34099672976 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 118 12 (1477831087265091 / 4000000000000)) (orderedInterval (-18617998356 / 1000000000000) (-18617997651 / 1000000000000), orderedInterval (37126277789 / 1000000000000) (37126278494 / 1000000000000))) = true
  rfl'

theorem compactCertificate382_stateChecks3 :
    compactCertificate382.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 181 12 (2267372929184493 / 4000000000000)) (orderedInterval (28197344565 / 1000000000000) (28197405346 / 1000000000000), orderedInterval (-18135797514 / 1000000000000) (-18135736734 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 104 12 (1309068371017797 / 4000000000000)) (orderedInterval (42795215937 / 1000000000000) (42795215942 / 1000000000000), orderedInterval (10603640881 / 1000000000000) (10603640886 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 185 12 (2322964796326473 / 4000000000000)) (orderedInterval (-10783324152 / 1000000000000) (-10783324151 / 1000000000000), orderedInterval (-31294703611 / 1000000000000) (-31294703610 / 1000000000000))) = true
  rfl'

theorem compactCertificate382_stateChecks4 :
    compactCertificate382.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 173 12 (2170415039796237 / 4000000000000)) (orderedInterval (3644503185 / 1000000000000) (3644503186 / 1000000000000), orderedInterval (-34061930673 / 1000000000000) (-34061930671 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 123 12 (1548910584894621 / 4000000000000)) (orderedInterval (-40533076645 / 1000000000000) (-40533076289 / 1000000000000), orderedInterval (1107606332 / 1000000000000) (1107606687 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 140 12 (1756299518874459 / 4000000000000)) (orderedInterval (1409378562 / 1000000000000) (1409378563 / 1000000000000), orderedInterval (38050020711 / 1000000000000) (38050020712 / 1000000000000))) = true
  rfl'

theorem compactCertificate382_stateChecks5 :
    compactCertificate382.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 117 12 (1464219435408171 / 4000000000000)) (orderedInterval (27699147982 / 1000000000000) (27699160461 / 1000000000000), orderedInterval (-31213065585 / 1000000000000) (-31213053106 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 103 12 (1293682276503591 / 4000000000000)) (orderedInterval (-25834031085 / 1000000000000) (-25834031084 / 1000000000000), orderedInterval (-36029434082 / 1000000000000) (-36029434081 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 149 12 (374959547419509 / 800000000000)) (orderedInterval (-36235693818 / 1000000000000) (-36235693784 / 1000000000000), orderedInterval (-6687597206 / 1000000000000) (-6687597172 / 1000000000000))) = true
  rfl'

theorem compactCertificate382_stateChecks6 :
    compactCertificate382.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 83 12 (1037157841202223 / 4000000000000)) (orderedInterval (31072639394 / 1000000000000) (31072652551 / 1000000000000), orderedInterval (-38657062560 / 1000000000000) (-38657049404 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (879210188195703 / 4000000000000)) (orderedInterval (33667795055 / 1000000000000) (33667795056 / 1000000000000), orderedInterval (41909208367 / 1000000000000) (41909208368 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 44 12 (550168912734909 / 4000000000000)) (orderedInterval (6564549145 / 1000000000000) (6564549146 / 1000000000000), orderedInterval (67692288223 / 1000000000000) (67692288225 / 1000000000000))) = true
  rfl'

theorem compactCertificate382_stateChecks7 :
    compactCertificate382.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 24 12 (295882671048003 / 4000000000000)) (orderedInterval (-55687426975 / 1000000000000) (-55687403895 / 1000000000000), orderedInterval (74574417672 / 1000000000000) (74574440753 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (803379009273009 / 4000000000000)) (orderedInterval (30267410276 / 1000000000000) (30267410277 / 1000000000000), orderedInterval (47396734407 / 1000000000000) (47396734408 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 87 12 (1096945354178193 / 4000000000000)) (orderedInterval (-47762493095 / 1000000000000) (-47762492439 / 1000000000000), orderedInterval (6424908136 / 1000000000000) (6424908792 / 1000000000000))) = true
  rfl'

theorem compactCertificate382_stateChecks8 :
    compactCertificate382.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (463831087265091 / 4000000000000)) (orderedInterval (-35728520496 / 1000000000000) (-35728520495 / 1000000000000), orderedInterval (-64758194568 / 1000000000000) (-64758194567 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 150 12 (1885447618600611 / 4000000000000)) (orderedInterval (28972607632 / 1000000000000) (28972607633 / 1000000000000), orderedInterval (22578654460 / 1000000000000) (22578654461 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 100 12 (1259391629920749 / 4000000000000)) (orderedInterval (44754484406 / 1000000000000) (44754484444 / 1000000000000), orderedInterval (4290699268 / 1000000000000) (4290699307 / 1000000000000))) = true
  rfl'

theorem compactCertificate382_states : ∀ j,
    BesselStateValid (compactCertificate382.point j) (compactCertificate382.state j) :=
  compactCertificate382.statesValid_of_checks3 compactCertificate382_stateChecks0
    compactCertificate382_stateChecks1 compactCertificate382_stateChecks2
    compactCertificate382_stateChecks3 compactCertificate382_stateChecks4
    compactCertificate382_stateChecks5 compactCertificate382_stateChecks6
    compactCertificate382_stateChecks7 compactCertificate382_stateChecks8

theorem compactCertificate382_chunkChecks0_0 :
    compactCertificate382.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (507 / 2) 0 (IntervalRat.scale (507 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (9173775773 / 1000000000000) (9173775808 / 1000000000000), orderedInterval (-49284380787 / 1000000000000) (-49284380753 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (746907810585807 / 4000000000000) 0 (IntervalRat.scale (507 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-48618221499 / 1000000000000) (-48618174707 / 1000000000000), orderedInterval (32466331249 / 1000000000000) (32466378041 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (241534639754031 / 800000000000) 0 (IntervalRat.scale (507 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (41137778034 / 1000000000000) (41137778035 / 1000000000000), orderedInterval (20334431430 / 1000000000000) (20334431431 / 1000000000000)))) (orderedInterval (5597147768 / 1000000000000) (5597148236 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (217945836314349 / 4000000000000) 0 (IntervalRat.scale (507 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-103524399267 / 1000000000000) (-103524398069 / 1000000000000), orderedInterval (32035097716 / 1000000000000) (32035098913 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (585433172958153 / 4000000000000) 0 (IntervalRat.scale (507 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (32312476254 / 1000000000000) (32312480594 / 1000000000000), orderedInterval (-57605187111 / 1000000000000) (-57605182772 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1589564947552101 / 4000000000000) 0 (IntervalRat.scale (507 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (28877439912 / 1000000000000) (28877462870 / 1000000000000), orderedInterval (-27750785927 / 1000000000000) (-27750762969 / 1000000000000)))) (orderedInterval (250062762 / 1000000000000) (250064596 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1170866345916813 / 4000000000000) 0 (IntervalRat.scale (507 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-45327930682 / 1000000000000) (-45327930678 / 1000000000000), orderedInterval (-10888125244 / 1000000000000) (-10888125240 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2006299440506049 / 4000000000000) 0 (IntervalRat.scale (507 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-10351728054 / 1000000000000) (-10351728026 / 1000000000000), orderedInterval (34099672948 / 1000000000000) (34099672976 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1477831087265091 / 4000000000000) 0 (IntervalRat.scale (507 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-18617998356 / 1000000000000) (-18617997651 / 1000000000000), orderedInterval (37126277789 / 1000000000000) (37126278494 / 1000000000000)))) (orderedInterval (-130671585 / 1000000000000) (-130671552 / 1000000000000))) = true
  rfl'

theorem compactCertificate382_chunkChecks0_1 :
    compactCertificate382.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2267372929184493 / 4000000000000) 0 (IntervalRat.scale (507 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (28197344565 / 1000000000000) (28197405346 / 1000000000000), orderedInterval (-18135797514 / 1000000000000) (-18135736734 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1309068371017797 / 4000000000000) 0 (IntervalRat.scale (507 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (42795215937 / 1000000000000) (42795215942 / 1000000000000), orderedInterval (10603640881 / 1000000000000) (10603640886 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2322964796326473 / 4000000000000) 0 (IntervalRat.scale (507 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-10783324152 / 1000000000000) (-10783324151 / 1000000000000), orderedInterval (-31294703611 / 1000000000000) (-31294703610 / 1000000000000)))) (orderedInterval (-3372478249 / 1000000000000) (-3372467348 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2170415039796237 / 4000000000000) 0 (IntervalRat.scale (507 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (3644503185 / 1000000000000) (3644503186 / 1000000000000), orderedInterval (-34061930673 / 1000000000000) (-34061930671 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1548910584894621 / 4000000000000) 0 (IntervalRat.scale (507 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-40533076645 / 1000000000000) (-40533076289 / 1000000000000), orderedInterval (1107606332 / 1000000000000) (1107606687 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1756299518874459 / 4000000000000) 0 (IntervalRat.scale (507 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (1409378562 / 1000000000000) (1409378563 / 1000000000000), orderedInterval (38050020711 / 1000000000000) (38050020712 / 1000000000000)))) (orderedInterval (-3905850708 / 1000000000000) (-3905850643 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1464219435408171 / 4000000000000) 0 (IntervalRat.scale (507 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (27699147982 / 1000000000000) (27699160461 / 1000000000000), orderedInterval (-31213065585 / 1000000000000) (-31213053106 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1293682276503591 / 4000000000000) 0 (IntervalRat.scale (507 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-25834031085 / 1000000000000) (-25834031084 / 1000000000000), orderedInterval (-36029434082 / 1000000000000) (-36029434081 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (374959547419509 / 800000000000) 0 (IntervalRat.scale (507 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-36235693818 / 1000000000000) (-36235693784 / 1000000000000), orderedInterval (-6687597206 / 1000000000000) (-6687597172 / 1000000000000)))) (orderedInterval (870479467 / 1000000000000) (870479637 / 1000000000000))) = true
  rfl'

theorem compactCertificate382_chunkChecks0_2 :
    compactCertificate382.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1037157841202223 / 4000000000000) 0 (IntervalRat.scale (507 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (31072639394 / 1000000000000) (31072652551 / 1000000000000), orderedInterval (-38657062560 / 1000000000000) (-38657049404 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (879210188195703 / 4000000000000) 0 (IntervalRat.scale (507 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (33667795055 / 1000000000000) (33667795056 / 1000000000000), orderedInterval (41909208367 / 1000000000000) (41909208368 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (550168912734909 / 4000000000000) 0 (IntervalRat.scale (507 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (6564549145 / 1000000000000) (6564549146 / 1000000000000), orderedInterval (67692288223 / 1000000000000) (67692288225 / 1000000000000)))) (orderedInterval (-6660167370 / 1000000000000) (-6660165202 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (295882671048003 / 4000000000000) 0 (IntervalRat.scale (507 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-55687426975 / 1000000000000) (-55687403895 / 1000000000000), orderedInterval (74574417672 / 1000000000000) (74574440753 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (803379009273009 / 4000000000000) 0 (IntervalRat.scale (507 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (30267410276 / 1000000000000) (30267410277 / 1000000000000), orderedInterval (47396734407 / 1000000000000) (47396734408 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1096945354178193 / 4000000000000) 0 (IntervalRat.scale (507 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-47762493095 / 1000000000000) (-47762492439 / 1000000000000), orderedInterval (6424908136 / 1000000000000) (6424908792 / 1000000000000)))) (orderedInterval (4002065302 / 1000000000000) (4002065809 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (463831087265091 / 4000000000000) 0 (IntervalRat.scale (507 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-35728520496 / 1000000000000) (-35728520495 / 1000000000000), orderedInterval (-64758194568 / 1000000000000) (-64758194567 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1885447618600611 / 4000000000000) 0 (IntervalRat.scale (507 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (28972607632 / 1000000000000) (28972607633 / 1000000000000), orderedInterval (22578654460 / 1000000000000) (22578654461 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1259391629920749 / 4000000000000) 0 (IntervalRat.scale (507 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (44754484406 / 1000000000000) (44754484444 / 1000000000000), orderedInterval (4290699268 / 1000000000000) (4290699307 / 1000000000000)))) (orderedInterval (-10970933505 / 1000000000000) (-10970933427 / 1000000000000))) = true
  rfl'

theorem compactCertificate382_chunkChecks0 :
    compactCertificate382.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate382.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate382_chunkChecks0_0
    compactCertificate382_chunkChecks0_1 compactCertificate382_chunkChecks0_2

theorem compactCertificate382_chunkChecks1_0 :
    compactCertificate382.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (507 / 2) 1 (IntervalRat.scale (507 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (9173775773 / 1000000000000) (9173775808 / 1000000000000), orderedInterval (-49284380787 / 1000000000000) (-49284380753 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (746907810585807 / 4000000000000) 1 (IntervalRat.scale (507 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-48618221499 / 1000000000000) (-48618174707 / 1000000000000), orderedInterval (32466331249 / 1000000000000) (32466378041 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (241534639754031 / 800000000000) 1 (IntervalRat.scale (507 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (41137778034 / 1000000000000) (41137778035 / 1000000000000), orderedInterval (20334431430 / 1000000000000) (20334431431 / 1000000000000)))) (orderedInterval (-17890609050 / 1000000000000) (-17890608695 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (217945836314349 / 4000000000000) 1 (IntervalRat.scale (507 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-103524399267 / 1000000000000) (-103524398069 / 1000000000000), orderedInterval (32035097716 / 1000000000000) (32035098913 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (585433172958153 / 4000000000000) 1 (IntervalRat.scale (507 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (32312476254 / 1000000000000) (32312480594 / 1000000000000), orderedInterval (-57605187111 / 1000000000000) (-57605182772 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1589564947552101 / 4000000000000) 1 (IntervalRat.scale (507 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (28877439912 / 1000000000000) (28877462870 / 1000000000000), orderedInterval (-27750785927 / 1000000000000) (-27750762969 / 1000000000000)))) (orderedInterval (1803560288 / 1000000000000) (1803562976 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1170866345916813 / 4000000000000) 1 (IntervalRat.scale (507 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-45327930682 / 1000000000000) (-45327930678 / 1000000000000), orderedInterval (-10888125244 / 1000000000000) (-10888125240 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2006299440506049 / 4000000000000) 1 (IntervalRat.scale (507 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-10351728054 / 1000000000000) (-10351728026 / 1000000000000), orderedInterval (34099672948 / 1000000000000) (34099672976 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1477831087265091 / 4000000000000) 1 (IntervalRat.scale (507 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-18617998356 / 1000000000000) (-18617997651 / 1000000000000), orderedInterval (37126277789 / 1000000000000) (37126278494 / 1000000000000)))) (orderedInterval (-773327832 / 1000000000000) (-773327780 / 1000000000000))) = true
  rfl'

theorem compactCertificate382_chunkChecks1_1 :
    compactCertificate382.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2267372929184493 / 4000000000000) 1 (IntervalRat.scale (507 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (28197344565 / 1000000000000) (28197405346 / 1000000000000), orderedInterval (-18135797514 / 1000000000000) (-18135736734 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1309068371017797 / 4000000000000) 1 (IntervalRat.scale (507 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (42795215937 / 1000000000000) (42795215942 / 1000000000000), orderedInterval (10603640881 / 1000000000000) (10603640886 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2322964796326473 / 4000000000000) 1 (IntervalRat.scale (507 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-10783324152 / 1000000000000) (-10783324151 / 1000000000000), orderedInterval (-31294703611 / 1000000000000) (-31294703610 / 1000000000000)))) (orderedInterval (-1971560981 / 1000000000000) (-1971536623 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2170415039796237 / 4000000000000) 1 (IntervalRat.scale (507 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (3644503185 / 1000000000000) (3644503186 / 1000000000000), orderedInterval (-34061930673 / 1000000000000) (-34061930671 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1548910584894621 / 4000000000000) 1 (IntervalRat.scale (507 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-40533076645 / 1000000000000) (-40533076289 / 1000000000000), orderedInterval (1107606332 / 1000000000000) (1107606687 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1756299518874459 / 4000000000000) 1 (IntervalRat.scale (507 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (1409378562 / 1000000000000) (1409378563 / 1000000000000), orderedInterval (38050020711 / 1000000000000) (38050020712 / 1000000000000)))) (orderedInterval (1142686581 / 1000000000000) (1142686682 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1464219435408171 / 4000000000000) 1 (IntervalRat.scale (507 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (27699147982 / 1000000000000) (27699160461 / 1000000000000), orderedInterval (-31213065585 / 1000000000000) (-31213053106 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1293682276503591 / 4000000000000) 1 (IntervalRat.scale (507 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-25834031085 / 1000000000000) (-25834031084 / 1000000000000), orderedInterval (-36029434082 / 1000000000000) (-36029434081 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (374959547419509 / 800000000000) 1 (IntervalRat.scale (507 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-36235693818 / 1000000000000) (-36235693784 / 1000000000000), orderedInterval (-6687597206 / 1000000000000) (-6687597172 / 1000000000000)))) (orderedInterval (1793483123 / 1000000000000) (1793483368 / 1000000000000))) = true
  rfl'

theorem compactCertificate382_chunkChecks1_2 :
    compactCertificate382.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1037157841202223 / 4000000000000) 1 (IntervalRat.scale (507 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (31072639394 / 1000000000000) (31072652551 / 1000000000000), orderedInterval (-38657062560 / 1000000000000) (-38657049404 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (879210188195703 / 4000000000000) 1 (IntervalRat.scale (507 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (33667795055 / 1000000000000) (33667795056 / 1000000000000), orderedInterval (41909208367 / 1000000000000) (41909208368 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (550168912734909 / 4000000000000) 1 (IntervalRat.scale (507 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (6564549145 / 1000000000000) (6564549146 / 1000000000000), orderedInterval (67692288223 / 1000000000000) (67692288225 / 1000000000000)))) (orderedInterval (5461077346 / 1000000000000) (5461079557 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (295882671048003 / 4000000000000) 1 (IntervalRat.scale (507 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-55687426975 / 1000000000000) (-55687403895 / 1000000000000), orderedInterval (74574417672 / 1000000000000) (74574440753 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (803379009273009 / 4000000000000) 1 (IntervalRat.scale (507 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (30267410276 / 1000000000000) (30267410277 / 1000000000000), orderedInterval (47396734407 / 1000000000000) (47396734408 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1096945354178193 / 4000000000000) 1 (IntervalRat.scale (507 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-47762493095 / 1000000000000) (-47762492439 / 1000000000000), orderedInterval (6424908136 / 1000000000000) (6424908792 / 1000000000000)))) (orderedInterval (-1786421531 / 1000000000000) (-1786421324 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (463831087265091 / 4000000000000) 1 (IntervalRat.scale (507 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-35728520496 / 1000000000000) (-35728520495 / 1000000000000), orderedInterval (-64758194568 / 1000000000000) (-64758194567 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1885447618600611 / 4000000000000) 1 (IntervalRat.scale (507 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (28972607632 / 1000000000000) (28972607633 / 1000000000000), orderedInterval (22578654460 / 1000000000000) (22578654461 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1259391629920749 / 4000000000000) 1 (IntervalRat.scale (507 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (44754484406 / 1000000000000) (44754484444 / 1000000000000), orderedInterval (4290699268 / 1000000000000) (4290699307 / 1000000000000)))) (orderedInterval (-4595945356 / 1000000000000) (-4595945248 / 1000000000000))) = true
  rfl'

theorem compactCertificate382_chunkChecks1 :
    compactCertificate382.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate382.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate382_chunkChecks1_0
    compactCertificate382_chunkChecks1_1 compactCertificate382_chunkChecks1_2

theorem compactCertificate382_chunkChecks2_0 :
    compactCertificate382.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (507 / 2) 2 (IntervalRat.scale (507 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (9173775773 / 1000000000000) (9173775808 / 1000000000000), orderedInterval (-49284380787 / 1000000000000) (-49284380753 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (746907810585807 / 4000000000000) 2 (IntervalRat.scale (507 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-48618221499 / 1000000000000) (-48618174707 / 1000000000000), orderedInterval (32466331249 / 1000000000000) (32466378041 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (241534639754031 / 800000000000) 2 (IntervalRat.scale (507 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (41137778034 / 1000000000000) (41137778035 / 1000000000000), orderedInterval (20334431430 / 1000000000000) (20334431431 / 1000000000000)))) (orderedInterval (-6744014199 / 1000000000000) (-6744013924 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (217945836314349 / 4000000000000) 2 (IntervalRat.scale (507 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-103524399267 / 1000000000000) (-103524398069 / 1000000000000), orderedInterval (32035097716 / 1000000000000) (32035098913 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (585433172958153 / 4000000000000) 2 (IntervalRat.scale (507 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (32312476254 / 1000000000000) (32312480594 / 1000000000000), orderedInterval (-57605187111 / 1000000000000) (-57605182772 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1589564947552101 / 4000000000000) 2 (IntervalRat.scale (507 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (28877439912 / 1000000000000) (28877462870 / 1000000000000), orderedInterval (-27750785927 / 1000000000000) (-27750762969 / 1000000000000)))) (orderedInterval (4592555588 / 1000000000000) (4592559711 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1170866345916813 / 4000000000000) 2 (IntervalRat.scale (507 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-45327930682 / 1000000000000) (-45327930678 / 1000000000000), orderedInterval (-10888125244 / 1000000000000) (-10888125240 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2006299440506049 / 4000000000000) 2 (IntervalRat.scale (507 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-10351728054 / 1000000000000) (-10351728026 / 1000000000000), orderedInterval (34099672948 / 1000000000000) (34099672976 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1477831087265091 / 4000000000000) 2 (IntervalRat.scale (507 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-18617998356 / 1000000000000) (-18617997651 / 1000000000000), orderedInterval (37126277789 / 1000000000000) (37126278494 / 1000000000000)))) (orderedInterval (-291160366 / 1000000000000) (-291160281 / 1000000000000))) = true
  rfl'

theorem compactCertificate382_chunkChecks2_1 :
    compactCertificate382.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2267372929184493 / 4000000000000) 2 (IntervalRat.scale (507 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (28197344565 / 1000000000000) (28197405346 / 1000000000000), orderedInterval (-18135797514 / 1000000000000) (-18135736734 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1309068371017797 / 4000000000000) 2 (IntervalRat.scale (507 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (42795215937 / 1000000000000) (42795215942 / 1000000000000), orderedInterval (10603640881 / 1000000000000) (10603640886 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2322964796326473 / 4000000000000) 2 (IntervalRat.scale (507 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-10783324152 / 1000000000000) (-10783324151 / 1000000000000), orderedInterval (-31294703611 / 1000000000000) (-31294703610 / 1000000000000)))) (orderedInterval (27819808435 / 1000000000000) (27819862978 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2170415039796237 / 4000000000000) 2 (IntervalRat.scale (507 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (3644503185 / 1000000000000) (3644503186 / 1000000000000), orderedInterval (-34061930673 / 1000000000000) (-34061930671 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1548910584894621 / 4000000000000) 2 (IntervalRat.scale (507 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-40533076645 / 1000000000000) (-40533076289 / 1000000000000), orderedInterval (1107606332 / 1000000000000) (1107606687 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1756299518874459 / 4000000000000) 2 (IntervalRat.scale (507 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (1409378562 / 1000000000000) (1409378563 / 1000000000000), orderedInterval (38050020711 / 1000000000000) (38050020712 / 1000000000000)))) (orderedInterval (9261817143 / 1000000000000) (9261817303 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1464219435408171 / 4000000000000) 2 (IntervalRat.scale (507 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (27699147982 / 1000000000000) (27699160461 / 1000000000000), orderedInterval (-31213065585 / 1000000000000) (-31213053106 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1293682276503591 / 4000000000000) 2 (IntervalRat.scale (507 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-25834031085 / 1000000000000) (-25834031084 / 1000000000000), orderedInterval (-36029434082 / 1000000000000) (-36029434081 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (374959547419509 / 800000000000) 2 (IntervalRat.scale (507 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-36235693818 / 1000000000000) (-36235693784 / 1000000000000), orderedInterval (-6687597206 / 1000000000000) (-6687597172 / 1000000000000)))) (orderedInterval (91142317 / 1000000000000) (91142674 / 1000000000000))) = true
  rfl'

theorem compactCertificate382_chunkChecks2_2 :
    compactCertificate382.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1037157841202223 / 4000000000000) 2 (IntervalRat.scale (507 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (31072639394 / 1000000000000) (31072652551 / 1000000000000), orderedInterval (-38657062560 / 1000000000000) (-38657049404 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (879210188195703 / 4000000000000) 2 (IntervalRat.scale (507 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (33667795055 / 1000000000000) (33667795056 / 1000000000000), orderedInterval (41909208367 / 1000000000000) (41909208368 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (550168912734909 / 4000000000000) 2 (IntervalRat.scale (507 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (6564549145 / 1000000000000) (6564549146 / 1000000000000), orderedInterval (67692288223 / 1000000000000) (67692288225 / 1000000000000)))) (orderedInterval (6545998329 / 1000000000000) (6546000595 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (295882671048003 / 4000000000000) 2 (IntervalRat.scale (507 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-55687426975 / 1000000000000) (-55687403895 / 1000000000000), orderedInterval (74574417672 / 1000000000000) (74574440753 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (803379009273009 / 4000000000000) 2 (IntervalRat.scale (507 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (30267410276 / 1000000000000) (30267410277 / 1000000000000), orderedInterval (47396734407 / 1000000000000) (47396734408 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1096945354178193 / 4000000000000) 2 (IntervalRat.scale (507 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-47762493095 / 1000000000000) (-47762492439 / 1000000000000), orderedInterval (6424908136 / 1000000000000) (6424908792 / 1000000000000)))) (orderedInterval (-3933278637 / 1000000000000) (-3933278513 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (463831087265091 / 4000000000000) 2 (IntervalRat.scale (507 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-35728520496 / 1000000000000) (-35728520495 / 1000000000000), orderedInterval (-64758194568 / 1000000000000) (-64758194567 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1885447618600611 / 4000000000000) 2 (IntervalRat.scale (507 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (28972607632 / 1000000000000) (28972607633 / 1000000000000), orderedInterval (22578654460 / 1000000000000) (22578654461 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1259391629920749 / 4000000000000) 2 (IntervalRat.scale (507 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (44754484406 / 1000000000000) (44754484444 / 1000000000000), orderedInterval (4290699268 / 1000000000000) (4290699307 / 1000000000000)))) (orderedInterval (21170450619 / 1000000000000) (21170450776 / 1000000000000))) = true
  rfl'

theorem compactCertificate382_chunkChecks2 :
    compactCertificate382.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate382.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate382_chunkChecks2_0
    compactCertificate382_chunkChecks2_1 compactCertificate382_chunkChecks2_2

theorem compactCertificate382_chunkChecks3_0 :
    compactCertificate382.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (507 / 2) 3 (IntervalRat.scale (507 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (9173775773 / 1000000000000) (9173775808 / 1000000000000), orderedInterval (-49284380787 / 1000000000000) (-49284380753 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (746907810585807 / 4000000000000) 3 (IntervalRat.scale (507 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-48618221499 / 1000000000000) (-48618174707 / 1000000000000), orderedInterval (32466331249 / 1000000000000) (32466378041 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (241534639754031 / 800000000000) 3 (IntervalRat.scale (507 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (41137778034 / 1000000000000) (41137778035 / 1000000000000), orderedInterval (20334431430 / 1000000000000) (20334431431 / 1000000000000)))) (orderedInterval (17424141321 / 1000000000000) (17424141537 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (217945836314349 / 4000000000000) 3 (IntervalRat.scale (507 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-103524399267 / 1000000000000) (-103524398069 / 1000000000000), orderedInterval (32035097716 / 1000000000000) (32035098913 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (585433172958153 / 4000000000000) 3 (IntervalRat.scale (507 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (32312476254 / 1000000000000) (32312480594 / 1000000000000), orderedInterval (-57605187111 / 1000000000000) (-57605182772 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1589564947552101 / 4000000000000) 3 (IntervalRat.scale (507 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (28877439912 / 1000000000000) (28877462870 / 1000000000000), orderedInterval (-27750785927 / 1000000000000) (-27750762969 / 1000000000000)))) (orderedInterval (-7209670979 / 1000000000000) (-7209664573 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1170866345916813 / 4000000000000) 3 (IntervalRat.scale (507 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-45327930682 / 1000000000000) (-45327930678 / 1000000000000), orderedInterval (-10888125244 / 1000000000000) (-10888125240 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2006299440506049 / 4000000000000) 3 (IntervalRat.scale (507 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-10351728054 / 1000000000000) (-10351728026 / 1000000000000), orderedInterval (34099672948 / 1000000000000) (34099672976 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1477831087265091 / 4000000000000) 3 (IntervalRat.scale (507 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-18617998356 / 1000000000000) (-18617997651 / 1000000000000), orderedInterval (37126277789 / 1000000000000) (37126278494 / 1000000000000)))) (orderedInterval (5370386684 / 1000000000000) (5370386824 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate382_chunkChecks3_1 :
    compactCertificate382.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2267372929184493 / 4000000000000) 3 (IntervalRat.scale (507 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (28197344565 / 1000000000000) (28197405346 / 1000000000000), orderedInterval (-18135797514 / 1000000000000) (-18135736734 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1309068371017797 / 4000000000000) 3 (IntervalRat.scale (507 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (42795215937 / 1000000000000) (42795215942 / 1000000000000), orderedInterval (10603640881 / 1000000000000) (10603640886 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2322964796326473 / 4000000000000) 3 (IntervalRat.scale (507 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-10783324152 / 1000000000000) (-10783324151 / 1000000000000), orderedInterval (-31294703611 / 1000000000000) (-31294703610 / 1000000000000)))) (orderedInterval (15658193215 / 1000000000000) (15658315155 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2170415039796237 / 4000000000000) 3 (IntervalRat.scale (507 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (3644503185 / 1000000000000) (3644503186 / 1000000000000), orderedInterval (-34061930673 / 1000000000000) (-34061930671 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1548910584894621 / 4000000000000) 3 (IntervalRat.scale (507 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-40533076645 / 1000000000000) (-40533076289 / 1000000000000), orderedInterval (1107606332 / 1000000000000) (1107606687 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1756299518874459 / 4000000000000) 3 (IntervalRat.scale (507 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (1409378562 / 1000000000000) (1409378563 / 1000000000000), orderedInterval (38050020711 / 1000000000000) (38050020712 / 1000000000000)))) (orderedInterval (-5439532928 / 1000000000000) (-5439532670 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1464219435408171 / 4000000000000) 3 (IntervalRat.scale (507 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (27699147982 / 1000000000000) (27699160461 / 1000000000000), orderedInterval (-31213065585 / 1000000000000) (-31213053106 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1293682276503591 / 4000000000000) 3 (IntervalRat.scale (507 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-25834031085 / 1000000000000) (-25834031084 / 1000000000000), orderedInterval (-36029434082 / 1000000000000) (-36029434081 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (374959547419509 / 800000000000) 3 (IntervalRat.scale (507 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-36235693818 / 1000000000000) (-36235693784 / 1000000000000), orderedInterval (-6687597206 / 1000000000000) (-6687597172 / 1000000000000)))) (orderedInterval (-2114607133 / 1000000000000) (-2114606611 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate382_chunkChecks3_2 :
    compactCertificate382.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1037157841202223 / 4000000000000) 3 (IntervalRat.scale (507 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (31072639394 / 1000000000000) (31072652551 / 1000000000000), orderedInterval (-38657062560 / 1000000000000) (-38657049404 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (879210188195703 / 4000000000000) 3 (IntervalRat.scale (507 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (33667795055 / 1000000000000) (33667795056 / 1000000000000), orderedInterval (41909208367 / 1000000000000) (41909208368 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (550168912734909 / 4000000000000) 3 (IntervalRat.scale (507 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (6564549145 / 1000000000000) (6564549146 / 1000000000000), orderedInterval (67692288223 / 1000000000000) (67692288225 / 1000000000000)))) (orderedInterval (-5445647636 / 1000000000000) (-5445645321 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (295882671048003 / 4000000000000) 3 (IntervalRat.scale (507 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-55687426975 / 1000000000000) (-55687403895 / 1000000000000), orderedInterval (74574417672 / 1000000000000) (74574440753 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (803379009273009 / 4000000000000) 3 (IntervalRat.scale (507 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (30267410276 / 1000000000000) (30267410277 / 1000000000000), orderedInterval (47396734407 / 1000000000000) (47396734408 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1096945354178193 / 4000000000000) 3 (IntervalRat.scale (507 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-47762493095 / 1000000000000) (-47762492439 / 1000000000000), orderedInterval (6424908136 / 1000000000000) (6424908792 / 1000000000000)))) (orderedInterval (1207861020 / 1000000000000) (1207861123 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (463831087265091 / 4000000000000) 3 (IntervalRat.scale (507 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-35728520496 / 1000000000000) (-35728520495 / 1000000000000), orderedInterval (-64758194568 / 1000000000000) (-64758194567 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1885447618600611 / 4000000000000) 3 (IntervalRat.scale (507 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (28972607632 / 1000000000000) (28972607633 / 1000000000000), orderedInterval (22578654460 / 1000000000000) (22578654461 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1259391629920749 / 4000000000000) 3 (IntervalRat.scale (507 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (44754484406 / 1000000000000) (44754484444 / 1000000000000), orderedInterval (4290699268 / 1000000000000) (4290699307 / 1000000000000)))) (orderedInterval (13311913612 / 1000000000000) (13311913852 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate382_chunkChecks3 :
    compactCertificate382.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate382.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate382_chunkChecks3_0
    compactCertificate382_chunkChecks3_1 compactCertificate382_chunkChecks3_2

theorem compactCertificate382_chunkChecks4_0 :
    compactCertificate382.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (507 / 2) 4 (IntervalRat.scale (507 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (9173775773 / 1000000000000) (9173775808 / 1000000000000), orderedInterval (-49284380787 / 1000000000000) (-49284380753 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (746907810585807 / 4000000000000) 4 (IntervalRat.scale (507 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-48618221499 / 1000000000000) (-48618174707 / 1000000000000), orderedInterval (32466331249 / 1000000000000) (32466378041 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (241534639754031 / 800000000000) 4 (IntervalRat.scale (507 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (41137778034 / 1000000000000) (41137778035 / 1000000000000), orderedInterval (20334431430 / 1000000000000) (20334431431 / 1000000000000)))) (orderedInterval (8222418424 / 1000000000000) (8222418599 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (217945836314349 / 4000000000000) 4 (IntervalRat.scale (507 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-103524399267 / 1000000000000) (-103524398069 / 1000000000000), orderedInterval (32035097716 / 1000000000000) (32035098913 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (585433172958153 / 4000000000000) 4 (IntervalRat.scale (507 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (32312476254 / 1000000000000) (32312480594 / 1000000000000), orderedInterval (-57605187111 / 1000000000000) (-57605182772 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1589564947552101 / 4000000000000) 4 (IntervalRat.scale (507 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (28877439912 / 1000000000000) (28877462870 / 1000000000000), orderedInterval (-27750785927 / 1000000000000) (-27750762969 / 1000000000000)))) (orderedInterval (-12206850091 / 1000000000000) (-12206840057 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1170866345916813 / 4000000000000) 4 (IntervalRat.scale (507 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-45327930682 / 1000000000000) (-45327930678 / 1000000000000), orderedInterval (-10888125244 / 1000000000000) (-10888125240 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2006299440506049 / 4000000000000) 4 (IntervalRat.scale (507 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-10351728054 / 1000000000000) (-10351728026 / 1000000000000), orderedInterval (34099672948 / 1000000000000) (34099672976 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1477831087265091 / 4000000000000) 4 (IntervalRat.scale (507 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-18617998356 / 1000000000000) (-18617997651 / 1000000000000), orderedInterval (37126277789 / 1000000000000) (37126278494 / 1000000000000)))) (orderedInterval (2820951673 / 1000000000000) (2820951912 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate382_chunkChecks4_1 :
    compactCertificate382.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2267372929184493 / 4000000000000) 4 (IntervalRat.scale (507 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (28197344565 / 1000000000000) (28197405346 / 1000000000000), orderedInterval (-18135797514 / 1000000000000) (-18135736734 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1309068371017797 / 4000000000000) 4 (IntervalRat.scale (507 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (42795215937 / 1000000000000) (42795215942 / 1000000000000), orderedInterval (10603640881 / 1000000000000) (10603640886 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2322964796326473 / 4000000000000) 4 (IntervalRat.scale (507 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-10783324152 / 1000000000000) (-10783324151 / 1000000000000), orderedInterval (-31294703611 / 1000000000000) (-31294703610 / 1000000000000)))) (orderedInterval (-158795612079 / 1000000000000) (-158795338950 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2170415039796237 / 4000000000000) 4 (IntervalRat.scale (507 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (3644503185 / 1000000000000) (3644503186 / 1000000000000), orderedInterval (-34061930673 / 1000000000000) (-34061930671 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1548910584894621 / 4000000000000) 4 (IntervalRat.scale (507 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-40533076645 / 1000000000000) (-40533076289 / 1000000000000), orderedInterval (1107606332 / 1000000000000) (1107606687 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1756299518874459 / 4000000000000) 4 (IntervalRat.scale (507 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (1409378562 / 1000000000000) (1409378563 / 1000000000000), orderedInterval (38050020711 / 1000000000000) (38050020712 / 1000000000000)))) (orderedInterval (-22270321354 / 1000000000000) (-22270320931 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1464219435408171 / 4000000000000) 4 (IntervalRat.scale (507 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (27699147982 / 1000000000000) (27699160461 / 1000000000000), orderedInterval (-31213065585 / 1000000000000) (-31213053106 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1293682276503591 / 4000000000000) 4 (IntervalRat.scale (507 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-25834031085 / 1000000000000) (-25834031084 / 1000000000000), orderedInterval (-36029434082 / 1000000000000) (-36029434081 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (374959547419509 / 800000000000) 4 (IntervalRat.scale (507 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-36235693818 / 1000000000000) (-36235693784 / 1000000000000), orderedInterval (-6687597206 / 1000000000000) (-6687597172 / 1000000000000)))) (orderedInterval (-5517652841 / 1000000000000) (-5517652073 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate382_chunkChecks4_2 :
    compactCertificate382.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1037157841202223 / 4000000000000) 4 (IntervalRat.scale (507 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (31072639394 / 1000000000000) (31072652551 / 1000000000000), orderedInterval (-38657062560 / 1000000000000) (-38657049404 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (879210188195703 / 4000000000000) 4 (IntervalRat.scale (507 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (33667795055 / 1000000000000) (33667795056 / 1000000000000), orderedInterval (41909208367 / 1000000000000) (41909208368 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (550168912734909 / 4000000000000) 4 (IntervalRat.scale (507 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (6564549145 / 1000000000000) (6564549146 / 1000000000000), orderedInterval (67692288223 / 1000000000000) (67692288225 / 1000000000000)))) (orderedInterval (-6453431780 / 1000000000000) (-6453429406 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (295882671048003 / 4000000000000) 4 (IntervalRat.scale (507 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-55687426975 / 1000000000000) (-55687403895 / 1000000000000), orderedInterval (74574417672 / 1000000000000) (74574440753 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (803379009273009 / 4000000000000) 4 (IntervalRat.scale (507 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (30267410276 / 1000000000000) (30267410277 / 1000000000000), orderedInterval (47396734407 / 1000000000000) (47396734408 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1096945354178193 / 4000000000000) 4 (IntervalRat.scale (507 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-47762493095 / 1000000000000) (-47762492439 / 1000000000000), orderedInterval (6424908136 / 1000000000000) (6424908792 / 1000000000000)))) (orderedInterval (4740600261 / 1000000000000) (4740600364 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (463831087265091 / 4000000000000) 4 (IntervalRat.scale (507 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-35728520496 / 1000000000000) (-35728520495 / 1000000000000), orderedInterval (-64758194568 / 1000000000000) (-64758194567 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1885447618600611 / 4000000000000) 4 (IntervalRat.scale (507 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (28972607632 / 1000000000000) (28972607633 / 1000000000000), orderedInterval (22578654460 / 1000000000000) (22578654461 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1259391629920749 / 4000000000000) 4 (IntervalRat.scale (507 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (44754484406 / 1000000000000) (44754484444 / 1000000000000), orderedInterval (4290699268 / 1000000000000) (4290699307 / 1000000000000)))) (orderedInterval (-48287460833 / 1000000000000) (-48287460453 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate382_chunkChecks4 :
    compactCertificate382.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate382.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate382_chunkChecks4_0
    compactCertificate382_chunkChecks4_1 compactCertificate382_chunkChecks4_2

theorem compactCertificate382_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate382.chunkCheck r b = true :=
  compactCertificate382.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate382_chunkChecks0
    · exact compactCertificate382_chunkChecks1
    · exact compactCertificate382_chunkChecks2
    · exact compactCertificate382_chunkChecks3
    · exact compactCertificate382_chunkChecks4)

theorem compactCertificate382_coefficient0 :
    compactCertificate382.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate382_coefficient1 :
    compactCertificate382.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate382_coefficient2 :
    compactCertificate382.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate382_coefficient3 :
    compactCertificate382.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate382_coefficient4 :
    compactCertificate382.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate382_coefficients : ∀ r : Fin 5,
    compactCertificate382.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate382_coefficient0
  · exact compactCertificate382_coefficient1
  · exact compactCertificate382_coefficient2
  · exact compactCertificate382_coefficient3
  · exact compactCertificate382_coefficient4

theorem compactCertificate382_lower : (1 : ℚ) ≤ compactCertificate382.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate382, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate382_proves {t : ℝ} (ht : t ∈ compactCertificate382.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate382.proves compactCertificate382_states compactCertificate382_chunks
    compactCertificate382_coefficients compactCertificate382_lower ht

end Erdos232
