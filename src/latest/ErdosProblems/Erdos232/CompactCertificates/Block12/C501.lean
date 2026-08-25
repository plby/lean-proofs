/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate501 : CompactCertificate where
  left := 372
  right := 373
  center := 745 / 2
  grid := fun i =>
    match i.val with
    | 0 => 119
    | 1 => 87
    | 2 => 141
    | 3 => 25
    | 4 => 68
    | 5 => 186
    | 6 => 137
    | 7 => 235
    | 8 => 173
    | 9 => 265
    | 10 => 153
    | 11 => 272
    | 12 => 254
    | 13 => 181
    | 14 => 205
    | 15 => 171
    | 16 => 151
    | 17 => 219
    | 18 => 121
    | 19 => 103
    | 20 => 64
    | 21 => 35
    | 22 => 94
    | 23 => 128
    | 24 => 54
    | 25 => 221
    | _ => 147
  point := fun i =>
    match i.val with
    | 0 => 745 / 2
    | 1 => 219505451237249 / 800000000000
    | 2 => 70983552906017 / 160000000000
    | 3 => 64051143216643 / 800000000000
    | 4 => 172050380218471 / 800000000000
    | 5 => 467150250858507 / 800000000000
    | 6 => 344100760437091 / 800000000000
    | 7 => 589622518018543 / 800000000000
    | 8 => 434313278111437 / 800000000000
    | 9 => 666348257294851 / 800000000000
    | 10 => 384716345723179 / 800000000000
    | 11 => 682685906612711 / 800000000000
    | 12 => 637853729644259 / 800000000000
    | 13 => 455202519032147 / 800000000000
    | 14 => 516151140655413 / 800000000000
    | 15 => 430313009616997 / 800000000000
    | 16 => 380194594080937 / 800000000000
    | 17 => 110195212160763 / 160000000000
    | 18 => 304805756092961 / 800000000000
    | 19 => 258387215071321 / 800000000000
    | 20 => 161686721888563 / 800000000000
    | 21 => 86955656777421 / 800000000000
    | 22 => 236101523435263 / 800000000000
    | 23 => 322376445310751 / 800000000000
    | 24 => 136313278111437 / 800000000000
    | 25 => 554105907636077 / 800000000000
    | _ => 370117066781443 / 800000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (22115660901 / 1000000000000) (22115663114 / 1000000000000), orderedInterval (-34957390664 / 1000000000000) (-34957388451 / 1000000000000))
    | 1 => (orderedInterval (-46326946004 / 1000000000000) (-46326942498 / 1000000000000), orderedInterval (13275613670 / 1000000000000) (13275617175 / 1000000000000))
    | 2 => (orderedInterval (-37680054668 / 1000000000000) (-37680054576 / 1000000000000), orderedInterval (-3853827951 / 1000000000000) (-3853827859 / 1000000000000))
    | 3 => (orderedInterval (-66019970196 / 1000000000000) (-66019862654 / 1000000000000), orderedInterval (60351761048 / 1000000000000) (60351868589 / 1000000000000))
    | 4 => (orderedInterval (43355588466 / 1000000000000) (43355678710 / 1000000000000), orderedInterval (-32970915985 / 1000000000000) (-32970825741 / 1000000000000))
    | 5 => (orderedInterval (12454345431 / 1000000000000) (12454345432 / 1000000000000), orderedInterval (30568871646 / 1000000000000) (30568871647 / 1000000000000))
    | 6 => (orderedInterval (-18877142703 / 1000000000000) (-18877142702 / 1000000000000), orderedInterval (-33500162035 / 1000000000000) (-33500162034 / 1000000000000))
    | 7 => (orderedInterval (13071216900 / 1000000000000) (13071216955 / 1000000000000), orderedInterval (-26332037868 / 1000000000000) (-26332037813 / 1000000000000))
    | 8 => (orderedInterval (-6172326729 / 1000000000000) (-6172326728 / 1000000000000), orderedInterval (-33677383093 / 1000000000000) (-33677383092 / 1000000000000))
    | 9 => (orderedInterval (-25752386290 / 1000000000000) (-25752386258 / 1000000000000), orderedInterval (-10040547938 / 1000000000000) (-10040547906 / 1000000000000))
    | 10 => (orderedInterval (-30944108802 / 1000000000000) (-30944108801 / 1000000000000), orderedInterval (-19106359356 / 1000000000000) (-19106359355 / 1000000000000))
    | 11 => (orderedInterval (-9891351935 / 1000000000000) (-9891351930 / 1000000000000), orderedInterval (25465155745 / 1000000000000) (25465155751 / 1000000000000))
    | 12 => (orderedInterval (3883432228 / 1000000000000) (3883432229 / 1000000000000), orderedInterval (27986338662 / 1000000000000) (27986338663 / 1000000000000))
    | 13 => (orderedInterval (-30666873132 / 1000000000000) (-30666873129 / 1000000000000), orderedInterval (-13328802833 / 1000000000000) (-13328802830 / 1000000000000))
    | 14 => (orderedInterval (-29207978815 / 1000000000000) (-29207922046 / 1000000000000), orderedInterval (11581747851 / 1000000000000) (11581804619 / 1000000000000))
    | 15 => (orderedInterval (-34207020621 / 1000000000000) (-34207020453 / 1000000000000), orderedInterval (-3632433401 / 1000000000000) (-3632433232 / 1000000000000))
    | 16 => (orderedInterval (-36491371884 / 1000000000000) (-36491370731 / 1000000000000), orderedInterval (2857125544 / 1000000000000) (2857126697 / 1000000000000))
    | 17 => (orderedInterval (-30319284087 / 1000000000000) (-30319283401 / 1000000000000), orderedInterval (-2234708146 / 1000000000000) (-2234707460 / 1000000000000))
    | 18 => (orderedInterval (-40715555535 / 1000000000000) (-40715554786 / 1000000000000), orderedInterval (3676776725 / 1000000000000) (3676777474 / 1000000000000))
    | 19 => (orderedInterval (-8166010860 / 1000000000000) (-8166010859 / 1000000000000), orderedInterval (-43626504236 / 1000000000000) (-43626504235 / 1000000000000))
    | 20 => (orderedInterval (54230911397 / 1000000000000) (54230913339 / 1000000000000), orderedInterval (-14587274667 / 1000000000000) (-14587272725 / 1000000000000))
    | 21 => (orderedInterval (35131138897 / 1000000000000) (35131142542 / 1000000000000), orderedInterval (-68152771394 / 1000000000000) (-68152767749 / 1000000000000))
    | 22 => (orderedInterval (26307700598 / 1000000000000) (26307700599 / 1000000000000), orderedInterval (38230894350 / 1000000000000) (38230894351 / 1000000000000))
    | 23 => (orderedInterval (39672998752 / 1000000000000) (39672999363 / 1000000000000), orderedInterval (-2471833701 / 1000000000000) (-2471833090 / 1000000000000))
    | 24 => (orderedInterval (61074245037 / 1000000000000) (61074245068 / 1000000000000), orderedInterval (2297943577 / 1000000000000) (2297943607 / 1000000000000))
    | 25 => (orderedInterval (23257572970 / 1000000000000) (23257583466 / 1000000000000), orderedInterval (-19464566232 / 1000000000000) (-19464555736 / 1000000000000))
    | _ => (orderedInterval (-37054825270 / 1000000000000) (-37054824529 / 1000000000000), orderedInterval (1766012500 / 1000000000000) (1766013241 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (6123087939 / 1000000000000) (6123088881 / 1000000000000)
      | 1 => orderedInterval (1413881967 / 1000000000000) (1413886474 / 1000000000000)
      | 2 => orderedInterval (-552341599 / 1000000000000) (-552341575 / 1000000000000)
      | 3 => orderedInterval (877070249 / 1000000000000) (877070404 / 1000000000000)
      | 4 => orderedInterval (-2822246464 / 1000000000000) (-2822246131 / 1000000000000)
      | 5 => orderedInterval (916975048 / 1000000000000) (916975170 / 1000000000000)
      | 6 => orderedInterval (8737807308 / 1000000000000) (8737807584 / 1000000000000)
      | 7 => orderedInterval (-4286033694 / 1000000000000) (-4286033535 / 1000000000000)
      | _ => orderedInterval (5427434942 / 1000000000000) (5427436039 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-14034107796 / 1000000000000) (-14034106859 / 1000000000000)
      | 1 => orderedInterval (-4242402824 / 1000000000000) (-4242400620 / 1000000000000)
      | 2 => orderedInterval (420766145 / 1000000000000) (420766185 / 1000000000000)
      | 3 => orderedInterval (10454850898 / 1000000000000) (10454851219 / 1000000000000)
      | 4 => orderedInterval (-3108264200 / 1000000000000) (-3108263629 / 1000000000000)
      | 5 => orderedInterval (-374961939 / 1000000000000) (-374961768 / 1000000000000)
      | 6 => orderedInterval (1282043529 / 1000000000000) (1282043773 / 1000000000000)
      | 7 => orderedInterval (-115034624 / 1000000000000) (-115034513 / 1000000000000)
      | _ => orderedInterval (2540947804 / 1000000000000) (2540949710 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-5357571538 / 1000000000000) (-5357570599 / 1000000000000)
      | 1 => orderedInterval (1626379420 / 1000000000000) (1626380649 / 1000000000000)
      | 2 => orderedInterval (1894074147 / 1000000000000) (1894074219 / 1000000000000)
      | 3 => orderedInterval (-11706784791 / 1000000000000) (-11706784103 / 1000000000000)
      | 4 => orderedInterval (6652661622 / 1000000000000) (6652662605 / 1000000000000)
      | 5 => orderedInterval (79273445 / 1000000000000) (79273694 / 1000000000000)
      | 6 => orderedInterval (-7681526612 / 1000000000000) (-7681526385 / 1000000000000)
      | 7 => orderedInterval (3988454266 / 1000000000000) (3988454367 / 1000000000000)
      | _ => orderedInterval (-4262919425 / 1000000000000) (-4262916037 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (14202782331 / 1000000000000) (14202783272 / 1000000000000)
      | 1 => orderedInterval (8605346451 / 1000000000000) (8605347206 / 1000000000000)
      | 2 => orderedInterval (-3776561396 / 1000000000000) (-3776561265 / 1000000000000)
      | 3 => orderedInterval (-60392868145 / 1000000000000) (-60392866633 / 1000000000000)
      | 4 => orderedInterval (9733690204 / 1000000000000) (9733691902 / 1000000000000)
      | 5 => orderedInterval (827267594 / 1000000000000) (827267967 / 1000000000000)
      | 6 => orderedInterval (-884069781 / 1000000000000) (-884069562 / 1000000000000)
      | 7 => orderedInterval (149548645 / 1000000000000) (149548748 / 1000000000000)
      | _ => orderedInterval (-9541140326 / 1000000000000) (-9541134229 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (4113565434 / 1000000000000) (4113566382 / 1000000000000)
      | 1 => orderedInterval (-5215508464 / 1000000000000) (-5215507930 / 1000000000000)
      | 2 => orderedInterval (-6831740441 / 1000000000000) (-6831740197 / 1000000000000)
      | 3 => orderedInterval (69623490516 / 1000000000000) (69623493870 / 1000000000000)
      | 4 => orderedInterval (-15982124974 / 1000000000000) (-15982122028 / 1000000000000)
      | 5 => orderedInterval (-5260818479 / 1000000000000) (-5260817901 / 1000000000000)
      | 6 => orderedInterval (7544446726 / 1000000000000) (7544446942 / 1000000000000)
      | 7 => orderedInterval (-4404856873 / 1000000000000) (-4404856764 / 1000000000000)
      | _ => orderedInterval (-6020111609 / 1000000000000) (-6020100505 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (15835635696 / 1000000000000) (15835643311 / 1000000000000)
    | 1 => orderedInterval (-7176163007 / 1000000000000) (-7176156502 / 1000000000000)
    | 2 => orderedInterval (-14767959466 / 1000000000000) (-14767951590 / 1000000000000)
    | 3 => orderedInterval (-41076004423 / 1000000000000) (-41075992594 / 1000000000000)
    | _ => orderedInterval (37566341836 / 1000000000000) (37566361869 / 1000000000000)

theorem compactCertificate501_stateChecks0 :
    compactCertificate501.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 119 12 (745 / 2)) (orderedInterval (22115660901 / 1000000000000) (22115663114 / 1000000000000), orderedInterval (-34957390664 / 1000000000000) (-34957388451 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 87 12 (219505451237249 / 800000000000)) (orderedInterval (-46326946004 / 1000000000000) (-46326942498 / 1000000000000), orderedInterval (13275613670 / 1000000000000) (13275617175 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 141 12 (70983552906017 / 160000000000)) (orderedInterval (-37680054668 / 1000000000000) (-37680054576 / 1000000000000), orderedInterval (-3853827951 / 1000000000000) (-3853827859 / 1000000000000))) = true
  rfl'

theorem compactCertificate501_stateChecks1 :
    compactCertificate501.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 25 12 (64051143216643 / 800000000000)) (orderedInterval (-66019970196 / 1000000000000) (-66019862654 / 1000000000000), orderedInterval (60351761048 / 1000000000000) (60351868589 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (172050380218471 / 800000000000)) (orderedInterval (43355588466 / 1000000000000) (43355678710 / 1000000000000), orderedInterval (-32970915985 / 1000000000000) (-32970825741 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 186 12 (467150250858507 / 800000000000)) (orderedInterval (12454345431 / 1000000000000) (12454345432 / 1000000000000), orderedInterval (30568871646 / 1000000000000) (30568871647 / 1000000000000))) = true
  rfl'

theorem compactCertificate501_stateChecks2 :
    compactCertificate501.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 137 12 (344100760437091 / 800000000000)) (orderedInterval (-18877142703 / 1000000000000) (-18877142702 / 1000000000000), orderedInterval (-33500162035 / 1000000000000) (-33500162034 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 235 12 (589622518018543 / 800000000000)) (orderedInterval (13071216900 / 1000000000000) (13071216955 / 1000000000000), orderedInterval (-26332037868 / 1000000000000) (-26332037813 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 173 12 (434313278111437 / 800000000000)) (orderedInterval (-6172326729 / 1000000000000) (-6172326728 / 1000000000000), orderedInterval (-33677383093 / 1000000000000) (-33677383092 / 1000000000000))) = true
  rfl'

theorem compactCertificate501_stateChecks3 :
    compactCertificate501.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 265 12 (666348257294851 / 800000000000)) (orderedInterval (-25752386290 / 1000000000000) (-25752386258 / 1000000000000), orderedInterval (-10040547938 / 1000000000000) (-10040547906 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 153 12 (384716345723179 / 800000000000)) (orderedInterval (-30944108802 / 1000000000000) (-30944108801 / 1000000000000), orderedInterval (-19106359356 / 1000000000000) (-19106359355 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 272 12 (682685906612711 / 800000000000)) (orderedInterval (-9891351935 / 1000000000000) (-9891351930 / 1000000000000), orderedInterval (25465155745 / 1000000000000) (25465155751 / 1000000000000))) = true
  rfl'

theorem compactCertificate501_stateChecks4 :
    compactCertificate501.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 254 12 (637853729644259 / 800000000000)) (orderedInterval (3883432228 / 1000000000000) (3883432229 / 1000000000000), orderedInterval (27986338662 / 1000000000000) (27986338663 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 181 12 (455202519032147 / 800000000000)) (orderedInterval (-30666873132 / 1000000000000) (-30666873129 / 1000000000000), orderedInterval (-13328802833 / 1000000000000) (-13328802830 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 205 12 (516151140655413 / 800000000000)) (orderedInterval (-29207978815 / 1000000000000) (-29207922046 / 1000000000000), orderedInterval (11581747851 / 1000000000000) (11581804619 / 1000000000000))) = true
  rfl'

theorem compactCertificate501_stateChecks5 :
    compactCertificate501.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 171 12 (430313009616997 / 800000000000)) (orderedInterval (-34207020621 / 1000000000000) (-34207020453 / 1000000000000), orderedInterval (-3632433401 / 1000000000000) (-3632433232 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 151 12 (380194594080937 / 800000000000)) (orderedInterval (-36491371884 / 1000000000000) (-36491370731 / 1000000000000), orderedInterval (2857125544 / 1000000000000) (2857126697 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 219 12 (110195212160763 / 160000000000)) (orderedInterval (-30319284087 / 1000000000000) (-30319283401 / 1000000000000), orderedInterval (-2234708146 / 1000000000000) (-2234707460 / 1000000000000))) = true
  rfl'

theorem compactCertificate501_stateChecks6 :
    compactCertificate501.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 121 12 (304805756092961 / 800000000000)) (orderedInterval (-40715555535 / 1000000000000) (-40715554786 / 1000000000000), orderedInterval (3676776725 / 1000000000000) (3676777474 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 103 12 (258387215071321 / 800000000000)) (orderedInterval (-8166010860 / 1000000000000) (-8166010859 / 1000000000000), orderedInterval (-43626504236 / 1000000000000) (-43626504235 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (161686721888563 / 800000000000)) (orderedInterval (54230911397 / 1000000000000) (54230913339 / 1000000000000), orderedInterval (-14587274667 / 1000000000000) (-14587272725 / 1000000000000))) = true
  rfl'

theorem compactCertificate501_stateChecks7 :
    compactCertificate501.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 35 12 (86955656777421 / 800000000000)) (orderedInterval (35131138897 / 1000000000000) (35131142542 / 1000000000000), orderedInterval (-68152771394 / 1000000000000) (-68152767749 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 94 12 (236101523435263 / 800000000000)) (orderedInterval (26307700598 / 1000000000000) (26307700599 / 1000000000000), orderedInterval (38230894350 / 1000000000000) (38230894351 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 128 12 (322376445310751 / 800000000000)) (orderedInterval (39672998752 / 1000000000000) (39672999363 / 1000000000000), orderedInterval (-2471833701 / 1000000000000) (-2471833090 / 1000000000000))) = true
  rfl'

theorem compactCertificate501_stateChecks8 :
    compactCertificate501.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (136313278111437 / 800000000000)) (orderedInterval (61074245037 / 1000000000000) (61074245068 / 1000000000000), orderedInterval (2297943577 / 1000000000000) (2297943607 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 221 12 (554105907636077 / 800000000000)) (orderedInterval (23257572970 / 1000000000000) (23257583466 / 1000000000000), orderedInterval (-19464566232 / 1000000000000) (-19464555736 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 147 12 (370117066781443 / 800000000000)) (orderedInterval (-37054825270 / 1000000000000) (-37054824529 / 1000000000000), orderedInterval (1766012500 / 1000000000000) (1766013241 / 1000000000000))) = true
  rfl'

theorem compactCertificate501_states : ∀ j,
    BesselStateValid (compactCertificate501.point j) (compactCertificate501.state j) :=
  compactCertificate501.statesValid_of_checks3 compactCertificate501_stateChecks0
    compactCertificate501_stateChecks1 compactCertificate501_stateChecks2
    compactCertificate501_stateChecks3 compactCertificate501_stateChecks4
    compactCertificate501_stateChecks5 compactCertificate501_stateChecks6
    compactCertificate501_stateChecks7 compactCertificate501_stateChecks8

theorem compactCertificate501_chunkChecks0_0 :
    compactCertificate501.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (745 / 2) 0 (IntervalRat.scale (745 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (22115660901 / 1000000000000) (22115663114 / 1000000000000), orderedInterval (-34957390664 / 1000000000000) (-34957388451 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (219505451237249 / 800000000000) 0 (IntervalRat.scale (745 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-46326946004 / 1000000000000) (-46326942498 / 1000000000000), orderedInterval (13275613670 / 1000000000000) (13275617175 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (70983552906017 / 160000000000) 0 (IntervalRat.scale (745 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-37680054668 / 1000000000000) (-37680054576 / 1000000000000), orderedInterval (-3853827951 / 1000000000000) (-3853827859 / 1000000000000)))) (orderedInterval (6123087939 / 1000000000000) (6123088881 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (64051143216643 / 800000000000) 0 (IntervalRat.scale (745 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-66019970196 / 1000000000000) (-66019862654 / 1000000000000), orderedInterval (60351761048 / 1000000000000) (60351868589 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (172050380218471 / 800000000000) 0 (IntervalRat.scale (745 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (43355588466 / 1000000000000) (43355678710 / 1000000000000), orderedInterval (-32970915985 / 1000000000000) (-32970825741 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (467150250858507 / 800000000000) 0 (IntervalRat.scale (745 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (12454345431 / 1000000000000) (12454345432 / 1000000000000), orderedInterval (30568871646 / 1000000000000) (30568871647 / 1000000000000)))) (orderedInterval (1413881967 / 1000000000000) (1413886474 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (344100760437091 / 800000000000) 0 (IntervalRat.scale (745 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-18877142703 / 1000000000000) (-18877142702 / 1000000000000), orderedInterval (-33500162035 / 1000000000000) (-33500162034 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (589622518018543 / 800000000000) 0 (IntervalRat.scale (745 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (13071216900 / 1000000000000) (13071216955 / 1000000000000), orderedInterval (-26332037868 / 1000000000000) (-26332037813 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (434313278111437 / 800000000000) 0 (IntervalRat.scale (745 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-6172326729 / 1000000000000) (-6172326728 / 1000000000000), orderedInterval (-33677383093 / 1000000000000) (-33677383092 / 1000000000000)))) (orderedInterval (-552341599 / 1000000000000) (-552341575 / 1000000000000))) = true
  rfl'

theorem compactCertificate501_chunkChecks0_1 :
    compactCertificate501.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (666348257294851 / 800000000000) 0 (IntervalRat.scale (745 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-25752386290 / 1000000000000) (-25752386258 / 1000000000000), orderedInterval (-10040547938 / 1000000000000) (-10040547906 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (384716345723179 / 800000000000) 0 (IntervalRat.scale (745 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-30944108802 / 1000000000000) (-30944108801 / 1000000000000), orderedInterval (-19106359356 / 1000000000000) (-19106359355 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (682685906612711 / 800000000000) 0 (IntervalRat.scale (745 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-9891351935 / 1000000000000) (-9891351930 / 1000000000000), orderedInterval (25465155745 / 1000000000000) (25465155751 / 1000000000000)))) (orderedInterval (877070249 / 1000000000000) (877070404 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (637853729644259 / 800000000000) 0 (IntervalRat.scale (745 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (3883432228 / 1000000000000) (3883432229 / 1000000000000), orderedInterval (27986338662 / 1000000000000) (27986338663 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (455202519032147 / 800000000000) 0 (IntervalRat.scale (745 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-30666873132 / 1000000000000) (-30666873129 / 1000000000000), orderedInterval (-13328802833 / 1000000000000) (-13328802830 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (516151140655413 / 800000000000) 0 (IntervalRat.scale (745 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-29207978815 / 1000000000000) (-29207922046 / 1000000000000), orderedInterval (11581747851 / 1000000000000) (11581804619 / 1000000000000)))) (orderedInterval (-2822246464 / 1000000000000) (-2822246131 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (430313009616997 / 800000000000) 0 (IntervalRat.scale (745 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-34207020621 / 1000000000000) (-34207020453 / 1000000000000), orderedInterval (-3632433401 / 1000000000000) (-3632433232 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (380194594080937 / 800000000000) 0 (IntervalRat.scale (745 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-36491371884 / 1000000000000) (-36491370731 / 1000000000000), orderedInterval (2857125544 / 1000000000000) (2857126697 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (110195212160763 / 160000000000) 0 (IntervalRat.scale (745 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-30319284087 / 1000000000000) (-30319283401 / 1000000000000), orderedInterval (-2234708146 / 1000000000000) (-2234707460 / 1000000000000)))) (orderedInterval (916975048 / 1000000000000) (916975170 / 1000000000000))) = true
  rfl'

theorem compactCertificate501_chunkChecks0_2 :
    compactCertificate501.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (304805756092961 / 800000000000) 0 (IntervalRat.scale (745 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-40715555535 / 1000000000000) (-40715554786 / 1000000000000), orderedInterval (3676776725 / 1000000000000) (3676777474 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (258387215071321 / 800000000000) 0 (IntervalRat.scale (745 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-8166010860 / 1000000000000) (-8166010859 / 1000000000000), orderedInterval (-43626504236 / 1000000000000) (-43626504235 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (161686721888563 / 800000000000) 0 (IntervalRat.scale (745 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (54230911397 / 1000000000000) (54230913339 / 1000000000000), orderedInterval (-14587274667 / 1000000000000) (-14587272725 / 1000000000000)))) (orderedInterval (8737807308 / 1000000000000) (8737807584 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (86955656777421 / 800000000000) 0 (IntervalRat.scale (745 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (35131138897 / 1000000000000) (35131142542 / 1000000000000), orderedInterval (-68152771394 / 1000000000000) (-68152767749 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (236101523435263 / 800000000000) 0 (IntervalRat.scale (745 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (26307700598 / 1000000000000) (26307700599 / 1000000000000), orderedInterval (38230894350 / 1000000000000) (38230894351 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (322376445310751 / 800000000000) 0 (IntervalRat.scale (745 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (39672998752 / 1000000000000) (39672999363 / 1000000000000), orderedInterval (-2471833701 / 1000000000000) (-2471833090 / 1000000000000)))) (orderedInterval (-4286033694 / 1000000000000) (-4286033535 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (136313278111437 / 800000000000) 0 (IntervalRat.scale (745 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (61074245037 / 1000000000000) (61074245068 / 1000000000000), orderedInterval (2297943577 / 1000000000000) (2297943607 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (554105907636077 / 800000000000) 0 (IntervalRat.scale (745 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (23257572970 / 1000000000000) (23257583466 / 1000000000000), orderedInterval (-19464566232 / 1000000000000) (-19464555736 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (370117066781443 / 800000000000) 0 (IntervalRat.scale (745 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-37054825270 / 1000000000000) (-37054824529 / 1000000000000), orderedInterval (1766012500 / 1000000000000) (1766013241 / 1000000000000)))) (orderedInterval (5427434942 / 1000000000000) (5427436039 / 1000000000000))) = true
  rfl'

theorem compactCertificate501_chunkChecks0 :
    compactCertificate501.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate501.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate501_chunkChecks0_0
    compactCertificate501_chunkChecks0_1 compactCertificate501_chunkChecks0_2

theorem compactCertificate501_chunkChecks1_0 :
    compactCertificate501.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (745 / 2) 1 (IntervalRat.scale (745 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (22115660901 / 1000000000000) (22115663114 / 1000000000000), orderedInterval (-34957390664 / 1000000000000) (-34957388451 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (219505451237249 / 800000000000) 1 (IntervalRat.scale (745 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-46326946004 / 1000000000000) (-46326942498 / 1000000000000), orderedInterval (13275613670 / 1000000000000) (13275617175 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (70983552906017 / 160000000000) 1 (IntervalRat.scale (745 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-37680054668 / 1000000000000) (-37680054576 / 1000000000000), orderedInterval (-3853827951 / 1000000000000) (-3853827859 / 1000000000000)))) (orderedInterval (-14034107796 / 1000000000000) (-14034106859 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (64051143216643 / 800000000000) 1 (IntervalRat.scale (745 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-66019970196 / 1000000000000) (-66019862654 / 1000000000000), orderedInterval (60351761048 / 1000000000000) (60351868589 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (172050380218471 / 800000000000) 1 (IntervalRat.scale (745 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (43355588466 / 1000000000000) (43355678710 / 1000000000000), orderedInterval (-32970915985 / 1000000000000) (-32970825741 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (467150250858507 / 800000000000) 1 (IntervalRat.scale (745 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (12454345431 / 1000000000000) (12454345432 / 1000000000000), orderedInterval (30568871646 / 1000000000000) (30568871647 / 1000000000000)))) (orderedInterval (-4242402824 / 1000000000000) (-4242400620 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (344100760437091 / 800000000000) 1 (IntervalRat.scale (745 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-18877142703 / 1000000000000) (-18877142702 / 1000000000000), orderedInterval (-33500162035 / 1000000000000) (-33500162034 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (589622518018543 / 800000000000) 1 (IntervalRat.scale (745 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (13071216900 / 1000000000000) (13071216955 / 1000000000000), orderedInterval (-26332037868 / 1000000000000) (-26332037813 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (434313278111437 / 800000000000) 1 (IntervalRat.scale (745 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-6172326729 / 1000000000000) (-6172326728 / 1000000000000), orderedInterval (-33677383093 / 1000000000000) (-33677383092 / 1000000000000)))) (orderedInterval (420766145 / 1000000000000) (420766185 / 1000000000000))) = true
  rfl'

theorem compactCertificate501_chunkChecks1_1 :
    compactCertificate501.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (666348257294851 / 800000000000) 1 (IntervalRat.scale (745 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-25752386290 / 1000000000000) (-25752386258 / 1000000000000), orderedInterval (-10040547938 / 1000000000000) (-10040547906 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (384716345723179 / 800000000000) 1 (IntervalRat.scale (745 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-30944108802 / 1000000000000) (-30944108801 / 1000000000000), orderedInterval (-19106359356 / 1000000000000) (-19106359355 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (682685906612711 / 800000000000) 1 (IntervalRat.scale (745 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-9891351935 / 1000000000000) (-9891351930 / 1000000000000), orderedInterval (25465155745 / 1000000000000) (25465155751 / 1000000000000)))) (orderedInterval (10454850898 / 1000000000000) (10454851219 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (637853729644259 / 800000000000) 1 (IntervalRat.scale (745 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (3883432228 / 1000000000000) (3883432229 / 1000000000000), orderedInterval (27986338662 / 1000000000000) (27986338663 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (455202519032147 / 800000000000) 1 (IntervalRat.scale (745 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-30666873132 / 1000000000000) (-30666873129 / 1000000000000), orderedInterval (-13328802833 / 1000000000000) (-13328802830 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (516151140655413 / 800000000000) 1 (IntervalRat.scale (745 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-29207978815 / 1000000000000) (-29207922046 / 1000000000000), orderedInterval (11581747851 / 1000000000000) (11581804619 / 1000000000000)))) (orderedInterval (-3108264200 / 1000000000000) (-3108263629 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (430313009616997 / 800000000000) 1 (IntervalRat.scale (745 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-34207020621 / 1000000000000) (-34207020453 / 1000000000000), orderedInterval (-3632433401 / 1000000000000) (-3632433232 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (380194594080937 / 800000000000) 1 (IntervalRat.scale (745 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-36491371884 / 1000000000000) (-36491370731 / 1000000000000), orderedInterval (2857125544 / 1000000000000) (2857126697 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (110195212160763 / 160000000000) 1 (IntervalRat.scale (745 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-30319284087 / 1000000000000) (-30319283401 / 1000000000000), orderedInterval (-2234708146 / 1000000000000) (-2234707460 / 1000000000000)))) (orderedInterval (-374961939 / 1000000000000) (-374961768 / 1000000000000))) = true
  rfl'

theorem compactCertificate501_chunkChecks1_2 :
    compactCertificate501.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (304805756092961 / 800000000000) 1 (IntervalRat.scale (745 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-40715555535 / 1000000000000) (-40715554786 / 1000000000000), orderedInterval (3676776725 / 1000000000000) (3676777474 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (258387215071321 / 800000000000) 1 (IntervalRat.scale (745 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-8166010860 / 1000000000000) (-8166010859 / 1000000000000), orderedInterval (-43626504236 / 1000000000000) (-43626504235 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (161686721888563 / 800000000000) 1 (IntervalRat.scale (745 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (54230911397 / 1000000000000) (54230913339 / 1000000000000), orderedInterval (-14587274667 / 1000000000000) (-14587272725 / 1000000000000)))) (orderedInterval (1282043529 / 1000000000000) (1282043773 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (86955656777421 / 800000000000) 1 (IntervalRat.scale (745 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (35131138897 / 1000000000000) (35131142542 / 1000000000000), orderedInterval (-68152771394 / 1000000000000) (-68152767749 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (236101523435263 / 800000000000) 1 (IntervalRat.scale (745 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (26307700598 / 1000000000000) (26307700599 / 1000000000000), orderedInterval (38230894350 / 1000000000000) (38230894351 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (322376445310751 / 800000000000) 1 (IntervalRat.scale (745 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (39672998752 / 1000000000000) (39672999363 / 1000000000000), orderedInterval (-2471833701 / 1000000000000) (-2471833090 / 1000000000000)))) (orderedInterval (-115034624 / 1000000000000) (-115034513 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (136313278111437 / 800000000000) 1 (IntervalRat.scale (745 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (61074245037 / 1000000000000) (61074245068 / 1000000000000), orderedInterval (2297943577 / 1000000000000) (2297943607 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (554105907636077 / 800000000000) 1 (IntervalRat.scale (745 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (23257572970 / 1000000000000) (23257583466 / 1000000000000), orderedInterval (-19464566232 / 1000000000000) (-19464555736 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (370117066781443 / 800000000000) 1 (IntervalRat.scale (745 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-37054825270 / 1000000000000) (-37054824529 / 1000000000000), orderedInterval (1766012500 / 1000000000000) (1766013241 / 1000000000000)))) (orderedInterval (2540947804 / 1000000000000) (2540949710 / 1000000000000))) = true
  rfl'

theorem compactCertificate501_chunkChecks1 :
    compactCertificate501.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate501.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate501_chunkChecks1_0
    compactCertificate501_chunkChecks1_1 compactCertificate501_chunkChecks1_2

theorem compactCertificate501_chunkChecks2_0 :
    compactCertificate501.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (745 / 2) 2 (IntervalRat.scale (745 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (22115660901 / 1000000000000) (22115663114 / 1000000000000), orderedInterval (-34957390664 / 1000000000000) (-34957388451 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (219505451237249 / 800000000000) 2 (IntervalRat.scale (745 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-46326946004 / 1000000000000) (-46326942498 / 1000000000000), orderedInterval (13275613670 / 1000000000000) (13275617175 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (70983552906017 / 160000000000) 2 (IntervalRat.scale (745 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-37680054668 / 1000000000000) (-37680054576 / 1000000000000), orderedInterval (-3853827951 / 1000000000000) (-3853827859 / 1000000000000)))) (orderedInterval (-5357571538 / 1000000000000) (-5357570599 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (64051143216643 / 800000000000) 2 (IntervalRat.scale (745 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-66019970196 / 1000000000000) (-66019862654 / 1000000000000), orderedInterval (60351761048 / 1000000000000) (60351868589 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (172050380218471 / 800000000000) 2 (IntervalRat.scale (745 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (43355588466 / 1000000000000) (43355678710 / 1000000000000), orderedInterval (-32970915985 / 1000000000000) (-32970825741 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (467150250858507 / 800000000000) 2 (IntervalRat.scale (745 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (12454345431 / 1000000000000) (12454345432 / 1000000000000), orderedInterval (30568871646 / 1000000000000) (30568871647 / 1000000000000)))) (orderedInterval (1626379420 / 1000000000000) (1626380649 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (344100760437091 / 800000000000) 2 (IntervalRat.scale (745 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-18877142703 / 1000000000000) (-18877142702 / 1000000000000), orderedInterval (-33500162035 / 1000000000000) (-33500162034 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (589622518018543 / 800000000000) 2 (IntervalRat.scale (745 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (13071216900 / 1000000000000) (13071216955 / 1000000000000), orderedInterval (-26332037868 / 1000000000000) (-26332037813 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (434313278111437 / 800000000000) 2 (IntervalRat.scale (745 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-6172326729 / 1000000000000) (-6172326728 / 1000000000000), orderedInterval (-33677383093 / 1000000000000) (-33677383092 / 1000000000000)))) (orderedInterval (1894074147 / 1000000000000) (1894074219 / 1000000000000))) = true
  rfl'

theorem compactCertificate501_chunkChecks2_1 :
    compactCertificate501.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (666348257294851 / 800000000000) 2 (IntervalRat.scale (745 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-25752386290 / 1000000000000) (-25752386258 / 1000000000000), orderedInterval (-10040547938 / 1000000000000) (-10040547906 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (384716345723179 / 800000000000) 2 (IntervalRat.scale (745 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-30944108802 / 1000000000000) (-30944108801 / 1000000000000), orderedInterval (-19106359356 / 1000000000000) (-19106359355 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (682685906612711 / 800000000000) 2 (IntervalRat.scale (745 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-9891351935 / 1000000000000) (-9891351930 / 1000000000000), orderedInterval (25465155745 / 1000000000000) (25465155751 / 1000000000000)))) (orderedInterval (-11706784791 / 1000000000000) (-11706784103 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (637853729644259 / 800000000000) 2 (IntervalRat.scale (745 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (3883432228 / 1000000000000) (3883432229 / 1000000000000), orderedInterval (27986338662 / 1000000000000) (27986338663 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (455202519032147 / 800000000000) 2 (IntervalRat.scale (745 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-30666873132 / 1000000000000) (-30666873129 / 1000000000000), orderedInterval (-13328802833 / 1000000000000) (-13328802830 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (516151140655413 / 800000000000) 2 (IntervalRat.scale (745 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-29207978815 / 1000000000000) (-29207922046 / 1000000000000), orderedInterval (11581747851 / 1000000000000) (11581804619 / 1000000000000)))) (orderedInterval (6652661622 / 1000000000000) (6652662605 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (430313009616997 / 800000000000) 2 (IntervalRat.scale (745 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-34207020621 / 1000000000000) (-34207020453 / 1000000000000), orderedInterval (-3632433401 / 1000000000000) (-3632433232 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (380194594080937 / 800000000000) 2 (IntervalRat.scale (745 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-36491371884 / 1000000000000) (-36491370731 / 1000000000000), orderedInterval (2857125544 / 1000000000000) (2857126697 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (110195212160763 / 160000000000) 2 (IntervalRat.scale (745 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-30319284087 / 1000000000000) (-30319283401 / 1000000000000), orderedInterval (-2234708146 / 1000000000000) (-2234707460 / 1000000000000)))) (orderedInterval (79273445 / 1000000000000) (79273694 / 1000000000000))) = true
  rfl'

theorem compactCertificate501_chunkChecks2_2 :
    compactCertificate501.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (304805756092961 / 800000000000) 2 (IntervalRat.scale (745 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-40715555535 / 1000000000000) (-40715554786 / 1000000000000), orderedInterval (3676776725 / 1000000000000) (3676777474 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (258387215071321 / 800000000000) 2 (IntervalRat.scale (745 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-8166010860 / 1000000000000) (-8166010859 / 1000000000000), orderedInterval (-43626504236 / 1000000000000) (-43626504235 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (161686721888563 / 800000000000) 2 (IntervalRat.scale (745 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (54230911397 / 1000000000000) (54230913339 / 1000000000000), orderedInterval (-14587274667 / 1000000000000) (-14587272725 / 1000000000000)))) (orderedInterval (-7681526612 / 1000000000000) (-7681526385 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (86955656777421 / 800000000000) 2 (IntervalRat.scale (745 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (35131138897 / 1000000000000) (35131142542 / 1000000000000), orderedInterval (-68152771394 / 1000000000000) (-68152767749 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (236101523435263 / 800000000000) 2 (IntervalRat.scale (745 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (26307700598 / 1000000000000) (26307700599 / 1000000000000), orderedInterval (38230894350 / 1000000000000) (38230894351 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (322376445310751 / 800000000000) 2 (IntervalRat.scale (745 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (39672998752 / 1000000000000) (39672999363 / 1000000000000), orderedInterval (-2471833701 / 1000000000000) (-2471833090 / 1000000000000)))) (orderedInterval (3988454266 / 1000000000000) (3988454367 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (136313278111437 / 800000000000) 2 (IntervalRat.scale (745 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (61074245037 / 1000000000000) (61074245068 / 1000000000000), orderedInterval (2297943577 / 1000000000000) (2297943607 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (554105907636077 / 800000000000) 2 (IntervalRat.scale (745 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (23257572970 / 1000000000000) (23257583466 / 1000000000000), orderedInterval (-19464566232 / 1000000000000) (-19464555736 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (370117066781443 / 800000000000) 2 (IntervalRat.scale (745 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-37054825270 / 1000000000000) (-37054824529 / 1000000000000), orderedInterval (1766012500 / 1000000000000) (1766013241 / 1000000000000)))) (orderedInterval (-4262919425 / 1000000000000) (-4262916037 / 1000000000000))) = true
  rfl'

theorem compactCertificate501_chunkChecks2 :
    compactCertificate501.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate501.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate501_chunkChecks2_0
    compactCertificate501_chunkChecks2_1 compactCertificate501_chunkChecks2_2

theorem compactCertificate501_chunkChecks3_0 :
    compactCertificate501.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (745 / 2) 3 (IntervalRat.scale (745 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (22115660901 / 1000000000000) (22115663114 / 1000000000000), orderedInterval (-34957390664 / 1000000000000) (-34957388451 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (219505451237249 / 800000000000) 3 (IntervalRat.scale (745 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-46326946004 / 1000000000000) (-46326942498 / 1000000000000), orderedInterval (13275613670 / 1000000000000) (13275617175 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (70983552906017 / 160000000000) 3 (IntervalRat.scale (745 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-37680054668 / 1000000000000) (-37680054576 / 1000000000000), orderedInterval (-3853827951 / 1000000000000) (-3853827859 / 1000000000000)))) (orderedInterval (14202782331 / 1000000000000) (14202783272 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (64051143216643 / 800000000000) 3 (IntervalRat.scale (745 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-66019970196 / 1000000000000) (-66019862654 / 1000000000000), orderedInterval (60351761048 / 1000000000000) (60351868589 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (172050380218471 / 800000000000) 3 (IntervalRat.scale (745 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (43355588466 / 1000000000000) (43355678710 / 1000000000000), orderedInterval (-32970915985 / 1000000000000) (-32970825741 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (467150250858507 / 800000000000) 3 (IntervalRat.scale (745 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (12454345431 / 1000000000000) (12454345432 / 1000000000000), orderedInterval (30568871646 / 1000000000000) (30568871647 / 1000000000000)))) (orderedInterval (8605346451 / 1000000000000) (8605347206 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (344100760437091 / 800000000000) 3 (IntervalRat.scale (745 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-18877142703 / 1000000000000) (-18877142702 / 1000000000000), orderedInterval (-33500162035 / 1000000000000) (-33500162034 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (589622518018543 / 800000000000) 3 (IntervalRat.scale (745 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (13071216900 / 1000000000000) (13071216955 / 1000000000000), orderedInterval (-26332037868 / 1000000000000) (-26332037813 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (434313278111437 / 800000000000) 3 (IntervalRat.scale (745 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-6172326729 / 1000000000000) (-6172326728 / 1000000000000), orderedInterval (-33677383093 / 1000000000000) (-33677383092 / 1000000000000)))) (orderedInterval (-3776561396 / 1000000000000) (-3776561265 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate501_chunkChecks3_1 :
    compactCertificate501.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (666348257294851 / 800000000000) 3 (IntervalRat.scale (745 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-25752386290 / 1000000000000) (-25752386258 / 1000000000000), orderedInterval (-10040547938 / 1000000000000) (-10040547906 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (384716345723179 / 800000000000) 3 (IntervalRat.scale (745 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-30944108802 / 1000000000000) (-30944108801 / 1000000000000), orderedInterval (-19106359356 / 1000000000000) (-19106359355 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (682685906612711 / 800000000000) 3 (IntervalRat.scale (745 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-9891351935 / 1000000000000) (-9891351930 / 1000000000000), orderedInterval (25465155745 / 1000000000000) (25465155751 / 1000000000000)))) (orderedInterval (-60392868145 / 1000000000000) (-60392866633 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (637853729644259 / 800000000000) 3 (IntervalRat.scale (745 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (3883432228 / 1000000000000) (3883432229 / 1000000000000), orderedInterval (27986338662 / 1000000000000) (27986338663 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (455202519032147 / 800000000000) 3 (IntervalRat.scale (745 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-30666873132 / 1000000000000) (-30666873129 / 1000000000000), orderedInterval (-13328802833 / 1000000000000) (-13328802830 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (516151140655413 / 800000000000) 3 (IntervalRat.scale (745 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-29207978815 / 1000000000000) (-29207922046 / 1000000000000), orderedInterval (11581747851 / 1000000000000) (11581804619 / 1000000000000)))) (orderedInterval (9733690204 / 1000000000000) (9733691902 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (430313009616997 / 800000000000) 3 (IntervalRat.scale (745 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-34207020621 / 1000000000000) (-34207020453 / 1000000000000), orderedInterval (-3632433401 / 1000000000000) (-3632433232 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (380194594080937 / 800000000000) 3 (IntervalRat.scale (745 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-36491371884 / 1000000000000) (-36491370731 / 1000000000000), orderedInterval (2857125544 / 1000000000000) (2857126697 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (110195212160763 / 160000000000) 3 (IntervalRat.scale (745 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-30319284087 / 1000000000000) (-30319283401 / 1000000000000), orderedInterval (-2234708146 / 1000000000000) (-2234707460 / 1000000000000)))) (orderedInterval (827267594 / 1000000000000) (827267967 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate501_chunkChecks3_2 :
    compactCertificate501.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (304805756092961 / 800000000000) 3 (IntervalRat.scale (745 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-40715555535 / 1000000000000) (-40715554786 / 1000000000000), orderedInterval (3676776725 / 1000000000000) (3676777474 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (258387215071321 / 800000000000) 3 (IntervalRat.scale (745 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-8166010860 / 1000000000000) (-8166010859 / 1000000000000), orderedInterval (-43626504236 / 1000000000000) (-43626504235 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (161686721888563 / 800000000000) 3 (IntervalRat.scale (745 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (54230911397 / 1000000000000) (54230913339 / 1000000000000), orderedInterval (-14587274667 / 1000000000000) (-14587272725 / 1000000000000)))) (orderedInterval (-884069781 / 1000000000000) (-884069562 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (86955656777421 / 800000000000) 3 (IntervalRat.scale (745 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (35131138897 / 1000000000000) (35131142542 / 1000000000000), orderedInterval (-68152771394 / 1000000000000) (-68152767749 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (236101523435263 / 800000000000) 3 (IntervalRat.scale (745 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (26307700598 / 1000000000000) (26307700599 / 1000000000000), orderedInterval (38230894350 / 1000000000000) (38230894351 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (322376445310751 / 800000000000) 3 (IntervalRat.scale (745 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (39672998752 / 1000000000000) (39672999363 / 1000000000000), orderedInterval (-2471833701 / 1000000000000) (-2471833090 / 1000000000000)))) (orderedInterval (149548645 / 1000000000000) (149548748 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (136313278111437 / 800000000000) 3 (IntervalRat.scale (745 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (61074245037 / 1000000000000) (61074245068 / 1000000000000), orderedInterval (2297943577 / 1000000000000) (2297943607 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (554105907636077 / 800000000000) 3 (IntervalRat.scale (745 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (23257572970 / 1000000000000) (23257583466 / 1000000000000), orderedInterval (-19464566232 / 1000000000000) (-19464555736 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (370117066781443 / 800000000000) 3 (IntervalRat.scale (745 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-37054825270 / 1000000000000) (-37054824529 / 1000000000000), orderedInterval (1766012500 / 1000000000000) (1766013241 / 1000000000000)))) (orderedInterval (-9541140326 / 1000000000000) (-9541134229 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate501_chunkChecks3 :
    compactCertificate501.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate501.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate501_chunkChecks3_0
    compactCertificate501_chunkChecks3_1 compactCertificate501_chunkChecks3_2

theorem compactCertificate501_chunkChecks4_0 :
    compactCertificate501.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (745 / 2) 4 (IntervalRat.scale (745 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (22115660901 / 1000000000000) (22115663114 / 1000000000000), orderedInterval (-34957390664 / 1000000000000) (-34957388451 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (219505451237249 / 800000000000) 4 (IntervalRat.scale (745 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-46326946004 / 1000000000000) (-46326942498 / 1000000000000), orderedInterval (13275613670 / 1000000000000) (13275617175 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (70983552906017 / 160000000000) 4 (IntervalRat.scale (745 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-37680054668 / 1000000000000) (-37680054576 / 1000000000000), orderedInterval (-3853827951 / 1000000000000) (-3853827859 / 1000000000000)))) (orderedInterval (4113565434 / 1000000000000) (4113566382 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (64051143216643 / 800000000000) 4 (IntervalRat.scale (745 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-66019970196 / 1000000000000) (-66019862654 / 1000000000000), orderedInterval (60351761048 / 1000000000000) (60351868589 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (172050380218471 / 800000000000) 4 (IntervalRat.scale (745 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (43355588466 / 1000000000000) (43355678710 / 1000000000000), orderedInterval (-32970915985 / 1000000000000) (-32970825741 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (467150250858507 / 800000000000) 4 (IntervalRat.scale (745 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (12454345431 / 1000000000000) (12454345432 / 1000000000000), orderedInterval (30568871646 / 1000000000000) (30568871647 / 1000000000000)))) (orderedInterval (-5215508464 / 1000000000000) (-5215507930 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (344100760437091 / 800000000000) 4 (IntervalRat.scale (745 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-18877142703 / 1000000000000) (-18877142702 / 1000000000000), orderedInterval (-33500162035 / 1000000000000) (-33500162034 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (589622518018543 / 800000000000) 4 (IntervalRat.scale (745 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (13071216900 / 1000000000000) (13071216955 / 1000000000000), orderedInterval (-26332037868 / 1000000000000) (-26332037813 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (434313278111437 / 800000000000) 4 (IntervalRat.scale (745 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-6172326729 / 1000000000000) (-6172326728 / 1000000000000), orderedInterval (-33677383093 / 1000000000000) (-33677383092 / 1000000000000)))) (orderedInterval (-6831740441 / 1000000000000) (-6831740197 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate501_chunkChecks4_1 :
    compactCertificate501.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (666348257294851 / 800000000000) 4 (IntervalRat.scale (745 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-25752386290 / 1000000000000) (-25752386258 / 1000000000000), orderedInterval (-10040547938 / 1000000000000) (-10040547906 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (384716345723179 / 800000000000) 4 (IntervalRat.scale (745 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-30944108802 / 1000000000000) (-30944108801 / 1000000000000), orderedInterval (-19106359356 / 1000000000000) (-19106359355 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (682685906612711 / 800000000000) 4 (IntervalRat.scale (745 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-9891351935 / 1000000000000) (-9891351930 / 1000000000000), orderedInterval (25465155745 / 1000000000000) (25465155751 / 1000000000000)))) (orderedInterval (69623490516 / 1000000000000) (69623493870 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (637853729644259 / 800000000000) 4 (IntervalRat.scale (745 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (3883432228 / 1000000000000) (3883432229 / 1000000000000), orderedInterval (27986338662 / 1000000000000) (27986338663 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (455202519032147 / 800000000000) 4 (IntervalRat.scale (745 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-30666873132 / 1000000000000) (-30666873129 / 1000000000000), orderedInterval (-13328802833 / 1000000000000) (-13328802830 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (516151140655413 / 800000000000) 4 (IntervalRat.scale (745 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-29207978815 / 1000000000000) (-29207922046 / 1000000000000), orderedInterval (11581747851 / 1000000000000) (11581804619 / 1000000000000)))) (orderedInterval (-15982124974 / 1000000000000) (-15982122028 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (430313009616997 / 800000000000) 4 (IntervalRat.scale (745 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-34207020621 / 1000000000000) (-34207020453 / 1000000000000), orderedInterval (-3632433401 / 1000000000000) (-3632433232 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (380194594080937 / 800000000000) 4 (IntervalRat.scale (745 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-36491371884 / 1000000000000) (-36491370731 / 1000000000000), orderedInterval (2857125544 / 1000000000000) (2857126697 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (110195212160763 / 160000000000) 4 (IntervalRat.scale (745 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-30319284087 / 1000000000000) (-30319283401 / 1000000000000), orderedInterval (-2234708146 / 1000000000000) (-2234707460 / 1000000000000)))) (orderedInterval (-5260818479 / 1000000000000) (-5260817901 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate501_chunkChecks4_2 :
    compactCertificate501.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (304805756092961 / 800000000000) 4 (IntervalRat.scale (745 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-40715555535 / 1000000000000) (-40715554786 / 1000000000000), orderedInterval (3676776725 / 1000000000000) (3676777474 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (258387215071321 / 800000000000) 4 (IntervalRat.scale (745 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-8166010860 / 1000000000000) (-8166010859 / 1000000000000), orderedInterval (-43626504236 / 1000000000000) (-43626504235 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (161686721888563 / 800000000000) 4 (IntervalRat.scale (745 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (54230911397 / 1000000000000) (54230913339 / 1000000000000), orderedInterval (-14587274667 / 1000000000000) (-14587272725 / 1000000000000)))) (orderedInterval (7544446726 / 1000000000000) (7544446942 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (86955656777421 / 800000000000) 4 (IntervalRat.scale (745 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (35131138897 / 1000000000000) (35131142542 / 1000000000000), orderedInterval (-68152771394 / 1000000000000) (-68152767749 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (236101523435263 / 800000000000) 4 (IntervalRat.scale (745 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (26307700598 / 1000000000000) (26307700599 / 1000000000000), orderedInterval (38230894350 / 1000000000000) (38230894351 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (322376445310751 / 800000000000) 4 (IntervalRat.scale (745 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (39672998752 / 1000000000000) (39672999363 / 1000000000000), orderedInterval (-2471833701 / 1000000000000) (-2471833090 / 1000000000000)))) (orderedInterval (-4404856873 / 1000000000000) (-4404856764 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (136313278111437 / 800000000000) 4 (IntervalRat.scale (745 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (61074245037 / 1000000000000) (61074245068 / 1000000000000), orderedInterval (2297943577 / 1000000000000) (2297943607 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (554105907636077 / 800000000000) 4 (IntervalRat.scale (745 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (23257572970 / 1000000000000) (23257583466 / 1000000000000), orderedInterval (-19464566232 / 1000000000000) (-19464555736 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (370117066781443 / 800000000000) 4 (IntervalRat.scale (745 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-37054825270 / 1000000000000) (-37054824529 / 1000000000000), orderedInterval (1766012500 / 1000000000000) (1766013241 / 1000000000000)))) (orderedInterval (-6020111609 / 1000000000000) (-6020100505 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate501_chunkChecks4 :
    compactCertificate501.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate501.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate501_chunkChecks4_0
    compactCertificate501_chunkChecks4_1 compactCertificate501_chunkChecks4_2

theorem compactCertificate501_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate501.chunkCheck r b = true :=
  compactCertificate501.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate501_chunkChecks0
    · exact compactCertificate501_chunkChecks1
    · exact compactCertificate501_chunkChecks2
    · exact compactCertificate501_chunkChecks3
    · exact compactCertificate501_chunkChecks4)

theorem compactCertificate501_coefficient0 :
    compactCertificate501.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate501_coefficient1 :
    compactCertificate501.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate501_coefficient2 :
    compactCertificate501.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate501_coefficient3 :
    compactCertificate501.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate501_coefficient4 :
    compactCertificate501.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate501_coefficients : ∀ r : Fin 5,
    compactCertificate501.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate501_coefficient0
  · exact compactCertificate501_coefficient1
  · exact compactCertificate501_coefficient2
  · exact compactCertificate501_coefficient3
  · exact compactCertificate501_coefficient4

theorem compactCertificate501_lower : (1 : ℚ) ≤ compactCertificate501.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate501, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate501_proves {t : ℝ} (ht : t ∈ compactCertificate501.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate501.proves compactCertificate501_states compactCertificate501_chunks
    compactCertificate501_coefficients compactCertificate501_lower ht

end Erdos232
