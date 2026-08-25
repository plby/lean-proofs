/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate335 : CompactCertificate where
  left := 207
  right := 208
  center := 415 / 2
  grid := fun i =>
    match i.val with
    | 0 => 66
    | 1 => 49
    | 2 => 79
    | 3 => 14
    | 4 => 38
    | 5 => 104
    | 6 => 76
    | 7 => 131
    | 8 => 96
    | 9 => 148
    | 10 => 85
    | 11 => 151
    | 12 => 141
    | 13 => 101
    | 14 => 114
    | 15 => 95
    | 16 => 84
    | 17 => 122
    | 18 => 68
    | 19 => 57
    | 20 => 36
    | 21 => 19
    | 22 => 52
    | 23 => 71
    | 24 => 30
    | 25 => 123
    | _ => 82
  point := fun i =>
    match i.val with
    | 0 => 415 / 2
    | 1 => 122274848675783 / 800000000000
    | 2 => 39541173766439 / 160000000000
    | 3 => 35679495885781 / 800000000000
    | 4 => 95840144685457 / 800000000000
    | 5 => 260224636384269 / 800000000000
    | 6 => 191680289370997 / 800000000000
    | 7 => 328447442923081 / 800000000000
    | 8 => 241932899887579 / 800000000000
    | 9 => 371187284264917 / 800000000000
    | 10 => 214305078490093 / 800000000000
    | 11 => 380288122475537 / 800000000000
    | 12 => 355314493694453 / 800000000000
    | 13 => 253569188454149 / 800000000000
    | 14 => 287520434056371 / 800000000000
    | 15 => 239704562404099 / 800000000000
    | 16 => 211786250394079 / 800000000000
    | 17 => 61383910129821 / 160000000000
    | 18 => 169791125877287 / 800000000000
    | 19 => 143933817791407 / 800000000000
    | 20 => 90067100112421 / 800000000000
    | 21 => 48438385990107 / 800000000000
    | 22 => 131519640571321 / 800000000000
    | 23 => 179578825240217 / 800000000000
    | 24 => 75932899887579 / 800000000000
    | 25 => 308663022374459 / 800000000000
    | _ => 206172594247381 / 800000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (44720106030 / 1000000000000) (44720106031 / 1000000000000), orderedInterval (32574905048 / 1000000000000) (32574905049 / 1000000000000))
    | 1 => (orderedInterval (19681647839 / 1000000000000) (19681648237 / 1000000000000), orderedInterval (-61528383769 / 1000000000000) (-61528383371 / 1000000000000))
    | 2 => (orderedInterval (13468904686 / 1000000000000) (13468904808 / 1000000000000), orderedInterval (-48962114723 / 1000000000000) (-48962114601 / 1000000000000))
    | 3 => (orderedInterval (117725816780 / 1000000000000) (117725816782 / 1000000000000), orderedInterval (19026735924 / 1000000000000) (19026735926 / 1000000000000))
    | 4 => (orderedInterval (68048321156 / 1000000000000) (68048321157 / 1000000000000), orderedInterval (25858014556 / 1000000000000) (25858014557 / 1000000000000))
    | 5 => (orderedInterval (-27117950556 / 1000000000000) (-27117942667 / 1000000000000), orderedInterval (34995315718 / 1000000000000) (34995323607 / 1000000000000))
    | 6 => (orderedInterval (51472628453 / 1000000000000) (51472628644 / 1000000000000), orderedInterval (-2858682404 / 1000000000000) (-2858682213 / 1000000000000))
    | 7 => (orderedInterval (7986743558 / 1000000000000) (7986743572 / 1000000000000), orderedInterval (-38569146436 / 1000000000000) (-38569146422 / 1000000000000))
    | 8 => (orderedInterval (45849349798 / 1000000000000) (45849350034 / 1000000000000), orderedInterval (-1792227701 / 1000000000000) (-1792227465 / 1000000000000))
    | 9 => (orderedInterval (-6867481701 / 1000000000000) (-6867481694 / 1000000000000), orderedInterval (36406724850 / 1000000000000) (36406724857 / 1000000000000))
    | 10 => (orderedInterval (-48661269252 / 1000000000000) (-48661269000 / 1000000000000), orderedInterval (3019278956 / 1000000000000) (3019279209 / 1000000000000))
    | 11 => (orderedInterval (-35909067904 / 1000000000000) (-35909063636 / 1000000000000), orderedInterval (7092909937 / 1000000000000) (7092914205 / 1000000000000))
    | 12 => (orderedInterval (-34975392855 / 1000000000000) (-34975366613 / 1000000000000), orderedInterval (14533788212 / 1000000000000) (14533814453 / 1000000000000))
    | 13 => (orderedInterval (-19317089130 / 1000000000000) (-19317089129 / 1000000000000), orderedInterval (-40409111496 / 1000000000000) (-40409111495 / 1000000000000))
    | 14 => (orderedInterval (37461792566 / 1000000000000) (37461829514 / 1000000000000), orderedInterval (-19234144338 / 1000000000000) (-19234107390 / 1000000000000))
    | 15 => (orderedInterval (-42569871766 / 1000000000000) (-42569858588 / 1000000000000), orderedInterval (17748299285 / 1000000000000) (17748312463 / 1000000000000))
    | 16 => (orderedInterval (48969069007 / 1000000000000) (48969069233 / 1000000000000), orderedInterval (-2698130901 / 1000000000000) (-2698130676 / 1000000000000))
    | 17 => (orderedInterval (37349758905 / 1000000000000) (37349758906 / 1000000000000), orderedInterval (16210887160 / 1000000000000) (16210887161 / 1000000000000))
    | 18 => (orderedInterval (-31131223435 / 1000000000000) (-31131215393 / 1000000000000), orderedInterval (45133221375 / 1000000000000) (45133229417 / 1000000000000))
    | 19 => (orderedInterval (-59375895842 / 1000000000000) (-59375895703 / 1000000000000), orderedInterval (3755577921 / 1000000000000) (3755578060 / 1000000000000))
    | 20 => (orderedInterval (20117338789 / 1000000000000) (20117338790 / 1000000000000), orderedInterval (72367314211 / 1000000000000) (72367314212 / 1000000000000))
    | 21 => (orderedInterval (-102284542674 / 1000000000000) (-102284542605 / 1000000000000), orderedInterval (8043176631 / 1000000000000) (8043176701 / 1000000000000))
    | 22 => (orderedInterval (60285033583 / 1000000000000) (60285034979 / 1000000000000), orderedInterval (-15613596273 / 1000000000000) (-15613594878 / 1000000000000))
    | 23 => (orderedInterval (-42889642552 / 1000000000000) (-42889559230 / 1000000000000), orderedInterval (31663465885 / 1000000000000) (31663549207 / 1000000000000))
    | 24 => (orderedInterval (81323746822 / 1000000000000) (81323746827 / 1000000000000), orderedInterval (9243235376 / 1000000000000) (9243235381 / 1000000000000))
    | 25 => (orderedInterval (-7988598492 / 1000000000000) (-7988598491 / 1000000000000), orderedInterval (-39816642170 / 1000000000000) (-39816642169 / 1000000000000))
    | _ => (orderedInterval (38623428550 / 1000000000000) (38623428551 / 1000000000000), orderedInterval (31205570269 / 1000000000000) (31205570270 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (18699249963 / 1000000000000) (18699249989 / 1000000000000)
      | 1 => orderedInterval (3135126169 / 1000000000000) (3135126756 / 1000000000000)
      | 2 => orderedInterval (861745191 / 1000000000000) (861745209 / 1000000000000)
      | 3 => orderedInterval (-7489816659 / 1000000000000) (-7489815950 / 1000000000000)
      | 4 => orderedInterval (-1384844458 / 1000000000000) (-1384843771 / 1000000000000)
      | 5 => orderedInterval (-2337618590 / 1000000000000) (-2337618404 / 1000000000000)
      | 6 => orderedInterval (8993244526 / 1000000000000) (8993245872 / 1000000000000)
      | 7 => orderedInterval (3808025119 / 1000000000000) (3808031563 / 1000000000000)
      | _ => orderedInterval (-6106247456 / 1000000000000) (-6106247398 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (9067320670 / 1000000000000) (9067320699 / 1000000000000)
      | 1 => orderedInterval (-3399208618 / 1000000000000) (-3399207710 / 1000000000000)
      | 2 => orderedInterval (2290666549 / 1000000000000) (2290666579 / 1000000000000)
      | 3 => orderedInterval (-11866498514 / 1000000000000) (-11866496926 / 1000000000000)
      | 4 => orderedInterval (-6230002633 / 1000000000000) (-6230001254 / 1000000000000)
      | 5 => orderedInterval (1260358711 / 1000000000000) (1260358977 / 1000000000000)
      | 6 => orderedInterval (-6287314264 / 1000000000000) (-6287312893 / 1000000000000)
      | 7 => orderedInterval (-2387850279 / 1000000000000) (-2387843322 / 1000000000000)
      | _ => orderedInterval (-1219796604 / 1000000000000) (-1219796522 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-18989811808 / 1000000000000) (-18989811776 / 1000000000000)
      | 1 => orderedInterval (-5490241395 / 1000000000000) (-5490239973 / 1000000000000)
      | 2 => orderedInterval (-1400325471 / 1000000000000) (-1400325421 / 1000000000000)
      | 3 => orderedInterval (26755188296 / 1000000000000) (26755191891 / 1000000000000)
      | 4 => orderedInterval (1968175143 / 1000000000000) (1968177949 / 1000000000000)
      | 5 => orderedInterval (2311267710 / 1000000000000) (2311268093 / 1000000000000)
      | 6 => orderedInterval (-7896699705 / 1000000000000) (-7896698301 / 1000000000000)
      | 7 => orderedInterval (-3137554133 / 1000000000000) (-3137546583 / 1000000000000)
      | _ => orderedInterval (8833668753 / 1000000000000) (8833668874 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-7736765252 / 1000000000000) (-7736765216 / 1000000000000)
      | 1 => orderedInterval (9430521649 / 1000000000000) (9430523876 / 1000000000000)
      | 2 => orderedInterval (-9073870849 / 1000000000000) (-9073870761 / 1000000000000)
      | 3 => orderedInterval (59592646183 / 1000000000000) (59592654349 / 1000000000000)
      | 4 => orderedInterval (15677251364 / 1000000000000) (15677257108 / 1000000000000)
      | 5 => orderedInterval (-3572251400 / 1000000000000) (-3572250847 / 1000000000000)
      | 6 => orderedInterval (7522442909 / 1000000000000) (7522444342 / 1000000000000)
      | 7 => orderedInterval (2914782213 / 1000000000000) (2914790372 / 1000000000000)
      | _ => orderedInterval (-9667121940 / 1000000000000) (-9667121755 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (19443893822 / 1000000000000) (19443893864 / 1000000000000)
      | 1 => orderedInterval (11824225804 / 1000000000000) (11824229303 / 1000000000000)
      | 2 => orderedInterval (1311395309 / 1000000000000) (1311395464 / 1000000000000)
      | 3 => orderedInterval (-120682816753 / 1000000000000) (-120682798110 / 1000000000000)
      | 4 => orderedInterval (1451056106 / 1000000000000) (1451067983 / 1000000000000)
      | 5 => orderedInterval (1647799236 / 1000000000000) (1647800042 / 1000000000000)
      | 6 => orderedInterval (7331777711 / 1000000000000) (7331779181 / 1000000000000)
      | 7 => orderedInterval (3948445698 / 1000000000000) (3948454558 / 1000000000000)
      | _ => orderedInterval (-9355700648 / 1000000000000) (-9355700351 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (18178863805 / 1000000000000) (18178873866 / 1000000000000)
    | 1 => orderedInterval (-18772324982 / 1000000000000) (-18772312372 / 1000000000000)
    | 2 => orderedInterval (2953667390 / 1000000000000) (2953684753 / 1000000000000)
    | 3 => orderedInterval (65087634877 / 1000000000000) (65087661468 / 1000000000000)
    | _ => orderedInterval (-83079923715 / 1000000000000) (-83079878066 / 1000000000000)

theorem compactCertificate335_stateChecks0 :
    compactCertificate335.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (415 / 2)) (orderedInterval (44720106030 / 1000000000000) (44720106031 / 1000000000000), orderedInterval (32574905048 / 1000000000000) (32574905049 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 49 12 (122274848675783 / 800000000000)) (orderedInterval (19681647839 / 1000000000000) (19681648237 / 1000000000000), orderedInterval (-61528383769 / 1000000000000) (-61528383371 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 79 12 (39541173766439 / 160000000000)) (orderedInterval (13468904686 / 1000000000000) (13468904808 / 1000000000000), orderedInterval (-48962114723 / 1000000000000) (-48962114601 / 1000000000000))) = true
  rfl'

theorem compactCertificate335_stateChecks1 :
    compactCertificate335.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 14 12 (35679495885781 / 800000000000)) (orderedInterval (117725816780 / 1000000000000) (117725816782 / 1000000000000), orderedInterval (19026735924 / 1000000000000) (19026735926 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (95840144685457 / 800000000000)) (orderedInterval (68048321156 / 1000000000000) (68048321157 / 1000000000000), orderedInterval (25858014556 / 1000000000000) (25858014557 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 104 12 (260224636384269 / 800000000000)) (orderedInterval (-27117950556 / 1000000000000) (-27117942667 / 1000000000000), orderedInterval (34995315718 / 1000000000000) (34995323607 / 1000000000000))) = true
  rfl'

theorem compactCertificate335_stateChecks2 :
    compactCertificate335.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 76 12 (191680289370997 / 800000000000)) (orderedInterval (51472628453 / 1000000000000) (51472628644 / 1000000000000), orderedInterval (-2858682404 / 1000000000000) (-2858682213 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 131 12 (328447442923081 / 800000000000)) (orderedInterval (7986743558 / 1000000000000) (7986743572 / 1000000000000), orderedInterval (-38569146436 / 1000000000000) (-38569146422 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 96 12 (241932899887579 / 800000000000)) (orderedInterval (45849349798 / 1000000000000) (45849350034 / 1000000000000), orderedInterval (-1792227701 / 1000000000000) (-1792227465 / 1000000000000))) = true
  rfl'

theorem compactCertificate335_stateChecks3 :
    compactCertificate335.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 148 12 (371187284264917 / 800000000000)) (orderedInterval (-6867481701 / 1000000000000) (-6867481694 / 1000000000000), orderedInterval (36406724850 / 1000000000000) (36406724857 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 85 12 (214305078490093 / 800000000000)) (orderedInterval (-48661269252 / 1000000000000) (-48661269000 / 1000000000000), orderedInterval (3019278956 / 1000000000000) (3019279209 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 151 12 (380288122475537 / 800000000000)) (orderedInterval (-35909067904 / 1000000000000) (-35909063636 / 1000000000000), orderedInterval (7092909937 / 1000000000000) (7092914205 / 1000000000000))) = true
  rfl'

theorem compactCertificate335_stateChecks4 :
    compactCertificate335.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 141 12 (355314493694453 / 800000000000)) (orderedInterval (-34975392855 / 1000000000000) (-34975366613 / 1000000000000), orderedInterval (14533788212 / 1000000000000) (14533814453 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 101 12 (253569188454149 / 800000000000)) (orderedInterval (-19317089130 / 1000000000000) (-19317089129 / 1000000000000), orderedInterval (-40409111496 / 1000000000000) (-40409111495 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 114 12 (287520434056371 / 800000000000)) (orderedInterval (37461792566 / 1000000000000) (37461829514 / 1000000000000), orderedInterval (-19234144338 / 1000000000000) (-19234107390 / 1000000000000))) = true
  rfl'

theorem compactCertificate335_stateChecks5 :
    compactCertificate335.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 95 12 (239704562404099 / 800000000000)) (orderedInterval (-42569871766 / 1000000000000) (-42569858588 / 1000000000000), orderedInterval (17748299285 / 1000000000000) (17748312463 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 84 12 (211786250394079 / 800000000000)) (orderedInterval (48969069007 / 1000000000000) (48969069233 / 1000000000000), orderedInterval (-2698130901 / 1000000000000) (-2698130676 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 122 12 (61383910129821 / 160000000000)) (orderedInterval (37349758905 / 1000000000000) (37349758906 / 1000000000000), orderedInterval (16210887160 / 1000000000000) (16210887161 / 1000000000000))) = true
  rfl'

theorem compactCertificate335_stateChecks6 :
    compactCertificate335.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (169791125877287 / 800000000000)) (orderedInterval (-31131223435 / 1000000000000) (-31131215393 / 1000000000000), orderedInterval (45133221375 / 1000000000000) (45133229417 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 57 12 (143933817791407 / 800000000000)) (orderedInterval (-59375895842 / 1000000000000) (-59375895703 / 1000000000000), orderedInterval (3755577921 / 1000000000000) (3755578060 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 36 12 (90067100112421 / 800000000000)) (orderedInterval (20117338789 / 1000000000000) (20117338790 / 1000000000000), orderedInterval (72367314211 / 1000000000000) (72367314212 / 1000000000000))) = true
  rfl'

theorem compactCertificate335_stateChecks7 :
    compactCertificate335.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 19 12 (48438385990107 / 800000000000)) (orderedInterval (-102284542674 / 1000000000000) (-102284542605 / 1000000000000), orderedInterval (8043176631 / 1000000000000) (8043176701 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 52 12 (131519640571321 / 800000000000)) (orderedInterval (60285033583 / 1000000000000) (60285034979 / 1000000000000), orderedInterval (-15613596273 / 1000000000000) (-15613594878 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (179578825240217 / 800000000000)) (orderedInterval (-42889642552 / 1000000000000) (-42889559230 / 1000000000000), orderedInterval (31663465885 / 1000000000000) (31663549207 / 1000000000000))) = true
  rfl'

theorem compactCertificate335_stateChecks8 :
    compactCertificate335.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (75932899887579 / 800000000000)) (orderedInterval (81323746822 / 1000000000000) (81323746827 / 1000000000000), orderedInterval (9243235376 / 1000000000000) (9243235381 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 123 12 (308663022374459 / 800000000000)) (orderedInterval (-7988598492 / 1000000000000) (-7988598491 / 1000000000000), orderedInterval (-39816642170 / 1000000000000) (-39816642169 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 82 12 (206172594247381 / 800000000000)) (orderedInterval (38623428550 / 1000000000000) (38623428551 / 1000000000000), orderedInterval (31205570269 / 1000000000000) (31205570270 / 1000000000000))) = true
  rfl'

theorem compactCertificate335_states : ∀ j,
    BesselStateValid (compactCertificate335.point j) (compactCertificate335.state j) :=
  compactCertificate335.statesValid_of_checks3 compactCertificate335_stateChecks0
    compactCertificate335_stateChecks1 compactCertificate335_stateChecks2
    compactCertificate335_stateChecks3 compactCertificate335_stateChecks4
    compactCertificate335_stateChecks5 compactCertificate335_stateChecks6
    compactCertificate335_stateChecks7 compactCertificate335_stateChecks8

theorem compactCertificate335_chunkChecks0_0 :
    compactCertificate335.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (415 / 2) 0 (IntervalRat.scale (415 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (44720106030 / 1000000000000) (44720106031 / 1000000000000), orderedInterval (32574905048 / 1000000000000) (32574905049 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (122274848675783 / 800000000000) 0 (IntervalRat.scale (415 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (19681647839 / 1000000000000) (19681648237 / 1000000000000), orderedInterval (-61528383769 / 1000000000000) (-61528383371 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (39541173766439 / 160000000000) 0 (IntervalRat.scale (415 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (13468904686 / 1000000000000) (13468904808 / 1000000000000), orderedInterval (-48962114723 / 1000000000000) (-48962114601 / 1000000000000)))) (orderedInterval (18699249963 / 1000000000000) (18699249989 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (35679495885781 / 800000000000) 0 (IntervalRat.scale (415 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (117725816780 / 1000000000000) (117725816782 / 1000000000000), orderedInterval (19026735924 / 1000000000000) (19026735926 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (95840144685457 / 800000000000) 0 (IntervalRat.scale (415 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (68048321156 / 1000000000000) (68048321157 / 1000000000000), orderedInterval (25858014556 / 1000000000000) (25858014557 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (260224636384269 / 800000000000) 0 (IntervalRat.scale (415 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-27117950556 / 1000000000000) (-27117942667 / 1000000000000), orderedInterval (34995315718 / 1000000000000) (34995323607 / 1000000000000)))) (orderedInterval (3135126169 / 1000000000000) (3135126756 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (191680289370997 / 800000000000) 0 (IntervalRat.scale (415 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (51472628453 / 1000000000000) (51472628644 / 1000000000000), orderedInterval (-2858682404 / 1000000000000) (-2858682213 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (328447442923081 / 800000000000) 0 (IntervalRat.scale (415 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (7986743558 / 1000000000000) (7986743572 / 1000000000000), orderedInterval (-38569146436 / 1000000000000) (-38569146422 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (241932899887579 / 800000000000) 0 (IntervalRat.scale (415 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (45849349798 / 1000000000000) (45849350034 / 1000000000000), orderedInterval (-1792227701 / 1000000000000) (-1792227465 / 1000000000000)))) (orderedInterval (861745191 / 1000000000000) (861745209 / 1000000000000))) = true
  rfl'

theorem compactCertificate335_chunkChecks0_1 :
    compactCertificate335.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (371187284264917 / 800000000000) 0 (IntervalRat.scale (415 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-6867481701 / 1000000000000) (-6867481694 / 1000000000000), orderedInterval (36406724850 / 1000000000000) (36406724857 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (214305078490093 / 800000000000) 0 (IntervalRat.scale (415 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-48661269252 / 1000000000000) (-48661269000 / 1000000000000), orderedInterval (3019278956 / 1000000000000) (3019279209 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (380288122475537 / 800000000000) 0 (IntervalRat.scale (415 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-35909067904 / 1000000000000) (-35909063636 / 1000000000000), orderedInterval (7092909937 / 1000000000000) (7092914205 / 1000000000000)))) (orderedInterval (-7489816659 / 1000000000000) (-7489815950 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (355314493694453 / 800000000000) 0 (IntervalRat.scale (415 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-34975392855 / 1000000000000) (-34975366613 / 1000000000000), orderedInterval (14533788212 / 1000000000000) (14533814453 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (253569188454149 / 800000000000) 0 (IntervalRat.scale (415 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-19317089130 / 1000000000000) (-19317089129 / 1000000000000), orderedInterval (-40409111496 / 1000000000000) (-40409111495 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (287520434056371 / 800000000000) 0 (IntervalRat.scale (415 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (37461792566 / 1000000000000) (37461829514 / 1000000000000), orderedInterval (-19234144338 / 1000000000000) (-19234107390 / 1000000000000)))) (orderedInterval (-1384844458 / 1000000000000) (-1384843771 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (239704562404099 / 800000000000) 0 (IntervalRat.scale (415 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-42569871766 / 1000000000000) (-42569858588 / 1000000000000), orderedInterval (17748299285 / 1000000000000) (17748312463 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (211786250394079 / 800000000000) 0 (IntervalRat.scale (415 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (48969069007 / 1000000000000) (48969069233 / 1000000000000), orderedInterval (-2698130901 / 1000000000000) (-2698130676 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (61383910129821 / 160000000000) 0 (IntervalRat.scale (415 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (37349758905 / 1000000000000) (37349758906 / 1000000000000), orderedInterval (16210887160 / 1000000000000) (16210887161 / 1000000000000)))) (orderedInterval (-2337618590 / 1000000000000) (-2337618404 / 1000000000000))) = true
  rfl'

theorem compactCertificate335_chunkChecks0_2 :
    compactCertificate335.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (169791125877287 / 800000000000) 0 (IntervalRat.scale (415 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-31131223435 / 1000000000000) (-31131215393 / 1000000000000), orderedInterval (45133221375 / 1000000000000) (45133229417 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (143933817791407 / 800000000000) 0 (IntervalRat.scale (415 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-59375895842 / 1000000000000) (-59375895703 / 1000000000000), orderedInterval (3755577921 / 1000000000000) (3755578060 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (90067100112421 / 800000000000) 0 (IntervalRat.scale (415 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (20117338789 / 1000000000000) (20117338790 / 1000000000000), orderedInterval (72367314211 / 1000000000000) (72367314212 / 1000000000000)))) (orderedInterval (8993244526 / 1000000000000) (8993245872 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (48438385990107 / 800000000000) 0 (IntervalRat.scale (415 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-102284542674 / 1000000000000) (-102284542605 / 1000000000000), orderedInterval (8043176631 / 1000000000000) (8043176701 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (131519640571321 / 800000000000) 0 (IntervalRat.scale (415 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (60285033583 / 1000000000000) (60285034979 / 1000000000000), orderedInterval (-15613596273 / 1000000000000) (-15613594878 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (179578825240217 / 800000000000) 0 (IntervalRat.scale (415 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-42889642552 / 1000000000000) (-42889559230 / 1000000000000), orderedInterval (31663465885 / 1000000000000) (31663549207 / 1000000000000)))) (orderedInterval (3808025119 / 1000000000000) (3808031563 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (75932899887579 / 800000000000) 0 (IntervalRat.scale (415 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (81323746822 / 1000000000000) (81323746827 / 1000000000000), orderedInterval (9243235376 / 1000000000000) (9243235381 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (308663022374459 / 800000000000) 0 (IntervalRat.scale (415 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-7988598492 / 1000000000000) (-7988598491 / 1000000000000), orderedInterval (-39816642170 / 1000000000000) (-39816642169 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (206172594247381 / 800000000000) 0 (IntervalRat.scale (415 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (38623428550 / 1000000000000) (38623428551 / 1000000000000), orderedInterval (31205570269 / 1000000000000) (31205570270 / 1000000000000)))) (orderedInterval (-6106247456 / 1000000000000) (-6106247398 / 1000000000000))) = true
  rfl'

theorem compactCertificate335_chunkChecks0 :
    compactCertificate335.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate335.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate335_chunkChecks0_0
    compactCertificate335_chunkChecks0_1 compactCertificate335_chunkChecks0_2

theorem compactCertificate335_chunkChecks1_0 :
    compactCertificate335.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (415 / 2) 1 (IntervalRat.scale (415 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (44720106030 / 1000000000000) (44720106031 / 1000000000000), orderedInterval (32574905048 / 1000000000000) (32574905049 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (122274848675783 / 800000000000) 1 (IntervalRat.scale (415 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (19681647839 / 1000000000000) (19681648237 / 1000000000000), orderedInterval (-61528383769 / 1000000000000) (-61528383371 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (39541173766439 / 160000000000) 1 (IntervalRat.scale (415 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (13468904686 / 1000000000000) (13468904808 / 1000000000000), orderedInterval (-48962114723 / 1000000000000) (-48962114601 / 1000000000000)))) (orderedInterval (9067320670 / 1000000000000) (9067320699 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (35679495885781 / 800000000000) 1 (IntervalRat.scale (415 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (117725816780 / 1000000000000) (117725816782 / 1000000000000), orderedInterval (19026735924 / 1000000000000) (19026735926 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (95840144685457 / 800000000000) 1 (IntervalRat.scale (415 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (68048321156 / 1000000000000) (68048321157 / 1000000000000), orderedInterval (25858014556 / 1000000000000) (25858014557 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (260224636384269 / 800000000000) 1 (IntervalRat.scale (415 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-27117950556 / 1000000000000) (-27117942667 / 1000000000000), orderedInterval (34995315718 / 1000000000000) (34995323607 / 1000000000000)))) (orderedInterval (-3399208618 / 1000000000000) (-3399207710 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (191680289370997 / 800000000000) 1 (IntervalRat.scale (415 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (51472628453 / 1000000000000) (51472628644 / 1000000000000), orderedInterval (-2858682404 / 1000000000000) (-2858682213 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (328447442923081 / 800000000000) 1 (IntervalRat.scale (415 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (7986743558 / 1000000000000) (7986743572 / 1000000000000), orderedInterval (-38569146436 / 1000000000000) (-38569146422 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (241932899887579 / 800000000000) 1 (IntervalRat.scale (415 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (45849349798 / 1000000000000) (45849350034 / 1000000000000), orderedInterval (-1792227701 / 1000000000000) (-1792227465 / 1000000000000)))) (orderedInterval (2290666549 / 1000000000000) (2290666579 / 1000000000000))) = true
  rfl'

theorem compactCertificate335_chunkChecks1_1 :
    compactCertificate335.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (371187284264917 / 800000000000) 1 (IntervalRat.scale (415 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-6867481701 / 1000000000000) (-6867481694 / 1000000000000), orderedInterval (36406724850 / 1000000000000) (36406724857 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (214305078490093 / 800000000000) 1 (IntervalRat.scale (415 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-48661269252 / 1000000000000) (-48661269000 / 1000000000000), orderedInterval (3019278956 / 1000000000000) (3019279209 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (380288122475537 / 800000000000) 1 (IntervalRat.scale (415 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-35909067904 / 1000000000000) (-35909063636 / 1000000000000), orderedInterval (7092909937 / 1000000000000) (7092914205 / 1000000000000)))) (orderedInterval (-11866498514 / 1000000000000) (-11866496926 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (355314493694453 / 800000000000) 1 (IntervalRat.scale (415 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-34975392855 / 1000000000000) (-34975366613 / 1000000000000), orderedInterval (14533788212 / 1000000000000) (14533814453 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (253569188454149 / 800000000000) 1 (IntervalRat.scale (415 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-19317089130 / 1000000000000) (-19317089129 / 1000000000000), orderedInterval (-40409111496 / 1000000000000) (-40409111495 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (287520434056371 / 800000000000) 1 (IntervalRat.scale (415 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (37461792566 / 1000000000000) (37461829514 / 1000000000000), orderedInterval (-19234144338 / 1000000000000) (-19234107390 / 1000000000000)))) (orderedInterval (-6230002633 / 1000000000000) (-6230001254 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (239704562404099 / 800000000000) 1 (IntervalRat.scale (415 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-42569871766 / 1000000000000) (-42569858588 / 1000000000000), orderedInterval (17748299285 / 1000000000000) (17748312463 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (211786250394079 / 800000000000) 1 (IntervalRat.scale (415 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (48969069007 / 1000000000000) (48969069233 / 1000000000000), orderedInterval (-2698130901 / 1000000000000) (-2698130676 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (61383910129821 / 160000000000) 1 (IntervalRat.scale (415 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (37349758905 / 1000000000000) (37349758906 / 1000000000000), orderedInterval (16210887160 / 1000000000000) (16210887161 / 1000000000000)))) (orderedInterval (1260358711 / 1000000000000) (1260358977 / 1000000000000))) = true
  rfl'

theorem compactCertificate335_chunkChecks1_2 :
    compactCertificate335.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (169791125877287 / 800000000000) 1 (IntervalRat.scale (415 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-31131223435 / 1000000000000) (-31131215393 / 1000000000000), orderedInterval (45133221375 / 1000000000000) (45133229417 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (143933817791407 / 800000000000) 1 (IntervalRat.scale (415 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-59375895842 / 1000000000000) (-59375895703 / 1000000000000), orderedInterval (3755577921 / 1000000000000) (3755578060 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (90067100112421 / 800000000000) 1 (IntervalRat.scale (415 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (20117338789 / 1000000000000) (20117338790 / 1000000000000), orderedInterval (72367314211 / 1000000000000) (72367314212 / 1000000000000)))) (orderedInterval (-6287314264 / 1000000000000) (-6287312893 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (48438385990107 / 800000000000) 1 (IntervalRat.scale (415 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-102284542674 / 1000000000000) (-102284542605 / 1000000000000), orderedInterval (8043176631 / 1000000000000) (8043176701 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (131519640571321 / 800000000000) 1 (IntervalRat.scale (415 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (60285033583 / 1000000000000) (60285034979 / 1000000000000), orderedInterval (-15613596273 / 1000000000000) (-15613594878 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (179578825240217 / 800000000000) 1 (IntervalRat.scale (415 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-42889642552 / 1000000000000) (-42889559230 / 1000000000000), orderedInterval (31663465885 / 1000000000000) (31663549207 / 1000000000000)))) (orderedInterval (-2387850279 / 1000000000000) (-2387843322 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (75932899887579 / 800000000000) 1 (IntervalRat.scale (415 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (81323746822 / 1000000000000) (81323746827 / 1000000000000), orderedInterval (9243235376 / 1000000000000) (9243235381 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (308663022374459 / 800000000000) 1 (IntervalRat.scale (415 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-7988598492 / 1000000000000) (-7988598491 / 1000000000000), orderedInterval (-39816642170 / 1000000000000) (-39816642169 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (206172594247381 / 800000000000) 1 (IntervalRat.scale (415 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (38623428550 / 1000000000000) (38623428551 / 1000000000000), orderedInterval (31205570269 / 1000000000000) (31205570270 / 1000000000000)))) (orderedInterval (-1219796604 / 1000000000000) (-1219796522 / 1000000000000))) = true
  rfl'

theorem compactCertificate335_chunkChecks1 :
    compactCertificate335.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate335.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate335_chunkChecks1_0
    compactCertificate335_chunkChecks1_1 compactCertificate335_chunkChecks1_2

theorem compactCertificate335_chunkChecks2_0 :
    compactCertificate335.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (415 / 2) 2 (IntervalRat.scale (415 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (44720106030 / 1000000000000) (44720106031 / 1000000000000), orderedInterval (32574905048 / 1000000000000) (32574905049 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (122274848675783 / 800000000000) 2 (IntervalRat.scale (415 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (19681647839 / 1000000000000) (19681648237 / 1000000000000), orderedInterval (-61528383769 / 1000000000000) (-61528383371 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (39541173766439 / 160000000000) 2 (IntervalRat.scale (415 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (13468904686 / 1000000000000) (13468904808 / 1000000000000), orderedInterval (-48962114723 / 1000000000000) (-48962114601 / 1000000000000)))) (orderedInterval (-18989811808 / 1000000000000) (-18989811776 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (35679495885781 / 800000000000) 2 (IntervalRat.scale (415 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (117725816780 / 1000000000000) (117725816782 / 1000000000000), orderedInterval (19026735924 / 1000000000000) (19026735926 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (95840144685457 / 800000000000) 2 (IntervalRat.scale (415 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (68048321156 / 1000000000000) (68048321157 / 1000000000000), orderedInterval (25858014556 / 1000000000000) (25858014557 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (260224636384269 / 800000000000) 2 (IntervalRat.scale (415 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-27117950556 / 1000000000000) (-27117942667 / 1000000000000), orderedInterval (34995315718 / 1000000000000) (34995323607 / 1000000000000)))) (orderedInterval (-5490241395 / 1000000000000) (-5490239973 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (191680289370997 / 800000000000) 2 (IntervalRat.scale (415 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (51472628453 / 1000000000000) (51472628644 / 1000000000000), orderedInterval (-2858682404 / 1000000000000) (-2858682213 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (328447442923081 / 800000000000) 2 (IntervalRat.scale (415 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (7986743558 / 1000000000000) (7986743572 / 1000000000000), orderedInterval (-38569146436 / 1000000000000) (-38569146422 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (241932899887579 / 800000000000) 2 (IntervalRat.scale (415 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (45849349798 / 1000000000000) (45849350034 / 1000000000000), orderedInterval (-1792227701 / 1000000000000) (-1792227465 / 1000000000000)))) (orderedInterval (-1400325471 / 1000000000000) (-1400325421 / 1000000000000))) = true
  rfl'

theorem compactCertificate335_chunkChecks2_1 :
    compactCertificate335.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (371187284264917 / 800000000000) 2 (IntervalRat.scale (415 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-6867481701 / 1000000000000) (-6867481694 / 1000000000000), orderedInterval (36406724850 / 1000000000000) (36406724857 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (214305078490093 / 800000000000) 2 (IntervalRat.scale (415 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-48661269252 / 1000000000000) (-48661269000 / 1000000000000), orderedInterval (3019278956 / 1000000000000) (3019279209 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (380288122475537 / 800000000000) 2 (IntervalRat.scale (415 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-35909067904 / 1000000000000) (-35909063636 / 1000000000000), orderedInterval (7092909937 / 1000000000000) (7092914205 / 1000000000000)))) (orderedInterval (26755188296 / 1000000000000) (26755191891 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (355314493694453 / 800000000000) 2 (IntervalRat.scale (415 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-34975392855 / 1000000000000) (-34975366613 / 1000000000000), orderedInterval (14533788212 / 1000000000000) (14533814453 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (253569188454149 / 800000000000) 2 (IntervalRat.scale (415 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-19317089130 / 1000000000000) (-19317089129 / 1000000000000), orderedInterval (-40409111496 / 1000000000000) (-40409111495 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (287520434056371 / 800000000000) 2 (IntervalRat.scale (415 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (37461792566 / 1000000000000) (37461829514 / 1000000000000), orderedInterval (-19234144338 / 1000000000000) (-19234107390 / 1000000000000)))) (orderedInterval (1968175143 / 1000000000000) (1968177949 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (239704562404099 / 800000000000) 2 (IntervalRat.scale (415 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-42569871766 / 1000000000000) (-42569858588 / 1000000000000), orderedInterval (17748299285 / 1000000000000) (17748312463 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (211786250394079 / 800000000000) 2 (IntervalRat.scale (415 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (48969069007 / 1000000000000) (48969069233 / 1000000000000), orderedInterval (-2698130901 / 1000000000000) (-2698130676 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (61383910129821 / 160000000000) 2 (IntervalRat.scale (415 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (37349758905 / 1000000000000) (37349758906 / 1000000000000), orderedInterval (16210887160 / 1000000000000) (16210887161 / 1000000000000)))) (orderedInterval (2311267710 / 1000000000000) (2311268093 / 1000000000000))) = true
  rfl'

theorem compactCertificate335_chunkChecks2_2 :
    compactCertificate335.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (169791125877287 / 800000000000) 2 (IntervalRat.scale (415 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-31131223435 / 1000000000000) (-31131215393 / 1000000000000), orderedInterval (45133221375 / 1000000000000) (45133229417 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (143933817791407 / 800000000000) 2 (IntervalRat.scale (415 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-59375895842 / 1000000000000) (-59375895703 / 1000000000000), orderedInterval (3755577921 / 1000000000000) (3755578060 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (90067100112421 / 800000000000) 2 (IntervalRat.scale (415 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (20117338789 / 1000000000000) (20117338790 / 1000000000000), orderedInterval (72367314211 / 1000000000000) (72367314212 / 1000000000000)))) (orderedInterval (-7896699705 / 1000000000000) (-7896698301 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (48438385990107 / 800000000000) 2 (IntervalRat.scale (415 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-102284542674 / 1000000000000) (-102284542605 / 1000000000000), orderedInterval (8043176631 / 1000000000000) (8043176701 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (131519640571321 / 800000000000) 2 (IntervalRat.scale (415 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (60285033583 / 1000000000000) (60285034979 / 1000000000000), orderedInterval (-15613596273 / 1000000000000) (-15613594878 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (179578825240217 / 800000000000) 2 (IntervalRat.scale (415 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-42889642552 / 1000000000000) (-42889559230 / 1000000000000), orderedInterval (31663465885 / 1000000000000) (31663549207 / 1000000000000)))) (orderedInterval (-3137554133 / 1000000000000) (-3137546583 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (75932899887579 / 800000000000) 2 (IntervalRat.scale (415 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (81323746822 / 1000000000000) (81323746827 / 1000000000000), orderedInterval (9243235376 / 1000000000000) (9243235381 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (308663022374459 / 800000000000) 2 (IntervalRat.scale (415 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-7988598492 / 1000000000000) (-7988598491 / 1000000000000), orderedInterval (-39816642170 / 1000000000000) (-39816642169 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (206172594247381 / 800000000000) 2 (IntervalRat.scale (415 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (38623428550 / 1000000000000) (38623428551 / 1000000000000), orderedInterval (31205570269 / 1000000000000) (31205570270 / 1000000000000)))) (orderedInterval (8833668753 / 1000000000000) (8833668874 / 1000000000000))) = true
  rfl'

theorem compactCertificate335_chunkChecks2 :
    compactCertificate335.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate335.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate335_chunkChecks2_0
    compactCertificate335_chunkChecks2_1 compactCertificate335_chunkChecks2_2

theorem compactCertificate335_chunkChecks3_0 :
    compactCertificate335.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (415 / 2) 3 (IntervalRat.scale (415 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (44720106030 / 1000000000000) (44720106031 / 1000000000000), orderedInterval (32574905048 / 1000000000000) (32574905049 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (122274848675783 / 800000000000) 3 (IntervalRat.scale (415 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (19681647839 / 1000000000000) (19681648237 / 1000000000000), orderedInterval (-61528383769 / 1000000000000) (-61528383371 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (39541173766439 / 160000000000) 3 (IntervalRat.scale (415 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (13468904686 / 1000000000000) (13468904808 / 1000000000000), orderedInterval (-48962114723 / 1000000000000) (-48962114601 / 1000000000000)))) (orderedInterval (-7736765252 / 1000000000000) (-7736765216 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (35679495885781 / 800000000000) 3 (IntervalRat.scale (415 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (117725816780 / 1000000000000) (117725816782 / 1000000000000), orderedInterval (19026735924 / 1000000000000) (19026735926 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (95840144685457 / 800000000000) 3 (IntervalRat.scale (415 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (68048321156 / 1000000000000) (68048321157 / 1000000000000), orderedInterval (25858014556 / 1000000000000) (25858014557 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (260224636384269 / 800000000000) 3 (IntervalRat.scale (415 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-27117950556 / 1000000000000) (-27117942667 / 1000000000000), orderedInterval (34995315718 / 1000000000000) (34995323607 / 1000000000000)))) (orderedInterval (9430521649 / 1000000000000) (9430523876 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (191680289370997 / 800000000000) 3 (IntervalRat.scale (415 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (51472628453 / 1000000000000) (51472628644 / 1000000000000), orderedInterval (-2858682404 / 1000000000000) (-2858682213 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (328447442923081 / 800000000000) 3 (IntervalRat.scale (415 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (7986743558 / 1000000000000) (7986743572 / 1000000000000), orderedInterval (-38569146436 / 1000000000000) (-38569146422 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (241932899887579 / 800000000000) 3 (IntervalRat.scale (415 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (45849349798 / 1000000000000) (45849350034 / 1000000000000), orderedInterval (-1792227701 / 1000000000000) (-1792227465 / 1000000000000)))) (orderedInterval (-9073870849 / 1000000000000) (-9073870761 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate335_chunkChecks3_1 :
    compactCertificate335.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (371187284264917 / 800000000000) 3 (IntervalRat.scale (415 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-6867481701 / 1000000000000) (-6867481694 / 1000000000000), orderedInterval (36406724850 / 1000000000000) (36406724857 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (214305078490093 / 800000000000) 3 (IntervalRat.scale (415 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-48661269252 / 1000000000000) (-48661269000 / 1000000000000), orderedInterval (3019278956 / 1000000000000) (3019279209 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (380288122475537 / 800000000000) 3 (IntervalRat.scale (415 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-35909067904 / 1000000000000) (-35909063636 / 1000000000000), orderedInterval (7092909937 / 1000000000000) (7092914205 / 1000000000000)))) (orderedInterval (59592646183 / 1000000000000) (59592654349 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (355314493694453 / 800000000000) 3 (IntervalRat.scale (415 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-34975392855 / 1000000000000) (-34975366613 / 1000000000000), orderedInterval (14533788212 / 1000000000000) (14533814453 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (253569188454149 / 800000000000) 3 (IntervalRat.scale (415 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-19317089130 / 1000000000000) (-19317089129 / 1000000000000), orderedInterval (-40409111496 / 1000000000000) (-40409111495 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (287520434056371 / 800000000000) 3 (IntervalRat.scale (415 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (37461792566 / 1000000000000) (37461829514 / 1000000000000), orderedInterval (-19234144338 / 1000000000000) (-19234107390 / 1000000000000)))) (orderedInterval (15677251364 / 1000000000000) (15677257108 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (239704562404099 / 800000000000) 3 (IntervalRat.scale (415 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-42569871766 / 1000000000000) (-42569858588 / 1000000000000), orderedInterval (17748299285 / 1000000000000) (17748312463 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (211786250394079 / 800000000000) 3 (IntervalRat.scale (415 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (48969069007 / 1000000000000) (48969069233 / 1000000000000), orderedInterval (-2698130901 / 1000000000000) (-2698130676 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (61383910129821 / 160000000000) 3 (IntervalRat.scale (415 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (37349758905 / 1000000000000) (37349758906 / 1000000000000), orderedInterval (16210887160 / 1000000000000) (16210887161 / 1000000000000)))) (orderedInterval (-3572251400 / 1000000000000) (-3572250847 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate335_chunkChecks3_2 :
    compactCertificate335.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (169791125877287 / 800000000000) 3 (IntervalRat.scale (415 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-31131223435 / 1000000000000) (-31131215393 / 1000000000000), orderedInterval (45133221375 / 1000000000000) (45133229417 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (143933817791407 / 800000000000) 3 (IntervalRat.scale (415 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-59375895842 / 1000000000000) (-59375895703 / 1000000000000), orderedInterval (3755577921 / 1000000000000) (3755578060 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (90067100112421 / 800000000000) 3 (IntervalRat.scale (415 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (20117338789 / 1000000000000) (20117338790 / 1000000000000), orderedInterval (72367314211 / 1000000000000) (72367314212 / 1000000000000)))) (orderedInterval (7522442909 / 1000000000000) (7522444342 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (48438385990107 / 800000000000) 3 (IntervalRat.scale (415 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-102284542674 / 1000000000000) (-102284542605 / 1000000000000), orderedInterval (8043176631 / 1000000000000) (8043176701 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (131519640571321 / 800000000000) 3 (IntervalRat.scale (415 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (60285033583 / 1000000000000) (60285034979 / 1000000000000), orderedInterval (-15613596273 / 1000000000000) (-15613594878 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (179578825240217 / 800000000000) 3 (IntervalRat.scale (415 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-42889642552 / 1000000000000) (-42889559230 / 1000000000000), orderedInterval (31663465885 / 1000000000000) (31663549207 / 1000000000000)))) (orderedInterval (2914782213 / 1000000000000) (2914790372 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (75932899887579 / 800000000000) 3 (IntervalRat.scale (415 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (81323746822 / 1000000000000) (81323746827 / 1000000000000), orderedInterval (9243235376 / 1000000000000) (9243235381 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (308663022374459 / 800000000000) 3 (IntervalRat.scale (415 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-7988598492 / 1000000000000) (-7988598491 / 1000000000000), orderedInterval (-39816642170 / 1000000000000) (-39816642169 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (206172594247381 / 800000000000) 3 (IntervalRat.scale (415 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (38623428550 / 1000000000000) (38623428551 / 1000000000000), orderedInterval (31205570269 / 1000000000000) (31205570270 / 1000000000000)))) (orderedInterval (-9667121940 / 1000000000000) (-9667121755 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate335_chunkChecks3 :
    compactCertificate335.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate335.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate335_chunkChecks3_0
    compactCertificate335_chunkChecks3_1 compactCertificate335_chunkChecks3_2

theorem compactCertificate335_chunkChecks4_0 :
    compactCertificate335.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (415 / 2) 4 (IntervalRat.scale (415 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (44720106030 / 1000000000000) (44720106031 / 1000000000000), orderedInterval (32574905048 / 1000000000000) (32574905049 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (122274848675783 / 800000000000) 4 (IntervalRat.scale (415 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (19681647839 / 1000000000000) (19681648237 / 1000000000000), orderedInterval (-61528383769 / 1000000000000) (-61528383371 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (39541173766439 / 160000000000) 4 (IntervalRat.scale (415 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (13468904686 / 1000000000000) (13468904808 / 1000000000000), orderedInterval (-48962114723 / 1000000000000) (-48962114601 / 1000000000000)))) (orderedInterval (19443893822 / 1000000000000) (19443893864 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (35679495885781 / 800000000000) 4 (IntervalRat.scale (415 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (117725816780 / 1000000000000) (117725816782 / 1000000000000), orderedInterval (19026735924 / 1000000000000) (19026735926 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (95840144685457 / 800000000000) 4 (IntervalRat.scale (415 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (68048321156 / 1000000000000) (68048321157 / 1000000000000), orderedInterval (25858014556 / 1000000000000) (25858014557 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (260224636384269 / 800000000000) 4 (IntervalRat.scale (415 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-27117950556 / 1000000000000) (-27117942667 / 1000000000000), orderedInterval (34995315718 / 1000000000000) (34995323607 / 1000000000000)))) (orderedInterval (11824225804 / 1000000000000) (11824229303 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (191680289370997 / 800000000000) 4 (IntervalRat.scale (415 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (51472628453 / 1000000000000) (51472628644 / 1000000000000), orderedInterval (-2858682404 / 1000000000000) (-2858682213 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (328447442923081 / 800000000000) 4 (IntervalRat.scale (415 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (7986743558 / 1000000000000) (7986743572 / 1000000000000), orderedInterval (-38569146436 / 1000000000000) (-38569146422 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (241932899887579 / 800000000000) 4 (IntervalRat.scale (415 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (45849349798 / 1000000000000) (45849350034 / 1000000000000), orderedInterval (-1792227701 / 1000000000000) (-1792227465 / 1000000000000)))) (orderedInterval (1311395309 / 1000000000000) (1311395464 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate335_chunkChecks4_1 :
    compactCertificate335.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (371187284264917 / 800000000000) 4 (IntervalRat.scale (415 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-6867481701 / 1000000000000) (-6867481694 / 1000000000000), orderedInterval (36406724850 / 1000000000000) (36406724857 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (214305078490093 / 800000000000) 4 (IntervalRat.scale (415 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-48661269252 / 1000000000000) (-48661269000 / 1000000000000), orderedInterval (3019278956 / 1000000000000) (3019279209 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (380288122475537 / 800000000000) 4 (IntervalRat.scale (415 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-35909067904 / 1000000000000) (-35909063636 / 1000000000000), orderedInterval (7092909937 / 1000000000000) (7092914205 / 1000000000000)))) (orderedInterval (-120682816753 / 1000000000000) (-120682798110 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (355314493694453 / 800000000000) 4 (IntervalRat.scale (415 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-34975392855 / 1000000000000) (-34975366613 / 1000000000000), orderedInterval (14533788212 / 1000000000000) (14533814453 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (253569188454149 / 800000000000) 4 (IntervalRat.scale (415 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-19317089130 / 1000000000000) (-19317089129 / 1000000000000), orderedInterval (-40409111496 / 1000000000000) (-40409111495 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (287520434056371 / 800000000000) 4 (IntervalRat.scale (415 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (37461792566 / 1000000000000) (37461829514 / 1000000000000), orderedInterval (-19234144338 / 1000000000000) (-19234107390 / 1000000000000)))) (orderedInterval (1451056106 / 1000000000000) (1451067983 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (239704562404099 / 800000000000) 4 (IntervalRat.scale (415 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-42569871766 / 1000000000000) (-42569858588 / 1000000000000), orderedInterval (17748299285 / 1000000000000) (17748312463 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (211786250394079 / 800000000000) 4 (IntervalRat.scale (415 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (48969069007 / 1000000000000) (48969069233 / 1000000000000), orderedInterval (-2698130901 / 1000000000000) (-2698130676 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (61383910129821 / 160000000000) 4 (IntervalRat.scale (415 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (37349758905 / 1000000000000) (37349758906 / 1000000000000), orderedInterval (16210887160 / 1000000000000) (16210887161 / 1000000000000)))) (orderedInterval (1647799236 / 1000000000000) (1647800042 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate335_chunkChecks4_2 :
    compactCertificate335.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (169791125877287 / 800000000000) 4 (IntervalRat.scale (415 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-31131223435 / 1000000000000) (-31131215393 / 1000000000000), orderedInterval (45133221375 / 1000000000000) (45133229417 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (143933817791407 / 800000000000) 4 (IntervalRat.scale (415 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-59375895842 / 1000000000000) (-59375895703 / 1000000000000), orderedInterval (3755577921 / 1000000000000) (3755578060 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (90067100112421 / 800000000000) 4 (IntervalRat.scale (415 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (20117338789 / 1000000000000) (20117338790 / 1000000000000), orderedInterval (72367314211 / 1000000000000) (72367314212 / 1000000000000)))) (orderedInterval (7331777711 / 1000000000000) (7331779181 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (48438385990107 / 800000000000) 4 (IntervalRat.scale (415 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-102284542674 / 1000000000000) (-102284542605 / 1000000000000), orderedInterval (8043176631 / 1000000000000) (8043176701 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (131519640571321 / 800000000000) 4 (IntervalRat.scale (415 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (60285033583 / 1000000000000) (60285034979 / 1000000000000), orderedInterval (-15613596273 / 1000000000000) (-15613594878 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (179578825240217 / 800000000000) 4 (IntervalRat.scale (415 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-42889642552 / 1000000000000) (-42889559230 / 1000000000000), orderedInterval (31663465885 / 1000000000000) (31663549207 / 1000000000000)))) (orderedInterval (3948445698 / 1000000000000) (3948454558 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (75932899887579 / 800000000000) 4 (IntervalRat.scale (415 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (81323746822 / 1000000000000) (81323746827 / 1000000000000), orderedInterval (9243235376 / 1000000000000) (9243235381 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (308663022374459 / 800000000000) 4 (IntervalRat.scale (415 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-7988598492 / 1000000000000) (-7988598491 / 1000000000000), orderedInterval (-39816642170 / 1000000000000) (-39816642169 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (206172594247381 / 800000000000) 4 (IntervalRat.scale (415 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (38623428550 / 1000000000000) (38623428551 / 1000000000000), orderedInterval (31205570269 / 1000000000000) (31205570270 / 1000000000000)))) (orderedInterval (-9355700648 / 1000000000000) (-9355700351 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate335_chunkChecks4 :
    compactCertificate335.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate335.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate335_chunkChecks4_0
    compactCertificate335_chunkChecks4_1 compactCertificate335_chunkChecks4_2

theorem compactCertificate335_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate335.chunkCheck r b = true :=
  compactCertificate335.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate335_chunkChecks0
    · exact compactCertificate335_chunkChecks1
    · exact compactCertificate335_chunkChecks2
    · exact compactCertificate335_chunkChecks3
    · exact compactCertificate335_chunkChecks4)

theorem compactCertificate335_coefficient0 :
    compactCertificate335.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate335_coefficient1 :
    compactCertificate335.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate335_coefficient2 :
    compactCertificate335.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate335_coefficient3 :
    compactCertificate335.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate335_coefficient4 :
    compactCertificate335.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate335_coefficients : ∀ r : Fin 5,
    compactCertificate335.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate335_coefficient0
  · exact compactCertificate335_coefficient1
  · exact compactCertificate335_coefficient2
  · exact compactCertificate335_coefficient3
  · exact compactCertificate335_coefficient4

theorem compactCertificate335_lower : (1 : ℚ) ≤ compactCertificate335.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate335, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate335_proves {t : ℝ} (ht : t ∈ compactCertificate335.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate335.proves compactCertificate335_states compactCertificate335_chunks
    compactCertificate335_coefficients compactCertificate335_lower ht

end Erdos232
