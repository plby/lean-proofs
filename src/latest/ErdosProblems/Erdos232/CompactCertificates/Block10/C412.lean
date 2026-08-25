/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate412 : CompactCertificate where
  left := 283
  right := 284
  center := 567 / 2
  grid := fun i =>
    match i.val with
    | 0 => 90
    | 1 => 67
    | 2 => 108
    | 3 => 19
    | 4 => 52
    | 5 => 142
    | 6 => 104
    | 7 => 179
    | 8 => 132
    | 9 => 202
    | 10 => 117
    | 11 => 207
    | 12 => 193
    | 13 => 138
    | 14 => 156
    | 15 => 130
    | 16 => 115
    | 17 => 167
    | 18 => 92
    | 19 => 78
    | 20 => 49
    | 21 => 26
    | 22 => 72
    | 23 => 98
    | 24 => 41
    | 25 => 168
    | _ => 112
  point := fun i =>
    match i.val with
    | 0 => 567 / 2
    | 1 => 835299267459867 / 4000000000000
    | 2 => 270118620790011 / 800000000000
    | 3 => 243738242978769 / 4000000000000
    | 4 => 654715205260893 / 4000000000000
    | 5 => 1777679142528681 / 4000000000000
    | 6 => 1309430410522353 / 4000000000000
    | 7 => 2243731326956469 / 4000000000000
    | 8 => 1652722340195871 / 4000000000000
    | 9 => 2535701086484433 / 4000000000000
    | 10 => 1463987704866057 / 4000000000000
    | 11 => 2597871872814813 / 4000000000000
    | 12 => 2427268890659697 / 4000000000000
    | 13 => 1732213612692801 / 4000000000000
    | 14 => 1964145615782679 / 4000000000000
    | 15 => 1637499841965351 / 4000000000000
    | 16 => 1446780770764371 / 4000000000000
    | 17 => 419333458356729 / 800000000000
    | 18 => 1159898414125563 / 4000000000000
    | 19 => 983258731177443 / 4000000000000
    | 20 => 615277659804129 / 4000000000000
    | 21 => 330898371763743 / 4000000000000
    | 22 => 898453448240229 / 4000000000000
    | 23 => 1226761372424133 / 4000000000000
    | 24 => 518722340195871 / 4000000000000
    | 25 => 2108577514292991 / 4000000000000
    | _ => 1408432059497169 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (47367263701 / 1000000000000) (47367263783 / 1000000000000), orderedInterval (1298931886 / 1000000000000) (1298931968 / 1000000000000))
    | 1 => (orderedInterval (42452937972 / 1000000000000) (42453037953 / 1000000000000), orderedInterval (-35405023118 / 1000000000000) (-35404923138 / 1000000000000))
    | 2 => (orderedInterval (-32870109619 / 1000000000000) (-32870060810 / 1000000000000), orderedInterval (28421341015 / 1000000000000) (28421389824 / 1000000000000))
    | 3 => (orderedInterval (-91729549767 / 1000000000000) (-91729542243 / 1000000000000), orderedInterval (45842247717 / 1000000000000) (45842255241 / 1000000000000))
    | 4 => (orderedInterval (55597857219 / 1000000000000) (55597857220 / 1000000000000), orderedInterval (28084597379 / 1000000000000) (28084597380 / 1000000000000))
    | 5 => (orderedInterval (-29676884127 / 1000000000000) (-29676840054 / 1000000000000), orderedInterval (23522886281 / 1000000000000) (23522930355 / 1000000000000))
    | 6 => (orderedInterval (43578353584 / 1000000000000) (43578353602 / 1000000000000), orderedInterval (6689745415 / 1000000000000) (6689745433 / 1000000000000))
    | 7 => (orderedInterval (19767906169 / 1000000000000) (19767907693 / 1000000000000), orderedInterval (-27296926331 / 1000000000000) (-27296924808 / 1000000000000))
    | 8 => (orderedInterval (-26016650162 / 1000000000000) (-26016640490 / 1000000000000), orderedInterval (29423872312 / 1000000000000) (29423881984 / 1000000000000))
    | 9 => (orderedInterval (3439695584 / 1000000000000) (3439695585 / 1000000000000), orderedInterval (31499974198 / 1000000000000) (31499974199 / 1000000000000))
    | 10 => (orderedInterval (29460058420 / 1000000000000) (29460080185 / 1000000000000), orderedInterval (-29561726907 / 1000000000000) (-29561705142 / 1000000000000))
    | 11 => (orderedInterval (1768153160 / 1000000000000) (1768153161 / 1000000000000), orderedInterval (-31259820496 / 1000000000000) (-31259820495 / 1000000000000))
    | 12 => (orderedInterval (-30983627635 / 1000000000000) (-30983627617 / 1000000000000), orderedInterval (-9415202216 / 1000000000000) (-9415202198 / 1000000000000))
    | 13 => (orderedInterval (11284033857 / 1000000000000) (11284033858 / 1000000000000), orderedInterval (36630437521 / 1000000000000) (36630437522 / 1000000000000))
    | 14 => (orderedInterval (35533505131 / 1000000000000) (35533508437 / 1000000000000), orderedInterval (-5854351712 / 1000000000000) (-5854348406 / 1000000000000))
    | 15 => (orderedInterval (38781932160 / 1000000000000) (38781934773 / 1000000000000), orderedInterval (-7193166791 / 1000000000000) (-7193164178 / 1000000000000))
    | 16 => (orderedInterval (-39057925343 / 1000000000000) (-39057925342 / 1000000000000), orderedInterval (-15261927400 / 1000000000000) (-15261927399 / 1000000000000))
    | 17 => (orderedInterval (-10498827134 / 1000000000000) (-10498827133 / 1000000000000), orderedInterval (-33221170069 / 1000000000000) (-33221170068 / 1000000000000))
    | 18 => (orderedInterval (46240025723 / 1000000000000) (46240026764 / 1000000000000), orderedInterval (-7648729736 / 1000000000000) (-7648728694 / 1000000000000))
    | 19 => (orderedInterval (50884306560 / 1000000000000) (50884306636 / 1000000000000), orderedInterval (682769416 / 1000000000000) (682769493 / 1000000000000))
    | 20 => (orderedInterval (-39745827381 / 1000000000000) (-39745827380 / 1000000000000), orderedInterval (-50457584129 / 1000000000000) (-50457584128 / 1000000000000))
    | 21 => (orderedInterval (84859083858 / 1000000000000) (84859084782 / 1000000000000), orderedInterval (-22749484638 / 1000000000000) (-22749483714 / 1000000000000))
    | 22 => (orderedInterval (-38059356803 / 1000000000000) (-38059310142 / 1000000000000), orderedInterval (37310743886 / 1000000000000) (37310790547 / 1000000000000))
    | 23 => (orderedInterval (-17773460579 / 1000000000000) (-17773460109 / 1000000000000), orderedInterval (41979897293 / 1000000000000) (41979897763 / 1000000000000))
    | 24 => (orderedInterval (-69788136933 / 1000000000000) (-69788136787 / 1000000000000), orderedInterval (6491383787 / 1000000000000) (6491383933 / 1000000000000))
    | 25 => (orderedInterval (4917263041 / 1000000000000) (4917263042 / 1000000000000), orderedInterval (34397332183 / 1000000000000) (34397332184 / 1000000000000))
    | _ => (orderedInterval (36555143684 / 1000000000000) (36555143685 / 1000000000000), orderedInterval (21667775417 / 1000000000000) (21667775418 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (17241448654 / 1000000000000) (17241452503 / 1000000000000)
      | 1 => orderedInterval (5134891226 / 1000000000000) (5134894476 / 1000000000000)
      | 2 => orderedInterval (-1238492477 / 1000000000000) (-1238492179 / 1000000000000)
      | 3 => orderedInterval (1822908861 / 1000000000000) (1822910586 / 1000000000000)
      | 4 => orderedInterval (1446580638 / 1000000000000) (1446580690 / 1000000000000)
      | 5 => orderedInterval (2414184774 / 1000000000000) (2414184832 / 1000000000000)
      | 6 => orderedInterval (-11567416531 / 1000000000000) (-11567416289 / 1000000000000)
      | 7 => orderedInterval (658651270 / 1000000000000) (658652416 / 1000000000000)
      | _ => orderedInterval (-7679694423 / 1000000000000) (-7679694343 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (2258188296 / 1000000000000) (2258192449 / 1000000000000)
      | 1 => orderedInterval (-2136303702 / 1000000000000) (-2136298734 / 1000000000000)
      | 2 => orderedInterval (2702275395 / 1000000000000) (2702275857 / 1000000000000)
      | 3 => orderedInterval (-25523475100 / 1000000000000) (-25523472784 / 1000000000000)
      | 4 => orderedInterval (5706296638 / 1000000000000) (5706296723 / 1000000000000)
      | 5 => orderedInterval (-578329583 / 1000000000000) (-578329499 / 1000000000000)
      | 6 => orderedInterval (326133596 / 1000000000000) (326133836 / 1000000000000)
      | 7 => orderedInterval (-4028534000 / 1000000000000) (-4028533086 / 1000000000000)
      | _ => orderedInterval (-10237774304 / 1000000000000) (-10237774192 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-16261284365 / 1000000000000) (-16261279724 / 1000000000000)
      | 1 => orderedInterval (-5899579689 / 1000000000000) (-5899571914 / 1000000000000)
      | 2 => orderedInterval (3713006499 / 1000000000000) (3713007231 / 1000000000000)
      | 3 => orderedInterval (-1811074079 / 1000000000000) (-1811070883 / 1000000000000)
      | 4 => orderedInterval (-4533126894 / 1000000000000) (-4533126751 / 1000000000000)
      | 5 => orderedInterval (-3651051488 / 1000000000000) (-3651051366 / 1000000000000)
      | 6 => orderedInterval (10280013335 / 1000000000000) (10280013577 / 1000000000000)
      | 7 => orderedInterval (-1988472875 / 1000000000000) (-1988472133 / 1000000000000)
      | _ => orderedInterval (12088125592 / 1000000000000) (12088125756 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-3143208324 / 1000000000000) (-3143203034 / 1000000000000)
      | 1 => orderedInterval (6270338097 / 1000000000000) (6270350276 / 1000000000000)
      | 2 => orderedInterval (-8736132712 / 1000000000000) (-8736131532 / 1000000000000)
      | 3 => orderedInterval (120724571355 / 1000000000000) (120724575932 / 1000000000000)
      | 4 => orderedInterval (-14150775519 / 1000000000000) (-14150775274 / 1000000000000)
      | 5 => orderedInterval (3825375292 / 1000000000000) (3825375473 / 1000000000000)
      | 6 => orderedInterval (-1057384285 / 1000000000000) (-1057384042 / 1000000000000)
      | 7 => orderedInterval (4490662686 / 1000000000000) (4490663293 / 1000000000000)
      | _ => orderedInterval (25743056080 / 1000000000000) (25743056332 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (15032132258 / 1000000000000) (15032138400 / 1000000000000)
      | 1 => orderedInterval (12923832733 / 1000000000000) (12923851863 / 1000000000000)
      | 2 => orderedInterval (-12119837355 / 1000000000000) (-12119835406 / 1000000000000)
      | 3 => orderedInterval (-3145170677 / 1000000000000) (-3145163736 / 1000000000000)
      | 4 => orderedInterval (16031834816 / 1000000000000) (16031835242 / 1000000000000)
      | 5 => orderedInterval (4700747587 / 1000000000000) (4700747862 / 1000000000000)
      | 6 => orderedInterval (-9824746439 / 1000000000000) (-9824746193 / 1000000000000)
      | 7 => orderedInterval (2162719719 / 1000000000000) (2162720223 / 1000000000000)
      | _ => orderedInterval (-21305197851 / 1000000000000) (-21305197446 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (8233061992 / 1000000000000) (8233072692 / 1000000000000)
    | 1 => orderedInterval (-31511522764 / 1000000000000) (-31511509430 / 1000000000000)
    | 2 => orderedInterval (-8063443964 / 1000000000000) (-8063426207 / 1000000000000)
    | 3 => orderedInterval (133966502670 / 1000000000000) (133966527424 / 1000000000000)
    | _ => orderedInterval (4456314791 / 1000000000000) (4456350809 / 1000000000000)

theorem compactCertificate412_stateChecks0 :
    compactCertificate412.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 90 12 (567 / 2)) (orderedInterval (47367263701 / 1000000000000) (47367263783 / 1000000000000), orderedInterval (1298931886 / 1000000000000) (1298931968 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (835299267459867 / 4000000000000)) (orderedInterval (42452937972 / 1000000000000) (42453037953 / 1000000000000), orderedInterval (-35405023118 / 1000000000000) (-35404923138 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 108 12 (270118620790011 / 800000000000)) (orderedInterval (-32870109619 / 1000000000000) (-32870060810 / 1000000000000), orderedInterval (28421341015 / 1000000000000) (28421389824 / 1000000000000))) = true
  rfl'

theorem compactCertificate412_stateChecks1 :
    compactCertificate412.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 19 12 (243738242978769 / 4000000000000)) (orderedInterval (-91729549767 / 1000000000000) (-91729542243 / 1000000000000), orderedInterval (45842247717 / 1000000000000) (45842255241 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 52 12 (654715205260893 / 4000000000000)) (orderedInterval (55597857219 / 1000000000000) (55597857220 / 1000000000000), orderedInterval (28084597379 / 1000000000000) (28084597380 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 142 12 (1777679142528681 / 4000000000000)) (orderedInterval (-29676884127 / 1000000000000) (-29676840054 / 1000000000000), orderedInterval (23522886281 / 1000000000000) (23522930355 / 1000000000000))) = true
  rfl'

theorem compactCertificate412_stateChecks2 :
    compactCertificate412.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 104 12 (1309430410522353 / 4000000000000)) (orderedInterval (43578353584 / 1000000000000) (43578353602 / 1000000000000), orderedInterval (6689745415 / 1000000000000) (6689745433 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 179 12 (2243731326956469 / 4000000000000)) (orderedInterval (19767906169 / 1000000000000) (19767907693 / 1000000000000), orderedInterval (-27296926331 / 1000000000000) (-27296924808 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 132 12 (1652722340195871 / 4000000000000)) (orderedInterval (-26016650162 / 1000000000000) (-26016640490 / 1000000000000), orderedInterval (29423872312 / 1000000000000) (29423881984 / 1000000000000))) = true
  rfl'

theorem compactCertificate412_stateChecks3 :
    compactCertificate412.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 202 12 (2535701086484433 / 4000000000000)) (orderedInterval (3439695584 / 1000000000000) (3439695585 / 1000000000000), orderedInterval (31499974198 / 1000000000000) (31499974199 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 117 12 (1463987704866057 / 4000000000000)) (orderedInterval (29460058420 / 1000000000000) (29460080185 / 1000000000000), orderedInterval (-29561726907 / 1000000000000) (-29561705142 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 207 12 (2597871872814813 / 4000000000000)) (orderedInterval (1768153160 / 1000000000000) (1768153161 / 1000000000000), orderedInterval (-31259820496 / 1000000000000) (-31259820495 / 1000000000000))) = true
  rfl'

theorem compactCertificate412_stateChecks4 :
    compactCertificate412.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 193 12 (2427268890659697 / 4000000000000)) (orderedInterval (-30983627635 / 1000000000000) (-30983627617 / 1000000000000), orderedInterval (-9415202216 / 1000000000000) (-9415202198 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 138 12 (1732213612692801 / 4000000000000)) (orderedInterval (11284033857 / 1000000000000) (11284033858 / 1000000000000), orderedInterval (36630437521 / 1000000000000) (36630437522 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 156 12 (1964145615782679 / 4000000000000)) (orderedInterval (35533505131 / 1000000000000) (35533508437 / 1000000000000), orderedInterval (-5854351712 / 1000000000000) (-5854348406 / 1000000000000))) = true
  rfl'

theorem compactCertificate412_stateChecks5 :
    compactCertificate412.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 130 12 (1637499841965351 / 4000000000000)) (orderedInterval (38781932160 / 1000000000000) (38781934773 / 1000000000000), orderedInterval (-7193166791 / 1000000000000) (-7193164178 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 115 12 (1446780770764371 / 4000000000000)) (orderedInterval (-39057925343 / 1000000000000) (-39057925342 / 1000000000000), orderedInterval (-15261927400 / 1000000000000) (-15261927399 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 167 12 (419333458356729 / 800000000000)) (orderedInterval (-10498827134 / 1000000000000) (-10498827133 / 1000000000000), orderedInterval (-33221170069 / 1000000000000) (-33221170068 / 1000000000000))) = true
  rfl'

theorem compactCertificate412_stateChecks6 :
    compactCertificate412.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 92 12 (1159898414125563 / 4000000000000)) (orderedInterval (46240025723 / 1000000000000) (46240026764 / 1000000000000), orderedInterval (-7648729736 / 1000000000000) (-7648728694 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 78 12 (983258731177443 / 4000000000000)) (orderedInterval (50884306560 / 1000000000000) (50884306636 / 1000000000000), orderedInterval (682769416 / 1000000000000) (682769493 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 49 12 (615277659804129 / 4000000000000)) (orderedInterval (-39745827381 / 1000000000000) (-39745827380 / 1000000000000), orderedInterval (-50457584129 / 1000000000000) (-50457584128 / 1000000000000))) = true
  rfl'

theorem compactCertificate412_stateChecks7 :
    compactCertificate412.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 26 12 (330898371763743 / 4000000000000)) (orderedInterval (84859083858 / 1000000000000) (84859084782 / 1000000000000), orderedInterval (-22749484638 / 1000000000000) (-22749483714 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 72 12 (898453448240229 / 4000000000000)) (orderedInterval (-38059356803 / 1000000000000) (-38059310142 / 1000000000000), orderedInterval (37310743886 / 1000000000000) (37310790547 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 98 12 (1226761372424133 / 4000000000000)) (orderedInterval (-17773460579 / 1000000000000) (-17773460109 / 1000000000000), orderedInterval (41979897293 / 1000000000000) (41979897763 / 1000000000000))) = true
  rfl'

theorem compactCertificate412_stateChecks8 :
    compactCertificate412.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 41 12 (518722340195871 / 4000000000000)) (orderedInterval (-69788136933 / 1000000000000) (-69788136787 / 1000000000000), orderedInterval (6491383787 / 1000000000000) (6491383933 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 168 12 (2108577514292991 / 4000000000000)) (orderedInterval (4917263041 / 1000000000000) (4917263042 / 1000000000000), orderedInterval (34397332183 / 1000000000000) (34397332184 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 112 12 (1408432059497169 / 4000000000000)) (orderedInterval (36555143684 / 1000000000000) (36555143685 / 1000000000000), orderedInterval (21667775417 / 1000000000000) (21667775418 / 1000000000000))) = true
  rfl'

theorem compactCertificate412_states : ∀ j,
    BesselStateValid (compactCertificate412.point j) (compactCertificate412.state j) :=
  compactCertificate412.statesValid_of_checks3 compactCertificate412_stateChecks0
    compactCertificate412_stateChecks1 compactCertificate412_stateChecks2
    compactCertificate412_stateChecks3 compactCertificate412_stateChecks4
    compactCertificate412_stateChecks5 compactCertificate412_stateChecks6
    compactCertificate412_stateChecks7 compactCertificate412_stateChecks8

theorem compactCertificate412_chunkChecks0_0 :
    compactCertificate412.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (567 / 2) 0 (IntervalRat.scale (567 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (47367263701 / 1000000000000) (47367263783 / 1000000000000), orderedInterval (1298931886 / 1000000000000) (1298931968 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (835299267459867 / 4000000000000) 0 (IntervalRat.scale (567 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (42452937972 / 1000000000000) (42453037953 / 1000000000000), orderedInterval (-35405023118 / 1000000000000) (-35404923138 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (270118620790011 / 800000000000) 0 (IntervalRat.scale (567 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-32870109619 / 1000000000000) (-32870060810 / 1000000000000), orderedInterval (28421341015 / 1000000000000) (28421389824 / 1000000000000)))) (orderedInterval (17241448654 / 1000000000000) (17241452503 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (243738242978769 / 4000000000000) 0 (IntervalRat.scale (567 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-91729549767 / 1000000000000) (-91729542243 / 1000000000000), orderedInterval (45842247717 / 1000000000000) (45842255241 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (654715205260893 / 4000000000000) 0 (IntervalRat.scale (567 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (55597857219 / 1000000000000) (55597857220 / 1000000000000), orderedInterval (28084597379 / 1000000000000) (28084597380 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1777679142528681 / 4000000000000) 0 (IntervalRat.scale (567 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29676884127 / 1000000000000) (-29676840054 / 1000000000000), orderedInterval (23522886281 / 1000000000000) (23522930355 / 1000000000000)))) (orderedInterval (5134891226 / 1000000000000) (5134894476 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1309430410522353 / 4000000000000) 0 (IntervalRat.scale (567 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (43578353584 / 1000000000000) (43578353602 / 1000000000000), orderedInterval (6689745415 / 1000000000000) (6689745433 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2243731326956469 / 4000000000000) 0 (IntervalRat.scale (567 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (19767906169 / 1000000000000) (19767907693 / 1000000000000), orderedInterval (-27296926331 / 1000000000000) (-27296924808 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1652722340195871 / 4000000000000) 0 (IntervalRat.scale (567 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-26016650162 / 1000000000000) (-26016640490 / 1000000000000), orderedInterval (29423872312 / 1000000000000) (29423881984 / 1000000000000)))) (orderedInterval (-1238492477 / 1000000000000) (-1238492179 / 1000000000000))) = true
  rfl'

theorem compactCertificate412_chunkChecks0_1 :
    compactCertificate412.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2535701086484433 / 4000000000000) 0 (IntervalRat.scale (567 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (3439695584 / 1000000000000) (3439695585 / 1000000000000), orderedInterval (31499974198 / 1000000000000) (31499974199 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1463987704866057 / 4000000000000) 0 (IntervalRat.scale (567 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (29460058420 / 1000000000000) (29460080185 / 1000000000000), orderedInterval (-29561726907 / 1000000000000) (-29561705142 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2597871872814813 / 4000000000000) 0 (IntervalRat.scale (567 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (1768153160 / 1000000000000) (1768153161 / 1000000000000), orderedInterval (-31259820496 / 1000000000000) (-31259820495 / 1000000000000)))) (orderedInterval (1822908861 / 1000000000000) (1822910586 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2427268890659697 / 4000000000000) 0 (IntervalRat.scale (567 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-30983627635 / 1000000000000) (-30983627617 / 1000000000000), orderedInterval (-9415202216 / 1000000000000) (-9415202198 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1732213612692801 / 4000000000000) 0 (IntervalRat.scale (567 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (11284033857 / 1000000000000) (11284033858 / 1000000000000), orderedInterval (36630437521 / 1000000000000) (36630437522 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1964145615782679 / 4000000000000) 0 (IntervalRat.scale (567 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (35533505131 / 1000000000000) (35533508437 / 1000000000000), orderedInterval (-5854351712 / 1000000000000) (-5854348406 / 1000000000000)))) (orderedInterval (1446580638 / 1000000000000) (1446580690 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1637499841965351 / 4000000000000) 0 (IntervalRat.scale (567 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (38781932160 / 1000000000000) (38781934773 / 1000000000000), orderedInterval (-7193166791 / 1000000000000) (-7193164178 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1446780770764371 / 4000000000000) 0 (IntervalRat.scale (567 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-39057925343 / 1000000000000) (-39057925342 / 1000000000000), orderedInterval (-15261927400 / 1000000000000) (-15261927399 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (419333458356729 / 800000000000) 0 (IntervalRat.scale (567 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-10498827134 / 1000000000000) (-10498827133 / 1000000000000), orderedInterval (-33221170069 / 1000000000000) (-33221170068 / 1000000000000)))) (orderedInterval (2414184774 / 1000000000000) (2414184832 / 1000000000000))) = true
  rfl'

theorem compactCertificate412_chunkChecks0_2 :
    compactCertificate412.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1159898414125563 / 4000000000000) 0 (IntervalRat.scale (567 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (46240025723 / 1000000000000) (46240026764 / 1000000000000), orderedInterval (-7648729736 / 1000000000000) (-7648728694 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (983258731177443 / 4000000000000) 0 (IntervalRat.scale (567 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (50884306560 / 1000000000000) (50884306636 / 1000000000000), orderedInterval (682769416 / 1000000000000) (682769493 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (615277659804129 / 4000000000000) 0 (IntervalRat.scale (567 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-39745827381 / 1000000000000) (-39745827380 / 1000000000000), orderedInterval (-50457584129 / 1000000000000) (-50457584128 / 1000000000000)))) (orderedInterval (-11567416531 / 1000000000000) (-11567416289 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (330898371763743 / 4000000000000) 0 (IntervalRat.scale (567 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (84859083858 / 1000000000000) (84859084782 / 1000000000000), orderedInterval (-22749484638 / 1000000000000) (-22749483714 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (898453448240229 / 4000000000000) 0 (IntervalRat.scale (567 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-38059356803 / 1000000000000) (-38059310142 / 1000000000000), orderedInterval (37310743886 / 1000000000000) (37310790547 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1226761372424133 / 4000000000000) 0 (IntervalRat.scale (567 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-17773460579 / 1000000000000) (-17773460109 / 1000000000000), orderedInterval (41979897293 / 1000000000000) (41979897763 / 1000000000000)))) (orderedInterval (658651270 / 1000000000000) (658652416 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (518722340195871 / 4000000000000) 0 (IntervalRat.scale (567 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-69788136933 / 1000000000000) (-69788136787 / 1000000000000), orderedInterval (6491383787 / 1000000000000) (6491383933 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2108577514292991 / 4000000000000) 0 (IntervalRat.scale (567 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (4917263041 / 1000000000000) (4917263042 / 1000000000000), orderedInterval (34397332183 / 1000000000000) (34397332184 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1408432059497169 / 4000000000000) 0 (IntervalRat.scale (567 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (36555143684 / 1000000000000) (36555143685 / 1000000000000), orderedInterval (21667775417 / 1000000000000) (21667775418 / 1000000000000)))) (orderedInterval (-7679694423 / 1000000000000) (-7679694343 / 1000000000000))) = true
  rfl'

theorem compactCertificate412_chunkChecks0 :
    compactCertificate412.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate412.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate412_chunkChecks0_0
    compactCertificate412_chunkChecks0_1 compactCertificate412_chunkChecks0_2

theorem compactCertificate412_chunkChecks1_0 :
    compactCertificate412.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (567 / 2) 1 (IntervalRat.scale (567 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (47367263701 / 1000000000000) (47367263783 / 1000000000000), orderedInterval (1298931886 / 1000000000000) (1298931968 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (835299267459867 / 4000000000000) 1 (IntervalRat.scale (567 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (42452937972 / 1000000000000) (42453037953 / 1000000000000), orderedInterval (-35405023118 / 1000000000000) (-35404923138 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (270118620790011 / 800000000000) 1 (IntervalRat.scale (567 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-32870109619 / 1000000000000) (-32870060810 / 1000000000000), orderedInterval (28421341015 / 1000000000000) (28421389824 / 1000000000000)))) (orderedInterval (2258188296 / 1000000000000) (2258192449 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (243738242978769 / 4000000000000) 1 (IntervalRat.scale (567 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-91729549767 / 1000000000000) (-91729542243 / 1000000000000), orderedInterval (45842247717 / 1000000000000) (45842255241 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (654715205260893 / 4000000000000) 1 (IntervalRat.scale (567 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (55597857219 / 1000000000000) (55597857220 / 1000000000000), orderedInterval (28084597379 / 1000000000000) (28084597380 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1777679142528681 / 4000000000000) 1 (IntervalRat.scale (567 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29676884127 / 1000000000000) (-29676840054 / 1000000000000), orderedInterval (23522886281 / 1000000000000) (23522930355 / 1000000000000)))) (orderedInterval (-2136303702 / 1000000000000) (-2136298734 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1309430410522353 / 4000000000000) 1 (IntervalRat.scale (567 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (43578353584 / 1000000000000) (43578353602 / 1000000000000), orderedInterval (6689745415 / 1000000000000) (6689745433 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2243731326956469 / 4000000000000) 1 (IntervalRat.scale (567 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (19767906169 / 1000000000000) (19767907693 / 1000000000000), orderedInterval (-27296926331 / 1000000000000) (-27296924808 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1652722340195871 / 4000000000000) 1 (IntervalRat.scale (567 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-26016650162 / 1000000000000) (-26016640490 / 1000000000000), orderedInterval (29423872312 / 1000000000000) (29423881984 / 1000000000000)))) (orderedInterval (2702275395 / 1000000000000) (2702275857 / 1000000000000))) = true
  rfl'

theorem compactCertificate412_chunkChecks1_1 :
    compactCertificate412.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2535701086484433 / 4000000000000) 1 (IntervalRat.scale (567 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (3439695584 / 1000000000000) (3439695585 / 1000000000000), orderedInterval (31499974198 / 1000000000000) (31499974199 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1463987704866057 / 4000000000000) 1 (IntervalRat.scale (567 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (29460058420 / 1000000000000) (29460080185 / 1000000000000), orderedInterval (-29561726907 / 1000000000000) (-29561705142 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2597871872814813 / 4000000000000) 1 (IntervalRat.scale (567 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (1768153160 / 1000000000000) (1768153161 / 1000000000000), orderedInterval (-31259820496 / 1000000000000) (-31259820495 / 1000000000000)))) (orderedInterval (-25523475100 / 1000000000000) (-25523472784 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2427268890659697 / 4000000000000) 1 (IntervalRat.scale (567 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-30983627635 / 1000000000000) (-30983627617 / 1000000000000), orderedInterval (-9415202216 / 1000000000000) (-9415202198 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1732213612692801 / 4000000000000) 1 (IntervalRat.scale (567 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (11284033857 / 1000000000000) (11284033858 / 1000000000000), orderedInterval (36630437521 / 1000000000000) (36630437522 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1964145615782679 / 4000000000000) 1 (IntervalRat.scale (567 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (35533505131 / 1000000000000) (35533508437 / 1000000000000), orderedInterval (-5854351712 / 1000000000000) (-5854348406 / 1000000000000)))) (orderedInterval (5706296638 / 1000000000000) (5706296723 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1637499841965351 / 4000000000000) 1 (IntervalRat.scale (567 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (38781932160 / 1000000000000) (38781934773 / 1000000000000), orderedInterval (-7193166791 / 1000000000000) (-7193164178 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1446780770764371 / 4000000000000) 1 (IntervalRat.scale (567 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-39057925343 / 1000000000000) (-39057925342 / 1000000000000), orderedInterval (-15261927400 / 1000000000000) (-15261927399 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (419333458356729 / 800000000000) 1 (IntervalRat.scale (567 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-10498827134 / 1000000000000) (-10498827133 / 1000000000000), orderedInterval (-33221170069 / 1000000000000) (-33221170068 / 1000000000000)))) (orderedInterval (-578329583 / 1000000000000) (-578329499 / 1000000000000))) = true
  rfl'

theorem compactCertificate412_chunkChecks1_2 :
    compactCertificate412.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1159898414125563 / 4000000000000) 1 (IntervalRat.scale (567 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (46240025723 / 1000000000000) (46240026764 / 1000000000000), orderedInterval (-7648729736 / 1000000000000) (-7648728694 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (983258731177443 / 4000000000000) 1 (IntervalRat.scale (567 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (50884306560 / 1000000000000) (50884306636 / 1000000000000), orderedInterval (682769416 / 1000000000000) (682769493 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (615277659804129 / 4000000000000) 1 (IntervalRat.scale (567 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-39745827381 / 1000000000000) (-39745827380 / 1000000000000), orderedInterval (-50457584129 / 1000000000000) (-50457584128 / 1000000000000)))) (orderedInterval (326133596 / 1000000000000) (326133836 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (330898371763743 / 4000000000000) 1 (IntervalRat.scale (567 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (84859083858 / 1000000000000) (84859084782 / 1000000000000), orderedInterval (-22749484638 / 1000000000000) (-22749483714 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (898453448240229 / 4000000000000) 1 (IntervalRat.scale (567 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-38059356803 / 1000000000000) (-38059310142 / 1000000000000), orderedInterval (37310743886 / 1000000000000) (37310790547 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1226761372424133 / 4000000000000) 1 (IntervalRat.scale (567 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-17773460579 / 1000000000000) (-17773460109 / 1000000000000), orderedInterval (41979897293 / 1000000000000) (41979897763 / 1000000000000)))) (orderedInterval (-4028534000 / 1000000000000) (-4028533086 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (518722340195871 / 4000000000000) 1 (IntervalRat.scale (567 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-69788136933 / 1000000000000) (-69788136787 / 1000000000000), orderedInterval (6491383787 / 1000000000000) (6491383933 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2108577514292991 / 4000000000000) 1 (IntervalRat.scale (567 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (4917263041 / 1000000000000) (4917263042 / 1000000000000), orderedInterval (34397332183 / 1000000000000) (34397332184 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1408432059497169 / 4000000000000) 1 (IntervalRat.scale (567 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (36555143684 / 1000000000000) (36555143685 / 1000000000000), orderedInterval (21667775417 / 1000000000000) (21667775418 / 1000000000000)))) (orderedInterval (-10237774304 / 1000000000000) (-10237774192 / 1000000000000))) = true
  rfl'

theorem compactCertificate412_chunkChecks1 :
    compactCertificate412.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate412.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate412_chunkChecks1_0
    compactCertificate412_chunkChecks1_1 compactCertificate412_chunkChecks1_2

theorem compactCertificate412_chunkChecks2_0 :
    compactCertificate412.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (567 / 2) 2 (IntervalRat.scale (567 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (47367263701 / 1000000000000) (47367263783 / 1000000000000), orderedInterval (1298931886 / 1000000000000) (1298931968 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (835299267459867 / 4000000000000) 2 (IntervalRat.scale (567 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (42452937972 / 1000000000000) (42453037953 / 1000000000000), orderedInterval (-35405023118 / 1000000000000) (-35404923138 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (270118620790011 / 800000000000) 2 (IntervalRat.scale (567 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-32870109619 / 1000000000000) (-32870060810 / 1000000000000), orderedInterval (28421341015 / 1000000000000) (28421389824 / 1000000000000)))) (orderedInterval (-16261284365 / 1000000000000) (-16261279724 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (243738242978769 / 4000000000000) 2 (IntervalRat.scale (567 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-91729549767 / 1000000000000) (-91729542243 / 1000000000000), orderedInterval (45842247717 / 1000000000000) (45842255241 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (654715205260893 / 4000000000000) 2 (IntervalRat.scale (567 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (55597857219 / 1000000000000) (55597857220 / 1000000000000), orderedInterval (28084597379 / 1000000000000) (28084597380 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1777679142528681 / 4000000000000) 2 (IntervalRat.scale (567 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29676884127 / 1000000000000) (-29676840054 / 1000000000000), orderedInterval (23522886281 / 1000000000000) (23522930355 / 1000000000000)))) (orderedInterval (-5899579689 / 1000000000000) (-5899571914 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1309430410522353 / 4000000000000) 2 (IntervalRat.scale (567 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (43578353584 / 1000000000000) (43578353602 / 1000000000000), orderedInterval (6689745415 / 1000000000000) (6689745433 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2243731326956469 / 4000000000000) 2 (IntervalRat.scale (567 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (19767906169 / 1000000000000) (19767907693 / 1000000000000), orderedInterval (-27296926331 / 1000000000000) (-27296924808 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1652722340195871 / 4000000000000) 2 (IntervalRat.scale (567 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-26016650162 / 1000000000000) (-26016640490 / 1000000000000), orderedInterval (29423872312 / 1000000000000) (29423881984 / 1000000000000)))) (orderedInterval (3713006499 / 1000000000000) (3713007231 / 1000000000000))) = true
  rfl'

theorem compactCertificate412_chunkChecks2_1 :
    compactCertificate412.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2535701086484433 / 4000000000000) 2 (IntervalRat.scale (567 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (3439695584 / 1000000000000) (3439695585 / 1000000000000), orderedInterval (31499974198 / 1000000000000) (31499974199 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1463987704866057 / 4000000000000) 2 (IntervalRat.scale (567 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (29460058420 / 1000000000000) (29460080185 / 1000000000000), orderedInterval (-29561726907 / 1000000000000) (-29561705142 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2597871872814813 / 4000000000000) 2 (IntervalRat.scale (567 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (1768153160 / 1000000000000) (1768153161 / 1000000000000), orderedInterval (-31259820496 / 1000000000000) (-31259820495 / 1000000000000)))) (orderedInterval (-1811074079 / 1000000000000) (-1811070883 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2427268890659697 / 4000000000000) 2 (IntervalRat.scale (567 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-30983627635 / 1000000000000) (-30983627617 / 1000000000000), orderedInterval (-9415202216 / 1000000000000) (-9415202198 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1732213612692801 / 4000000000000) 2 (IntervalRat.scale (567 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (11284033857 / 1000000000000) (11284033858 / 1000000000000), orderedInterval (36630437521 / 1000000000000) (36630437522 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1964145615782679 / 4000000000000) 2 (IntervalRat.scale (567 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (35533505131 / 1000000000000) (35533508437 / 1000000000000), orderedInterval (-5854351712 / 1000000000000) (-5854348406 / 1000000000000)))) (orderedInterval (-4533126894 / 1000000000000) (-4533126751 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1637499841965351 / 4000000000000) 2 (IntervalRat.scale (567 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (38781932160 / 1000000000000) (38781934773 / 1000000000000), orderedInterval (-7193166791 / 1000000000000) (-7193164178 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1446780770764371 / 4000000000000) 2 (IntervalRat.scale (567 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-39057925343 / 1000000000000) (-39057925342 / 1000000000000), orderedInterval (-15261927400 / 1000000000000) (-15261927399 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (419333458356729 / 800000000000) 2 (IntervalRat.scale (567 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-10498827134 / 1000000000000) (-10498827133 / 1000000000000), orderedInterval (-33221170069 / 1000000000000) (-33221170068 / 1000000000000)))) (orderedInterval (-3651051488 / 1000000000000) (-3651051366 / 1000000000000))) = true
  rfl'

theorem compactCertificate412_chunkChecks2_2 :
    compactCertificate412.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1159898414125563 / 4000000000000) 2 (IntervalRat.scale (567 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (46240025723 / 1000000000000) (46240026764 / 1000000000000), orderedInterval (-7648729736 / 1000000000000) (-7648728694 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (983258731177443 / 4000000000000) 2 (IntervalRat.scale (567 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (50884306560 / 1000000000000) (50884306636 / 1000000000000), orderedInterval (682769416 / 1000000000000) (682769493 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (615277659804129 / 4000000000000) 2 (IntervalRat.scale (567 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-39745827381 / 1000000000000) (-39745827380 / 1000000000000), orderedInterval (-50457584129 / 1000000000000) (-50457584128 / 1000000000000)))) (orderedInterval (10280013335 / 1000000000000) (10280013577 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (330898371763743 / 4000000000000) 2 (IntervalRat.scale (567 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (84859083858 / 1000000000000) (84859084782 / 1000000000000), orderedInterval (-22749484638 / 1000000000000) (-22749483714 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (898453448240229 / 4000000000000) 2 (IntervalRat.scale (567 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-38059356803 / 1000000000000) (-38059310142 / 1000000000000), orderedInterval (37310743886 / 1000000000000) (37310790547 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1226761372424133 / 4000000000000) 2 (IntervalRat.scale (567 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-17773460579 / 1000000000000) (-17773460109 / 1000000000000), orderedInterval (41979897293 / 1000000000000) (41979897763 / 1000000000000)))) (orderedInterval (-1988472875 / 1000000000000) (-1988472133 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (518722340195871 / 4000000000000) 2 (IntervalRat.scale (567 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-69788136933 / 1000000000000) (-69788136787 / 1000000000000), orderedInterval (6491383787 / 1000000000000) (6491383933 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2108577514292991 / 4000000000000) 2 (IntervalRat.scale (567 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (4917263041 / 1000000000000) (4917263042 / 1000000000000), orderedInterval (34397332183 / 1000000000000) (34397332184 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1408432059497169 / 4000000000000) 2 (IntervalRat.scale (567 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (36555143684 / 1000000000000) (36555143685 / 1000000000000), orderedInterval (21667775417 / 1000000000000) (21667775418 / 1000000000000)))) (orderedInterval (12088125592 / 1000000000000) (12088125756 / 1000000000000))) = true
  rfl'

theorem compactCertificate412_chunkChecks2 :
    compactCertificate412.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate412.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate412_chunkChecks2_0
    compactCertificate412_chunkChecks2_1 compactCertificate412_chunkChecks2_2

theorem compactCertificate412_chunkChecks3_0 :
    compactCertificate412.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (567 / 2) 3 (IntervalRat.scale (567 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (47367263701 / 1000000000000) (47367263783 / 1000000000000), orderedInterval (1298931886 / 1000000000000) (1298931968 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (835299267459867 / 4000000000000) 3 (IntervalRat.scale (567 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (42452937972 / 1000000000000) (42453037953 / 1000000000000), orderedInterval (-35405023118 / 1000000000000) (-35404923138 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (270118620790011 / 800000000000) 3 (IntervalRat.scale (567 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-32870109619 / 1000000000000) (-32870060810 / 1000000000000), orderedInterval (28421341015 / 1000000000000) (28421389824 / 1000000000000)))) (orderedInterval (-3143208324 / 1000000000000) (-3143203034 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (243738242978769 / 4000000000000) 3 (IntervalRat.scale (567 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-91729549767 / 1000000000000) (-91729542243 / 1000000000000), orderedInterval (45842247717 / 1000000000000) (45842255241 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (654715205260893 / 4000000000000) 3 (IntervalRat.scale (567 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (55597857219 / 1000000000000) (55597857220 / 1000000000000), orderedInterval (28084597379 / 1000000000000) (28084597380 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1777679142528681 / 4000000000000) 3 (IntervalRat.scale (567 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29676884127 / 1000000000000) (-29676840054 / 1000000000000), orderedInterval (23522886281 / 1000000000000) (23522930355 / 1000000000000)))) (orderedInterval (6270338097 / 1000000000000) (6270350276 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1309430410522353 / 4000000000000) 3 (IntervalRat.scale (567 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (43578353584 / 1000000000000) (43578353602 / 1000000000000), orderedInterval (6689745415 / 1000000000000) (6689745433 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2243731326956469 / 4000000000000) 3 (IntervalRat.scale (567 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (19767906169 / 1000000000000) (19767907693 / 1000000000000), orderedInterval (-27296926331 / 1000000000000) (-27296924808 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1652722340195871 / 4000000000000) 3 (IntervalRat.scale (567 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-26016650162 / 1000000000000) (-26016640490 / 1000000000000), orderedInterval (29423872312 / 1000000000000) (29423881984 / 1000000000000)))) (orderedInterval (-8736132712 / 1000000000000) (-8736131532 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate412_chunkChecks3_1 :
    compactCertificate412.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2535701086484433 / 4000000000000) 3 (IntervalRat.scale (567 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (3439695584 / 1000000000000) (3439695585 / 1000000000000), orderedInterval (31499974198 / 1000000000000) (31499974199 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1463987704866057 / 4000000000000) 3 (IntervalRat.scale (567 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (29460058420 / 1000000000000) (29460080185 / 1000000000000), orderedInterval (-29561726907 / 1000000000000) (-29561705142 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2597871872814813 / 4000000000000) 3 (IntervalRat.scale (567 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (1768153160 / 1000000000000) (1768153161 / 1000000000000), orderedInterval (-31259820496 / 1000000000000) (-31259820495 / 1000000000000)))) (orderedInterval (120724571355 / 1000000000000) (120724575932 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2427268890659697 / 4000000000000) 3 (IntervalRat.scale (567 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-30983627635 / 1000000000000) (-30983627617 / 1000000000000), orderedInterval (-9415202216 / 1000000000000) (-9415202198 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1732213612692801 / 4000000000000) 3 (IntervalRat.scale (567 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (11284033857 / 1000000000000) (11284033858 / 1000000000000), orderedInterval (36630437521 / 1000000000000) (36630437522 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1964145615782679 / 4000000000000) 3 (IntervalRat.scale (567 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (35533505131 / 1000000000000) (35533508437 / 1000000000000), orderedInterval (-5854351712 / 1000000000000) (-5854348406 / 1000000000000)))) (orderedInterval (-14150775519 / 1000000000000) (-14150775274 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1637499841965351 / 4000000000000) 3 (IntervalRat.scale (567 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (38781932160 / 1000000000000) (38781934773 / 1000000000000), orderedInterval (-7193166791 / 1000000000000) (-7193164178 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1446780770764371 / 4000000000000) 3 (IntervalRat.scale (567 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-39057925343 / 1000000000000) (-39057925342 / 1000000000000), orderedInterval (-15261927400 / 1000000000000) (-15261927399 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (419333458356729 / 800000000000) 3 (IntervalRat.scale (567 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-10498827134 / 1000000000000) (-10498827133 / 1000000000000), orderedInterval (-33221170069 / 1000000000000) (-33221170068 / 1000000000000)))) (orderedInterval (3825375292 / 1000000000000) (3825375473 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate412_chunkChecks3_2 :
    compactCertificate412.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1159898414125563 / 4000000000000) 3 (IntervalRat.scale (567 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (46240025723 / 1000000000000) (46240026764 / 1000000000000), orderedInterval (-7648729736 / 1000000000000) (-7648728694 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (983258731177443 / 4000000000000) 3 (IntervalRat.scale (567 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (50884306560 / 1000000000000) (50884306636 / 1000000000000), orderedInterval (682769416 / 1000000000000) (682769493 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (615277659804129 / 4000000000000) 3 (IntervalRat.scale (567 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-39745827381 / 1000000000000) (-39745827380 / 1000000000000), orderedInterval (-50457584129 / 1000000000000) (-50457584128 / 1000000000000)))) (orderedInterval (-1057384285 / 1000000000000) (-1057384042 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (330898371763743 / 4000000000000) 3 (IntervalRat.scale (567 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (84859083858 / 1000000000000) (84859084782 / 1000000000000), orderedInterval (-22749484638 / 1000000000000) (-22749483714 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (898453448240229 / 4000000000000) 3 (IntervalRat.scale (567 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-38059356803 / 1000000000000) (-38059310142 / 1000000000000), orderedInterval (37310743886 / 1000000000000) (37310790547 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1226761372424133 / 4000000000000) 3 (IntervalRat.scale (567 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-17773460579 / 1000000000000) (-17773460109 / 1000000000000), orderedInterval (41979897293 / 1000000000000) (41979897763 / 1000000000000)))) (orderedInterval (4490662686 / 1000000000000) (4490663293 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (518722340195871 / 4000000000000) 3 (IntervalRat.scale (567 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-69788136933 / 1000000000000) (-69788136787 / 1000000000000), orderedInterval (6491383787 / 1000000000000) (6491383933 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2108577514292991 / 4000000000000) 3 (IntervalRat.scale (567 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (4917263041 / 1000000000000) (4917263042 / 1000000000000), orderedInterval (34397332183 / 1000000000000) (34397332184 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1408432059497169 / 4000000000000) 3 (IntervalRat.scale (567 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (36555143684 / 1000000000000) (36555143685 / 1000000000000), orderedInterval (21667775417 / 1000000000000) (21667775418 / 1000000000000)))) (orderedInterval (25743056080 / 1000000000000) (25743056332 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate412_chunkChecks3 :
    compactCertificate412.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate412.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate412_chunkChecks3_0
    compactCertificate412_chunkChecks3_1 compactCertificate412_chunkChecks3_2

theorem compactCertificate412_chunkChecks4_0 :
    compactCertificate412.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (567 / 2) 4 (IntervalRat.scale (567 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (47367263701 / 1000000000000) (47367263783 / 1000000000000), orderedInterval (1298931886 / 1000000000000) (1298931968 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (835299267459867 / 4000000000000) 4 (IntervalRat.scale (567 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (42452937972 / 1000000000000) (42453037953 / 1000000000000), orderedInterval (-35405023118 / 1000000000000) (-35404923138 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (270118620790011 / 800000000000) 4 (IntervalRat.scale (567 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-32870109619 / 1000000000000) (-32870060810 / 1000000000000), orderedInterval (28421341015 / 1000000000000) (28421389824 / 1000000000000)))) (orderedInterval (15032132258 / 1000000000000) (15032138400 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (243738242978769 / 4000000000000) 4 (IntervalRat.scale (567 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-91729549767 / 1000000000000) (-91729542243 / 1000000000000), orderedInterval (45842247717 / 1000000000000) (45842255241 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (654715205260893 / 4000000000000) 4 (IntervalRat.scale (567 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (55597857219 / 1000000000000) (55597857220 / 1000000000000), orderedInterval (28084597379 / 1000000000000) (28084597380 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1777679142528681 / 4000000000000) 4 (IntervalRat.scale (567 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29676884127 / 1000000000000) (-29676840054 / 1000000000000), orderedInterval (23522886281 / 1000000000000) (23522930355 / 1000000000000)))) (orderedInterval (12923832733 / 1000000000000) (12923851863 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1309430410522353 / 4000000000000) 4 (IntervalRat.scale (567 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (43578353584 / 1000000000000) (43578353602 / 1000000000000), orderedInterval (6689745415 / 1000000000000) (6689745433 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2243731326956469 / 4000000000000) 4 (IntervalRat.scale (567 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (19767906169 / 1000000000000) (19767907693 / 1000000000000), orderedInterval (-27296926331 / 1000000000000) (-27296924808 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1652722340195871 / 4000000000000) 4 (IntervalRat.scale (567 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-26016650162 / 1000000000000) (-26016640490 / 1000000000000), orderedInterval (29423872312 / 1000000000000) (29423881984 / 1000000000000)))) (orderedInterval (-12119837355 / 1000000000000) (-12119835406 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate412_chunkChecks4_1 :
    compactCertificate412.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2535701086484433 / 4000000000000) 4 (IntervalRat.scale (567 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (3439695584 / 1000000000000) (3439695585 / 1000000000000), orderedInterval (31499974198 / 1000000000000) (31499974199 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1463987704866057 / 4000000000000) 4 (IntervalRat.scale (567 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (29460058420 / 1000000000000) (29460080185 / 1000000000000), orderedInterval (-29561726907 / 1000000000000) (-29561705142 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2597871872814813 / 4000000000000) 4 (IntervalRat.scale (567 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (1768153160 / 1000000000000) (1768153161 / 1000000000000), orderedInterval (-31259820496 / 1000000000000) (-31259820495 / 1000000000000)))) (orderedInterval (-3145170677 / 1000000000000) (-3145163736 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2427268890659697 / 4000000000000) 4 (IntervalRat.scale (567 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-30983627635 / 1000000000000) (-30983627617 / 1000000000000), orderedInterval (-9415202216 / 1000000000000) (-9415202198 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1732213612692801 / 4000000000000) 4 (IntervalRat.scale (567 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (11284033857 / 1000000000000) (11284033858 / 1000000000000), orderedInterval (36630437521 / 1000000000000) (36630437522 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1964145615782679 / 4000000000000) 4 (IntervalRat.scale (567 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (35533505131 / 1000000000000) (35533508437 / 1000000000000), orderedInterval (-5854351712 / 1000000000000) (-5854348406 / 1000000000000)))) (orderedInterval (16031834816 / 1000000000000) (16031835242 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1637499841965351 / 4000000000000) 4 (IntervalRat.scale (567 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (38781932160 / 1000000000000) (38781934773 / 1000000000000), orderedInterval (-7193166791 / 1000000000000) (-7193164178 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1446780770764371 / 4000000000000) 4 (IntervalRat.scale (567 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-39057925343 / 1000000000000) (-39057925342 / 1000000000000), orderedInterval (-15261927400 / 1000000000000) (-15261927399 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (419333458356729 / 800000000000) 4 (IntervalRat.scale (567 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-10498827134 / 1000000000000) (-10498827133 / 1000000000000), orderedInterval (-33221170069 / 1000000000000) (-33221170068 / 1000000000000)))) (orderedInterval (4700747587 / 1000000000000) (4700747862 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate412_chunkChecks4_2 :
    compactCertificate412.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1159898414125563 / 4000000000000) 4 (IntervalRat.scale (567 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (46240025723 / 1000000000000) (46240026764 / 1000000000000), orderedInterval (-7648729736 / 1000000000000) (-7648728694 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (983258731177443 / 4000000000000) 4 (IntervalRat.scale (567 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (50884306560 / 1000000000000) (50884306636 / 1000000000000), orderedInterval (682769416 / 1000000000000) (682769493 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (615277659804129 / 4000000000000) 4 (IntervalRat.scale (567 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-39745827381 / 1000000000000) (-39745827380 / 1000000000000), orderedInterval (-50457584129 / 1000000000000) (-50457584128 / 1000000000000)))) (orderedInterval (-9824746439 / 1000000000000) (-9824746193 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (330898371763743 / 4000000000000) 4 (IntervalRat.scale (567 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (84859083858 / 1000000000000) (84859084782 / 1000000000000), orderedInterval (-22749484638 / 1000000000000) (-22749483714 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (898453448240229 / 4000000000000) 4 (IntervalRat.scale (567 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-38059356803 / 1000000000000) (-38059310142 / 1000000000000), orderedInterval (37310743886 / 1000000000000) (37310790547 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1226761372424133 / 4000000000000) 4 (IntervalRat.scale (567 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-17773460579 / 1000000000000) (-17773460109 / 1000000000000), orderedInterval (41979897293 / 1000000000000) (41979897763 / 1000000000000)))) (orderedInterval (2162719719 / 1000000000000) (2162720223 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (518722340195871 / 4000000000000) 4 (IntervalRat.scale (567 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-69788136933 / 1000000000000) (-69788136787 / 1000000000000), orderedInterval (6491383787 / 1000000000000) (6491383933 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2108577514292991 / 4000000000000) 4 (IntervalRat.scale (567 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (4917263041 / 1000000000000) (4917263042 / 1000000000000), orderedInterval (34397332183 / 1000000000000) (34397332184 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1408432059497169 / 4000000000000) 4 (IntervalRat.scale (567 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (36555143684 / 1000000000000) (36555143685 / 1000000000000), orderedInterval (21667775417 / 1000000000000) (21667775418 / 1000000000000)))) (orderedInterval (-21305197851 / 1000000000000) (-21305197446 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate412_chunkChecks4 :
    compactCertificate412.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate412.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate412_chunkChecks4_0
    compactCertificate412_chunkChecks4_1 compactCertificate412_chunkChecks4_2

theorem compactCertificate412_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate412.chunkCheck r b = true :=
  compactCertificate412.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate412_chunkChecks0
    · exact compactCertificate412_chunkChecks1
    · exact compactCertificate412_chunkChecks2
    · exact compactCertificate412_chunkChecks3
    · exact compactCertificate412_chunkChecks4)

theorem compactCertificate412_coefficient0 :
    compactCertificate412.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate412_coefficient1 :
    compactCertificate412.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate412_coefficient2 :
    compactCertificate412.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate412_coefficient3 :
    compactCertificate412.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate412_coefficient4 :
    compactCertificate412.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate412_coefficients : ∀ r : Fin 5,
    compactCertificate412.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate412_coefficient0
  · exact compactCertificate412_coefficient1
  · exact compactCertificate412_coefficient2
  · exact compactCertificate412_coefficient3
  · exact compactCertificate412_coefficient4

theorem compactCertificate412_lower : (1 : ℚ) ≤ compactCertificate412.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate412, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate412_proves {t : ℝ} (ht : t ∈ compactCertificate412.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate412.proves compactCertificate412_states compactCertificate412_chunks
    compactCertificate412_coefficients compactCertificate412_lower ht

end Erdos232
