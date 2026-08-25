/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate521 : CompactCertificate where
  left := 392
  right := 393
  center := 785 / 2
  grid := fun i =>
    match i.val with
    | 0 => 125
    | 1 => 92
    | 2 => 149
    | 3 => 27
    | 4 => 72
    | 5 => 196
    | 6 => 144
    | 7 => 247
    | 8 => 182
    | 9 => 280
    | 10 => 161
    | 11 => 286
    | 12 => 268
    | 13 => 191
    | 14 => 217
    | 15 => 181
    | 16 => 159
    | 17 => 231
    | 18 => 128
    | 19 => 108
    | 20 => 68
    | 21 => 36
    | 22 => 99
    | 23 => 135
    | 24 => 57
    | 25 => 232
    | _ => 155
  point := fun i =>
    match i.val with
    | 0 => 785 / 2
    | 1 => 231290978820457 / 800000000000
    | 2 => 74794750377481 / 160000000000
    | 3 => 67490130771899 / 800000000000
    | 4 => 181287984525503 / 800000000000
    | 5 => 492232143522051 / 800000000000
    | 6 => 362575969051163 / 800000000000
    | 7 => 621280102878599 / 800000000000
    | 8 => 457632111835541 / 800000000000
    | 9 => 702125344934843 / 800000000000
    | 10 => 405372256902947 / 800000000000
    | 11 => 719340183477823 / 800000000000
    | 12 => 672100909759387 / 800000000000
    | 13 => 479642922738571 / 800000000000
    | 14 => 543863953576509 / 800000000000
    | 15 => 453417063824621 / 800000000000
    | 16 => 400607726649041 / 800000000000
    | 17 => 116111733619059 / 160000000000
    | 18 => 321171165816073 / 800000000000
    | 19 => 272260354135553 / 800000000000
    | 20 => 170367888164459 / 800000000000
    | 21 => 91624416872853 / 800000000000
    | 22 => 248778115297559 / 800000000000
    | 23 => 339685247743543 / 800000000000
    | 24 => 143632111835541 / 800000000000
    | 25 => 583856560395061 / 800000000000
    | _ => 389989124058299 / 800000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-22272534822 / 1000000000000) (-22272534821 / 1000000000000), orderedInterval (-33525999790 / 1000000000000) (-33525999789 / 1000000000000))
    | 1 => (orderedInterval (35931658257 / 1000000000000) (35931658258 / 1000000000000), orderedInterval (30118738156 / 1000000000000) (30118738157 / 1000000000000))
    | 2 => (orderedInterval (-5697679843 / 1000000000000) (-5697679842 / 1000000000000), orderedInterval (-36454655763 / 1000000000000) (-36454655762 / 1000000000000))
    | 3 => (orderedInterval (-27620741767 / 1000000000000) (-27620741766 / 1000000000000), orderedInterval (-82197865421 / 1000000000000) (-82197865420 / 1000000000000))
    | 4 => (orderedInterval (49403816719 / 1000000000000) (49403816720 / 1000000000000), orderedInterval (19089355182 / 1000000000000) (19089355183 / 1000000000000))
    | 5 => (orderedInterval (10216507483 / 1000000000000) (10216507484 / 1000000000000), orderedInterval (30492339711 / 1000000000000) (30492339712 / 1000000000000))
    | 6 => (orderedInterval (37440928419 / 1000000000000) (37440929105 / 1000000000000), orderedInterval (-1725231976 / 1000000000000) (-1725231290 / 1000000000000))
    | 7 => (orderedInterval (-28270996205 / 1000000000000) (-28270995788 / 1000000000000), orderedInterval (-4509818247 / 1000000000000) (-4509817830 / 1000000000000))
    | 8 => (orderedInterval (29027425424 / 1000000000000) (29027425425 / 1000000000000), orderedInterval (16415488492 / 1000000000000) (16415488493 / 1000000000000))
    | 9 => (orderedInterval (-25141140935 / 1000000000000) (-25141050429 / 1000000000000), orderedInterval (9672862240 / 1000000000000) (9672952746 / 1000000000000))
    | 10 => (orderedInterval (-35130990227 / 1000000000000) (-35130987603 / 1000000000000), orderedInterval (4744098294 / 1000000000000) (4744100918 / 1000000000000))
    | 11 => (orderedInterval (26459541764 / 1000000000000) (26459543436 / 1000000000000), orderedInterval (2795379062 / 1000000000000) (2795380733 / 1000000000000))
    | 12 => (orderedInterval (-23676173109 / 1000000000000) (-23676149030 / 1000000000000), orderedInterval (14057091566 / 1000000000000) (14057115644 / 1000000000000))
    | 13 => (orderedInterval (-9462908225 / 1000000000000) (-9462908224 / 1000000000000), orderedInterval (-31173457459 / 1000000000000) (-31173457458 / 1000000000000))
    | 14 => (orderedInterval (27415608342 / 1000000000000) (27415704122 / 1000000000000), orderedInterval (-13615110869 / 1000000000000) (-13615015089 / 1000000000000))
    | 15 => (orderedInterval (29427423360 / 1000000000000) (29427535218 / 1000000000000), orderedInterval (-16065414810 / 1000000000000) (-16065302952 / 1000000000000))
    | 16 => (orderedInterval (-31936804157 / 1000000000000) (-31936741833 / 1000000000000), orderedInterval (15885881710 / 1000000000000) (15885944034 / 1000000000000))
    | 17 => (orderedInterval (-20738407414 / 1000000000000) (-20738407413 / 1000000000000), orderedInterval (-21132099127 / 1000000000000) (-21132099126 / 1000000000000))
    | 18 => (orderedInterval (4972009699 / 1000000000000) (4972009700 / 1000000000000), orderedInterval (39503630260 / 1000000000000) (39503630261 / 1000000000000))
    | 19 => (orderedInterval (41930899652 / 1000000000000) (41930903298 / 1000000000000), orderedInterval (-10664354786 / 1000000000000) (-10664351140 / 1000000000000))
    | 20 => (orderedInterval (6348257987 / 1000000000000) (6348257988 / 1000000000000), orderedInterval (54290677010 / 1000000000000) (54290677012 / 1000000000000))
    | 21 => (orderedInterval (59500829455 / 1000000000000) (59500887019 / 1000000000000), orderedInterval (-45183601293 / 1000000000000) (-45183543729 / 1000000000000))
    | 22 => (orderedInterval (-30507643227 / 1000000000000) (-30507643226 / 1000000000000), orderedInterval (-33364612008 / 1000000000000) (-33364612007 / 1000000000000))
    | 23 => (orderedInterval (-37057990976 / 1000000000000) (-37057990971 / 1000000000000), orderedInterval (-11182282788 / 1000000000000) (-11182282784 / 1000000000000))
    | 24 => (orderedInterval (-56584774424 / 1000000000000) (-56584774423 / 1000000000000), orderedInterval (-18389320341 / 1000000000000) (-18389320340 / 1000000000000))
    | 25 => (orderedInterval (29027218931 / 1000000000000) (29027233456 / 1000000000000), orderedInterval (-5471138285 / 1000000000000) (-5471123761 / 1000000000000))
    | _ => (orderedInterval (-35048626730 / 1000000000000) (-35048626715 / 1000000000000), orderedInterval (-8768385346 / 1000000000000) (-8768385331 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-8827586124 / 1000000000000) (-8827586096 / 1000000000000)
      | 1 => orderedInterval (1377197199 / 1000000000000) (1377197247 / 1000000000000)
      | 2 => orderedInterval (1573526212 / 1000000000000) (1573526248 / 1000000000000)
      | 3 => orderedInterval (5625723509 / 1000000000000) (5625740178 / 1000000000000)
      | 4 => orderedInterval (-606151446 / 1000000000000) (-606150479 / 1000000000000)
      | 5 => orderedInterval (1636466618 / 1000000000000) (1636471514 / 1000000000000)
      | 6 => orderedInterval (-2961604845 / 1000000000000) (-2961604539 / 1000000000000)
      | 7 => orderedInterval (2433514380 / 1000000000000) (2433515491 / 1000000000000)
      | _ => orderedInterval (3872072087 / 1000000000000) (3872073382 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-15629594900 / 1000000000000) (-15629594868 / 1000000000000)
      | 1 => orderedInterval (-2804026727 / 1000000000000) (-2804026673 / 1000000000000)
      | 2 => orderedInterval (853429754 / 1000000000000) (853429818 / 1000000000000)
      | 3 => orderedInterval (-2479143138 / 1000000000000) (-2479106060 / 1000000000000)
      | 4 => orderedInterval (-4926770490 / 1000000000000) (-4926768644 / 1000000000000)
      | 5 => orderedInterval (-2428119686 / 1000000000000) (-2428113216 / 1000000000000)
      | 6 => orderedInterval (-4978250076 / 1000000000000) (-4978249805 / 1000000000000)
      | 7 => orderedInterval (1770264755 / 1000000000000) (1770265109 / 1000000000000)
      | _ => orderedInterval (2820720463 / 1000000000000) (2820722818 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (9160476382 / 1000000000000) (9160476418 / 1000000000000)
      | 1 => orderedInterval (1176826342 / 1000000000000) (1176826417 / 1000000000000)
      | 2 => orderedInterval (-4906017995 / 1000000000000) (-4906017876 / 1000000000000)
      | 3 => orderedInterval (-37732302631 / 1000000000000) (-37732219866 / 1000000000000)
      | 4 => orderedInterval (558457616 / 1000000000000) (558461193 / 1000000000000)
      | 5 => orderedInterval (-1862104421 / 1000000000000) (-1862095825 / 1000000000000)
      | 6 => orderedInterval (2567823176 / 1000000000000) (2567823419 / 1000000000000)
      | 7 => orderedInterval (-3669144455 / 1000000000000) (-3669144321 / 1000000000000)
      | _ => orderedInterval (-1910411236 / 1000000000000) (-1910406912 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (16766911280 / 1000000000000) (16766911322 / 1000000000000)
      | 1 => orderedInterval (8204600248 / 1000000000000) (8204600360 / 1000000000000)
      | 2 => orderedInterval (-2293121698 / 1000000000000) (-2293121474 / 1000000000000)
      | 3 => orderedInterval (13778318837 / 1000000000000) (13778503634 / 1000000000000)
      | 4 => orderedInterval (12635972433 / 1000000000000) (12635979437 / 1000000000000)
      | 5 => orderedInterval (5870997743 / 1000000000000) (5871009186 / 1000000000000)
      | 6 => orderedInterval (6076695682 / 1000000000000) (6076695901 / 1000000000000)
      | 7 => orderedInterval (-1472797402 / 1000000000000) (-1472797331 / 1000000000000)
      | _ => orderedInterval (-5999607091 / 1000000000000) (-5999599127 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-9487598368 / 1000000000000) (-9487598319 / 1000000000000)
      | 1 => orderedInterval (-4226749871 / 1000000000000) (-4226749699 / 1000000000000)
      | 2 => orderedInterval (16541024177 / 1000000000000) (16541024604 / 1000000000000)
      | 3 => orderedInterval (207982206622 / 1000000000000) (207982620048 / 1000000000000)
      | 4 => orderedInterval (2786904880 / 1000000000000) (2786918771 / 1000000000000)
      | 5 => orderedInterval (84709319 / 1000000000000) (84724640 / 1000000000000)
      | 6 => orderedInterval (-2224607651 / 1000000000000) (-2224607450 / 1000000000000)
      | 7 => orderedInterval (4161960106 / 1000000000000) (4161960160 / 1000000000000)
      | _ => orderedInterval (-12581716414 / 1000000000000) (-12581701676 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (4123157590 / 1000000000000) (4123182946 / 1000000000000)
    | 1 => orderedInterval (-27801490045 / 1000000000000) (-27801441521 / 1000000000000)
    | 2 => orderedInterval (-36616397222 / 1000000000000) (-36616297353 / 1000000000000)
    | 3 => orderedInterval (53567970032 / 1000000000000) (53568181908 / 1000000000000)
    | _ => orderedInterval (203036132800 / 1000000000000) (203036591079 / 1000000000000)

theorem compactCertificate521_stateChecks0 :
    compactCertificate521.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 125 12 (785 / 2)) (orderedInterval (-22272534822 / 1000000000000) (-22272534821 / 1000000000000), orderedInterval (-33525999790 / 1000000000000) (-33525999789 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 92 12 (231290978820457 / 800000000000)) (orderedInterval (35931658257 / 1000000000000) (35931658258 / 1000000000000), orderedInterval (30118738156 / 1000000000000) (30118738157 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 149 12 (74794750377481 / 160000000000)) (orderedInterval (-5697679843 / 1000000000000) (-5697679842 / 1000000000000), orderedInterval (-36454655763 / 1000000000000) (-36454655762 / 1000000000000))) = true
  rfl'

theorem compactCertificate521_stateChecks1 :
    compactCertificate521.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 27 12 (67490130771899 / 800000000000)) (orderedInterval (-27620741767 / 1000000000000) (-27620741766 / 1000000000000), orderedInterval (-82197865421 / 1000000000000) (-82197865420 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 72 12 (181287984525503 / 800000000000)) (orderedInterval (49403816719 / 1000000000000) (49403816720 / 1000000000000), orderedInterval (19089355182 / 1000000000000) (19089355183 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 196 12 (492232143522051 / 800000000000)) (orderedInterval (10216507483 / 1000000000000) (10216507484 / 1000000000000), orderedInterval (30492339711 / 1000000000000) (30492339712 / 1000000000000))) = true
  rfl'

theorem compactCertificate521_stateChecks2 :
    compactCertificate521.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 144 12 (362575969051163 / 800000000000)) (orderedInterval (37440928419 / 1000000000000) (37440929105 / 1000000000000), orderedInterval (-1725231976 / 1000000000000) (-1725231290 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 247 12 (621280102878599 / 800000000000)) (orderedInterval (-28270996205 / 1000000000000) (-28270995788 / 1000000000000), orderedInterval (-4509818247 / 1000000000000) (-4509817830 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 182 12 (457632111835541 / 800000000000)) (orderedInterval (29027425424 / 1000000000000) (29027425425 / 1000000000000), orderedInterval (16415488492 / 1000000000000) (16415488493 / 1000000000000))) = true
  rfl'

theorem compactCertificate521_stateChecks3 :
    compactCertificate521.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 280 12 (702125344934843 / 800000000000)) (orderedInterval (-25141140935 / 1000000000000) (-25141050429 / 1000000000000), orderedInterval (9672862240 / 1000000000000) (9672952746 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 161 12 (405372256902947 / 800000000000)) (orderedInterval (-35130990227 / 1000000000000) (-35130987603 / 1000000000000), orderedInterval (4744098294 / 1000000000000) (4744100918 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 286 12 (719340183477823 / 800000000000)) (orderedInterval (26459541764 / 1000000000000) (26459543436 / 1000000000000), orderedInterval (2795379062 / 1000000000000) (2795380733 / 1000000000000))) = true
  rfl'

theorem compactCertificate521_stateChecks4 :
    compactCertificate521.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 268 12 (672100909759387 / 800000000000)) (orderedInterval (-23676173109 / 1000000000000) (-23676149030 / 1000000000000), orderedInterval (14057091566 / 1000000000000) (14057115644 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 191 12 (479642922738571 / 800000000000)) (orderedInterval (-9462908225 / 1000000000000) (-9462908224 / 1000000000000), orderedInterval (-31173457459 / 1000000000000) (-31173457458 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 217 12 (543863953576509 / 800000000000)) (orderedInterval (27415608342 / 1000000000000) (27415704122 / 1000000000000), orderedInterval (-13615110869 / 1000000000000) (-13615015089 / 1000000000000))) = true
  rfl'

theorem compactCertificate521_stateChecks5 :
    compactCertificate521.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 181 12 (453417063824621 / 800000000000)) (orderedInterval (29427423360 / 1000000000000) (29427535218 / 1000000000000), orderedInterval (-16065414810 / 1000000000000) (-16065302952 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 159 12 (400607726649041 / 800000000000)) (orderedInterval (-31936804157 / 1000000000000) (-31936741833 / 1000000000000), orderedInterval (15885881710 / 1000000000000) (15885944034 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 231 12 (116111733619059 / 160000000000)) (orderedInterval (-20738407414 / 1000000000000) (-20738407413 / 1000000000000), orderedInterval (-21132099127 / 1000000000000) (-21132099126 / 1000000000000))) = true
  rfl'

theorem compactCertificate521_stateChecks6 :
    compactCertificate521.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 128 12 (321171165816073 / 800000000000)) (orderedInterval (4972009699 / 1000000000000) (4972009700 / 1000000000000), orderedInterval (39503630260 / 1000000000000) (39503630261 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 108 12 (272260354135553 / 800000000000)) (orderedInterval (41930899652 / 1000000000000) (41930903298 / 1000000000000), orderedInterval (-10664354786 / 1000000000000) (-10664351140 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (170367888164459 / 800000000000)) (orderedInterval (6348257987 / 1000000000000) (6348257988 / 1000000000000), orderedInterval (54290677010 / 1000000000000) (54290677012 / 1000000000000))) = true
  rfl'

theorem compactCertificate521_stateChecks7 :
    compactCertificate521.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 36 12 (91624416872853 / 800000000000)) (orderedInterval (59500829455 / 1000000000000) (59500887019 / 1000000000000), orderedInterval (-45183601293 / 1000000000000) (-45183543729 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 99 12 (248778115297559 / 800000000000)) (orderedInterval (-30507643227 / 1000000000000) (-30507643226 / 1000000000000), orderedInterval (-33364612008 / 1000000000000) (-33364612007 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 135 12 (339685247743543 / 800000000000)) (orderedInterval (-37057990976 / 1000000000000) (-37057990971 / 1000000000000), orderedInterval (-11182282788 / 1000000000000) (-11182282784 / 1000000000000))) = true
  rfl'

theorem compactCertificate521_stateChecks8 :
    compactCertificate521.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 57 12 (143632111835541 / 800000000000)) (orderedInterval (-56584774424 / 1000000000000) (-56584774423 / 1000000000000), orderedInterval (-18389320341 / 1000000000000) (-18389320340 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 232 12 (583856560395061 / 800000000000)) (orderedInterval (29027218931 / 1000000000000) (29027233456 / 1000000000000), orderedInterval (-5471138285 / 1000000000000) (-5471123761 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 155 12 (389989124058299 / 800000000000)) (orderedInterval (-35048626730 / 1000000000000) (-35048626715 / 1000000000000), orderedInterval (-8768385346 / 1000000000000) (-8768385331 / 1000000000000))) = true
  rfl'

theorem compactCertificate521_states : ∀ j,
    BesselStateValid (compactCertificate521.point j) (compactCertificate521.state j) :=
  compactCertificate521.statesValid_of_checks3 compactCertificate521_stateChecks0
    compactCertificate521_stateChecks1 compactCertificate521_stateChecks2
    compactCertificate521_stateChecks3 compactCertificate521_stateChecks4
    compactCertificate521_stateChecks5 compactCertificate521_stateChecks6
    compactCertificate521_stateChecks7 compactCertificate521_stateChecks8

theorem compactCertificate521_chunkChecks0_0 :
    compactCertificate521.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (785 / 2) 0 (IntervalRat.scale (785 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-22272534822 / 1000000000000) (-22272534821 / 1000000000000), orderedInterval (-33525999790 / 1000000000000) (-33525999789 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (231290978820457 / 800000000000) 0 (IntervalRat.scale (785 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (35931658257 / 1000000000000) (35931658258 / 1000000000000), orderedInterval (30118738156 / 1000000000000) (30118738157 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (74794750377481 / 160000000000) 0 (IntervalRat.scale (785 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-5697679843 / 1000000000000) (-5697679842 / 1000000000000), orderedInterval (-36454655763 / 1000000000000) (-36454655762 / 1000000000000)))) (orderedInterval (-8827586124 / 1000000000000) (-8827586096 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (67490130771899 / 800000000000) 0 (IntervalRat.scale (785 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-27620741767 / 1000000000000) (-27620741766 / 1000000000000), orderedInterval (-82197865421 / 1000000000000) (-82197865420 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (181287984525503 / 800000000000) 0 (IntervalRat.scale (785 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (49403816719 / 1000000000000) (49403816720 / 1000000000000), orderedInterval (19089355182 / 1000000000000) (19089355183 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (492232143522051 / 800000000000) 0 (IntervalRat.scale (785 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (10216507483 / 1000000000000) (10216507484 / 1000000000000), orderedInterval (30492339711 / 1000000000000) (30492339712 / 1000000000000)))) (orderedInterval (1377197199 / 1000000000000) (1377197247 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (362575969051163 / 800000000000) 0 (IntervalRat.scale (785 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (37440928419 / 1000000000000) (37440929105 / 1000000000000), orderedInterval (-1725231976 / 1000000000000) (-1725231290 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (621280102878599 / 800000000000) 0 (IntervalRat.scale (785 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-28270996205 / 1000000000000) (-28270995788 / 1000000000000), orderedInterval (-4509818247 / 1000000000000) (-4509817830 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (457632111835541 / 800000000000) 0 (IntervalRat.scale (785 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (29027425424 / 1000000000000) (29027425425 / 1000000000000), orderedInterval (16415488492 / 1000000000000) (16415488493 / 1000000000000)))) (orderedInterval (1573526212 / 1000000000000) (1573526248 / 1000000000000))) = true
  rfl'

theorem compactCertificate521_chunkChecks0_1 :
    compactCertificate521.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (702125344934843 / 800000000000) 0 (IntervalRat.scale (785 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-25141140935 / 1000000000000) (-25141050429 / 1000000000000), orderedInterval (9672862240 / 1000000000000) (9672952746 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (405372256902947 / 800000000000) 0 (IntervalRat.scale (785 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-35130990227 / 1000000000000) (-35130987603 / 1000000000000), orderedInterval (4744098294 / 1000000000000) (4744100918 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (719340183477823 / 800000000000) 0 (IntervalRat.scale (785 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (26459541764 / 1000000000000) (26459543436 / 1000000000000), orderedInterval (2795379062 / 1000000000000) (2795380733 / 1000000000000)))) (orderedInterval (5625723509 / 1000000000000) (5625740178 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (672100909759387 / 800000000000) 0 (IntervalRat.scale (785 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-23676173109 / 1000000000000) (-23676149030 / 1000000000000), orderedInterval (14057091566 / 1000000000000) (14057115644 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (479642922738571 / 800000000000) 0 (IntervalRat.scale (785 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-9462908225 / 1000000000000) (-9462908224 / 1000000000000), orderedInterval (-31173457459 / 1000000000000) (-31173457458 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (543863953576509 / 800000000000) 0 (IntervalRat.scale (785 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (27415608342 / 1000000000000) (27415704122 / 1000000000000), orderedInterval (-13615110869 / 1000000000000) (-13615015089 / 1000000000000)))) (orderedInterval (-606151446 / 1000000000000) (-606150479 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (453417063824621 / 800000000000) 0 (IntervalRat.scale (785 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (29427423360 / 1000000000000) (29427535218 / 1000000000000), orderedInterval (-16065414810 / 1000000000000) (-16065302952 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (400607726649041 / 800000000000) 0 (IntervalRat.scale (785 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-31936804157 / 1000000000000) (-31936741833 / 1000000000000), orderedInterval (15885881710 / 1000000000000) (15885944034 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (116111733619059 / 160000000000) 0 (IntervalRat.scale (785 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-20738407414 / 1000000000000) (-20738407413 / 1000000000000), orderedInterval (-21132099127 / 1000000000000) (-21132099126 / 1000000000000)))) (orderedInterval (1636466618 / 1000000000000) (1636471514 / 1000000000000))) = true
  rfl'

theorem compactCertificate521_chunkChecks0_2 :
    compactCertificate521.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (321171165816073 / 800000000000) 0 (IntervalRat.scale (785 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (4972009699 / 1000000000000) (4972009700 / 1000000000000), orderedInterval (39503630260 / 1000000000000) (39503630261 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (272260354135553 / 800000000000) 0 (IntervalRat.scale (785 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (41930899652 / 1000000000000) (41930903298 / 1000000000000), orderedInterval (-10664354786 / 1000000000000) (-10664351140 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (170367888164459 / 800000000000) 0 (IntervalRat.scale (785 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (6348257987 / 1000000000000) (6348257988 / 1000000000000), orderedInterval (54290677010 / 1000000000000) (54290677012 / 1000000000000)))) (orderedInterval (-2961604845 / 1000000000000) (-2961604539 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (91624416872853 / 800000000000) 0 (IntervalRat.scale (785 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (59500829455 / 1000000000000) (59500887019 / 1000000000000), orderedInterval (-45183601293 / 1000000000000) (-45183543729 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (248778115297559 / 800000000000) 0 (IntervalRat.scale (785 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-30507643227 / 1000000000000) (-30507643226 / 1000000000000), orderedInterval (-33364612008 / 1000000000000) (-33364612007 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (339685247743543 / 800000000000) 0 (IntervalRat.scale (785 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-37057990976 / 1000000000000) (-37057990971 / 1000000000000), orderedInterval (-11182282788 / 1000000000000) (-11182282784 / 1000000000000)))) (orderedInterval (2433514380 / 1000000000000) (2433515491 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (143632111835541 / 800000000000) 0 (IntervalRat.scale (785 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-56584774424 / 1000000000000) (-56584774423 / 1000000000000), orderedInterval (-18389320341 / 1000000000000) (-18389320340 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (583856560395061 / 800000000000) 0 (IntervalRat.scale (785 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (29027218931 / 1000000000000) (29027233456 / 1000000000000), orderedInterval (-5471138285 / 1000000000000) (-5471123761 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (389989124058299 / 800000000000) 0 (IntervalRat.scale (785 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-35048626730 / 1000000000000) (-35048626715 / 1000000000000), orderedInterval (-8768385346 / 1000000000000) (-8768385331 / 1000000000000)))) (orderedInterval (3872072087 / 1000000000000) (3872073382 / 1000000000000))) = true
  rfl'

theorem compactCertificate521_chunkChecks0 :
    compactCertificate521.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate521.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate521_chunkChecks0_0
    compactCertificate521_chunkChecks0_1 compactCertificate521_chunkChecks0_2

theorem compactCertificate521_chunkChecks1_0 :
    compactCertificate521.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (785 / 2) 1 (IntervalRat.scale (785 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-22272534822 / 1000000000000) (-22272534821 / 1000000000000), orderedInterval (-33525999790 / 1000000000000) (-33525999789 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (231290978820457 / 800000000000) 1 (IntervalRat.scale (785 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (35931658257 / 1000000000000) (35931658258 / 1000000000000), orderedInterval (30118738156 / 1000000000000) (30118738157 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (74794750377481 / 160000000000) 1 (IntervalRat.scale (785 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-5697679843 / 1000000000000) (-5697679842 / 1000000000000), orderedInterval (-36454655763 / 1000000000000) (-36454655762 / 1000000000000)))) (orderedInterval (-15629594900 / 1000000000000) (-15629594868 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (67490130771899 / 800000000000) 1 (IntervalRat.scale (785 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-27620741767 / 1000000000000) (-27620741766 / 1000000000000), orderedInterval (-82197865421 / 1000000000000) (-82197865420 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (181287984525503 / 800000000000) 1 (IntervalRat.scale (785 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (49403816719 / 1000000000000) (49403816720 / 1000000000000), orderedInterval (19089355182 / 1000000000000) (19089355183 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (492232143522051 / 800000000000) 1 (IntervalRat.scale (785 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (10216507483 / 1000000000000) (10216507484 / 1000000000000), orderedInterval (30492339711 / 1000000000000) (30492339712 / 1000000000000)))) (orderedInterval (-2804026727 / 1000000000000) (-2804026673 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (362575969051163 / 800000000000) 1 (IntervalRat.scale (785 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (37440928419 / 1000000000000) (37440929105 / 1000000000000), orderedInterval (-1725231976 / 1000000000000) (-1725231290 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (621280102878599 / 800000000000) 1 (IntervalRat.scale (785 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-28270996205 / 1000000000000) (-28270995788 / 1000000000000), orderedInterval (-4509818247 / 1000000000000) (-4509817830 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (457632111835541 / 800000000000) 1 (IntervalRat.scale (785 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (29027425424 / 1000000000000) (29027425425 / 1000000000000), orderedInterval (16415488492 / 1000000000000) (16415488493 / 1000000000000)))) (orderedInterval (853429754 / 1000000000000) (853429818 / 1000000000000))) = true
  rfl'

theorem compactCertificate521_chunkChecks1_1 :
    compactCertificate521.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (702125344934843 / 800000000000) 1 (IntervalRat.scale (785 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-25141140935 / 1000000000000) (-25141050429 / 1000000000000), orderedInterval (9672862240 / 1000000000000) (9672952746 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (405372256902947 / 800000000000) 1 (IntervalRat.scale (785 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-35130990227 / 1000000000000) (-35130987603 / 1000000000000), orderedInterval (4744098294 / 1000000000000) (4744100918 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (719340183477823 / 800000000000) 1 (IntervalRat.scale (785 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (26459541764 / 1000000000000) (26459543436 / 1000000000000), orderedInterval (2795379062 / 1000000000000) (2795380733 / 1000000000000)))) (orderedInterval (-2479143138 / 1000000000000) (-2479106060 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (672100909759387 / 800000000000) 1 (IntervalRat.scale (785 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-23676173109 / 1000000000000) (-23676149030 / 1000000000000), orderedInterval (14057091566 / 1000000000000) (14057115644 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (479642922738571 / 800000000000) 1 (IntervalRat.scale (785 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-9462908225 / 1000000000000) (-9462908224 / 1000000000000), orderedInterval (-31173457459 / 1000000000000) (-31173457458 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (543863953576509 / 800000000000) 1 (IntervalRat.scale (785 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (27415608342 / 1000000000000) (27415704122 / 1000000000000), orderedInterval (-13615110869 / 1000000000000) (-13615015089 / 1000000000000)))) (orderedInterval (-4926770490 / 1000000000000) (-4926768644 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (453417063824621 / 800000000000) 1 (IntervalRat.scale (785 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (29427423360 / 1000000000000) (29427535218 / 1000000000000), orderedInterval (-16065414810 / 1000000000000) (-16065302952 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (400607726649041 / 800000000000) 1 (IntervalRat.scale (785 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-31936804157 / 1000000000000) (-31936741833 / 1000000000000), orderedInterval (15885881710 / 1000000000000) (15885944034 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (116111733619059 / 160000000000) 1 (IntervalRat.scale (785 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-20738407414 / 1000000000000) (-20738407413 / 1000000000000), orderedInterval (-21132099127 / 1000000000000) (-21132099126 / 1000000000000)))) (orderedInterval (-2428119686 / 1000000000000) (-2428113216 / 1000000000000))) = true
  rfl'

theorem compactCertificate521_chunkChecks1_2 :
    compactCertificate521.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (321171165816073 / 800000000000) 1 (IntervalRat.scale (785 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (4972009699 / 1000000000000) (4972009700 / 1000000000000), orderedInterval (39503630260 / 1000000000000) (39503630261 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (272260354135553 / 800000000000) 1 (IntervalRat.scale (785 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (41930899652 / 1000000000000) (41930903298 / 1000000000000), orderedInterval (-10664354786 / 1000000000000) (-10664351140 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (170367888164459 / 800000000000) 1 (IntervalRat.scale (785 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (6348257987 / 1000000000000) (6348257988 / 1000000000000), orderedInterval (54290677010 / 1000000000000) (54290677012 / 1000000000000)))) (orderedInterval (-4978250076 / 1000000000000) (-4978249805 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (91624416872853 / 800000000000) 1 (IntervalRat.scale (785 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (59500829455 / 1000000000000) (59500887019 / 1000000000000), orderedInterval (-45183601293 / 1000000000000) (-45183543729 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (248778115297559 / 800000000000) 1 (IntervalRat.scale (785 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-30507643227 / 1000000000000) (-30507643226 / 1000000000000), orderedInterval (-33364612008 / 1000000000000) (-33364612007 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (339685247743543 / 800000000000) 1 (IntervalRat.scale (785 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-37057990976 / 1000000000000) (-37057990971 / 1000000000000), orderedInterval (-11182282788 / 1000000000000) (-11182282784 / 1000000000000)))) (orderedInterval (1770264755 / 1000000000000) (1770265109 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (143632111835541 / 800000000000) 1 (IntervalRat.scale (785 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-56584774424 / 1000000000000) (-56584774423 / 1000000000000), orderedInterval (-18389320341 / 1000000000000) (-18389320340 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (583856560395061 / 800000000000) 1 (IntervalRat.scale (785 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (29027218931 / 1000000000000) (29027233456 / 1000000000000), orderedInterval (-5471138285 / 1000000000000) (-5471123761 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (389989124058299 / 800000000000) 1 (IntervalRat.scale (785 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-35048626730 / 1000000000000) (-35048626715 / 1000000000000), orderedInterval (-8768385346 / 1000000000000) (-8768385331 / 1000000000000)))) (orderedInterval (2820720463 / 1000000000000) (2820722818 / 1000000000000))) = true
  rfl'

theorem compactCertificate521_chunkChecks1 :
    compactCertificate521.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate521.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate521_chunkChecks1_0
    compactCertificate521_chunkChecks1_1 compactCertificate521_chunkChecks1_2

theorem compactCertificate521_chunkChecks2_0 :
    compactCertificate521.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (785 / 2) 2 (IntervalRat.scale (785 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-22272534822 / 1000000000000) (-22272534821 / 1000000000000), orderedInterval (-33525999790 / 1000000000000) (-33525999789 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (231290978820457 / 800000000000) 2 (IntervalRat.scale (785 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (35931658257 / 1000000000000) (35931658258 / 1000000000000), orderedInterval (30118738156 / 1000000000000) (30118738157 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (74794750377481 / 160000000000) 2 (IntervalRat.scale (785 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-5697679843 / 1000000000000) (-5697679842 / 1000000000000), orderedInterval (-36454655763 / 1000000000000) (-36454655762 / 1000000000000)))) (orderedInterval (9160476382 / 1000000000000) (9160476418 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (67490130771899 / 800000000000) 2 (IntervalRat.scale (785 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-27620741767 / 1000000000000) (-27620741766 / 1000000000000), orderedInterval (-82197865421 / 1000000000000) (-82197865420 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (181287984525503 / 800000000000) 2 (IntervalRat.scale (785 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (49403816719 / 1000000000000) (49403816720 / 1000000000000), orderedInterval (19089355182 / 1000000000000) (19089355183 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (492232143522051 / 800000000000) 2 (IntervalRat.scale (785 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (10216507483 / 1000000000000) (10216507484 / 1000000000000), orderedInterval (30492339711 / 1000000000000) (30492339712 / 1000000000000)))) (orderedInterval (1176826342 / 1000000000000) (1176826417 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (362575969051163 / 800000000000) 2 (IntervalRat.scale (785 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (37440928419 / 1000000000000) (37440929105 / 1000000000000), orderedInterval (-1725231976 / 1000000000000) (-1725231290 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (621280102878599 / 800000000000) 2 (IntervalRat.scale (785 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-28270996205 / 1000000000000) (-28270995788 / 1000000000000), orderedInterval (-4509818247 / 1000000000000) (-4509817830 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (457632111835541 / 800000000000) 2 (IntervalRat.scale (785 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (29027425424 / 1000000000000) (29027425425 / 1000000000000), orderedInterval (16415488492 / 1000000000000) (16415488493 / 1000000000000)))) (orderedInterval (-4906017995 / 1000000000000) (-4906017876 / 1000000000000))) = true
  rfl'

theorem compactCertificate521_chunkChecks2_1 :
    compactCertificate521.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (702125344934843 / 800000000000) 2 (IntervalRat.scale (785 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-25141140935 / 1000000000000) (-25141050429 / 1000000000000), orderedInterval (9672862240 / 1000000000000) (9672952746 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (405372256902947 / 800000000000) 2 (IntervalRat.scale (785 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-35130990227 / 1000000000000) (-35130987603 / 1000000000000), orderedInterval (4744098294 / 1000000000000) (4744100918 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (719340183477823 / 800000000000) 2 (IntervalRat.scale (785 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (26459541764 / 1000000000000) (26459543436 / 1000000000000), orderedInterval (2795379062 / 1000000000000) (2795380733 / 1000000000000)))) (orderedInterval (-37732302631 / 1000000000000) (-37732219866 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (672100909759387 / 800000000000) 2 (IntervalRat.scale (785 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-23676173109 / 1000000000000) (-23676149030 / 1000000000000), orderedInterval (14057091566 / 1000000000000) (14057115644 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (479642922738571 / 800000000000) 2 (IntervalRat.scale (785 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-9462908225 / 1000000000000) (-9462908224 / 1000000000000), orderedInterval (-31173457459 / 1000000000000) (-31173457458 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (543863953576509 / 800000000000) 2 (IntervalRat.scale (785 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (27415608342 / 1000000000000) (27415704122 / 1000000000000), orderedInterval (-13615110869 / 1000000000000) (-13615015089 / 1000000000000)))) (orderedInterval (558457616 / 1000000000000) (558461193 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (453417063824621 / 800000000000) 2 (IntervalRat.scale (785 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (29427423360 / 1000000000000) (29427535218 / 1000000000000), orderedInterval (-16065414810 / 1000000000000) (-16065302952 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (400607726649041 / 800000000000) 2 (IntervalRat.scale (785 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-31936804157 / 1000000000000) (-31936741833 / 1000000000000), orderedInterval (15885881710 / 1000000000000) (15885944034 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (116111733619059 / 160000000000) 2 (IntervalRat.scale (785 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-20738407414 / 1000000000000) (-20738407413 / 1000000000000), orderedInterval (-21132099127 / 1000000000000) (-21132099126 / 1000000000000)))) (orderedInterval (-1862104421 / 1000000000000) (-1862095825 / 1000000000000))) = true
  rfl'

theorem compactCertificate521_chunkChecks2_2 :
    compactCertificate521.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (321171165816073 / 800000000000) 2 (IntervalRat.scale (785 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (4972009699 / 1000000000000) (4972009700 / 1000000000000), orderedInterval (39503630260 / 1000000000000) (39503630261 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (272260354135553 / 800000000000) 2 (IntervalRat.scale (785 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (41930899652 / 1000000000000) (41930903298 / 1000000000000), orderedInterval (-10664354786 / 1000000000000) (-10664351140 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (170367888164459 / 800000000000) 2 (IntervalRat.scale (785 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (6348257987 / 1000000000000) (6348257988 / 1000000000000), orderedInterval (54290677010 / 1000000000000) (54290677012 / 1000000000000)))) (orderedInterval (2567823176 / 1000000000000) (2567823419 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (91624416872853 / 800000000000) 2 (IntervalRat.scale (785 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (59500829455 / 1000000000000) (59500887019 / 1000000000000), orderedInterval (-45183601293 / 1000000000000) (-45183543729 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (248778115297559 / 800000000000) 2 (IntervalRat.scale (785 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-30507643227 / 1000000000000) (-30507643226 / 1000000000000), orderedInterval (-33364612008 / 1000000000000) (-33364612007 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (339685247743543 / 800000000000) 2 (IntervalRat.scale (785 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-37057990976 / 1000000000000) (-37057990971 / 1000000000000), orderedInterval (-11182282788 / 1000000000000) (-11182282784 / 1000000000000)))) (orderedInterval (-3669144455 / 1000000000000) (-3669144321 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (143632111835541 / 800000000000) 2 (IntervalRat.scale (785 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-56584774424 / 1000000000000) (-56584774423 / 1000000000000), orderedInterval (-18389320341 / 1000000000000) (-18389320340 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (583856560395061 / 800000000000) 2 (IntervalRat.scale (785 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (29027218931 / 1000000000000) (29027233456 / 1000000000000), orderedInterval (-5471138285 / 1000000000000) (-5471123761 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (389989124058299 / 800000000000) 2 (IntervalRat.scale (785 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-35048626730 / 1000000000000) (-35048626715 / 1000000000000), orderedInterval (-8768385346 / 1000000000000) (-8768385331 / 1000000000000)))) (orderedInterval (-1910411236 / 1000000000000) (-1910406912 / 1000000000000))) = true
  rfl'

theorem compactCertificate521_chunkChecks2 :
    compactCertificate521.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate521.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate521_chunkChecks2_0
    compactCertificate521_chunkChecks2_1 compactCertificate521_chunkChecks2_2

theorem compactCertificate521_chunkChecks3_0 :
    compactCertificate521.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (785 / 2) 3 (IntervalRat.scale (785 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-22272534822 / 1000000000000) (-22272534821 / 1000000000000), orderedInterval (-33525999790 / 1000000000000) (-33525999789 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (231290978820457 / 800000000000) 3 (IntervalRat.scale (785 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (35931658257 / 1000000000000) (35931658258 / 1000000000000), orderedInterval (30118738156 / 1000000000000) (30118738157 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (74794750377481 / 160000000000) 3 (IntervalRat.scale (785 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-5697679843 / 1000000000000) (-5697679842 / 1000000000000), orderedInterval (-36454655763 / 1000000000000) (-36454655762 / 1000000000000)))) (orderedInterval (16766911280 / 1000000000000) (16766911322 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (67490130771899 / 800000000000) 3 (IntervalRat.scale (785 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-27620741767 / 1000000000000) (-27620741766 / 1000000000000), orderedInterval (-82197865421 / 1000000000000) (-82197865420 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (181287984525503 / 800000000000) 3 (IntervalRat.scale (785 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (49403816719 / 1000000000000) (49403816720 / 1000000000000), orderedInterval (19089355182 / 1000000000000) (19089355183 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (492232143522051 / 800000000000) 3 (IntervalRat.scale (785 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (10216507483 / 1000000000000) (10216507484 / 1000000000000), orderedInterval (30492339711 / 1000000000000) (30492339712 / 1000000000000)))) (orderedInterval (8204600248 / 1000000000000) (8204600360 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (362575969051163 / 800000000000) 3 (IntervalRat.scale (785 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (37440928419 / 1000000000000) (37440929105 / 1000000000000), orderedInterval (-1725231976 / 1000000000000) (-1725231290 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (621280102878599 / 800000000000) 3 (IntervalRat.scale (785 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-28270996205 / 1000000000000) (-28270995788 / 1000000000000), orderedInterval (-4509818247 / 1000000000000) (-4509817830 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (457632111835541 / 800000000000) 3 (IntervalRat.scale (785 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (29027425424 / 1000000000000) (29027425425 / 1000000000000), orderedInterval (16415488492 / 1000000000000) (16415488493 / 1000000000000)))) (orderedInterval (-2293121698 / 1000000000000) (-2293121474 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate521_chunkChecks3_1 :
    compactCertificate521.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (702125344934843 / 800000000000) 3 (IntervalRat.scale (785 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-25141140935 / 1000000000000) (-25141050429 / 1000000000000), orderedInterval (9672862240 / 1000000000000) (9672952746 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (405372256902947 / 800000000000) 3 (IntervalRat.scale (785 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-35130990227 / 1000000000000) (-35130987603 / 1000000000000), orderedInterval (4744098294 / 1000000000000) (4744100918 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (719340183477823 / 800000000000) 3 (IntervalRat.scale (785 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (26459541764 / 1000000000000) (26459543436 / 1000000000000), orderedInterval (2795379062 / 1000000000000) (2795380733 / 1000000000000)))) (orderedInterval (13778318837 / 1000000000000) (13778503634 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (672100909759387 / 800000000000) 3 (IntervalRat.scale (785 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-23676173109 / 1000000000000) (-23676149030 / 1000000000000), orderedInterval (14057091566 / 1000000000000) (14057115644 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (479642922738571 / 800000000000) 3 (IntervalRat.scale (785 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-9462908225 / 1000000000000) (-9462908224 / 1000000000000), orderedInterval (-31173457459 / 1000000000000) (-31173457458 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (543863953576509 / 800000000000) 3 (IntervalRat.scale (785 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (27415608342 / 1000000000000) (27415704122 / 1000000000000), orderedInterval (-13615110869 / 1000000000000) (-13615015089 / 1000000000000)))) (orderedInterval (12635972433 / 1000000000000) (12635979437 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (453417063824621 / 800000000000) 3 (IntervalRat.scale (785 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (29427423360 / 1000000000000) (29427535218 / 1000000000000), orderedInterval (-16065414810 / 1000000000000) (-16065302952 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (400607726649041 / 800000000000) 3 (IntervalRat.scale (785 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-31936804157 / 1000000000000) (-31936741833 / 1000000000000), orderedInterval (15885881710 / 1000000000000) (15885944034 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (116111733619059 / 160000000000) 3 (IntervalRat.scale (785 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-20738407414 / 1000000000000) (-20738407413 / 1000000000000), orderedInterval (-21132099127 / 1000000000000) (-21132099126 / 1000000000000)))) (orderedInterval (5870997743 / 1000000000000) (5871009186 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate521_chunkChecks3_2 :
    compactCertificate521.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (321171165816073 / 800000000000) 3 (IntervalRat.scale (785 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (4972009699 / 1000000000000) (4972009700 / 1000000000000), orderedInterval (39503630260 / 1000000000000) (39503630261 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (272260354135553 / 800000000000) 3 (IntervalRat.scale (785 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (41930899652 / 1000000000000) (41930903298 / 1000000000000), orderedInterval (-10664354786 / 1000000000000) (-10664351140 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (170367888164459 / 800000000000) 3 (IntervalRat.scale (785 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (6348257987 / 1000000000000) (6348257988 / 1000000000000), orderedInterval (54290677010 / 1000000000000) (54290677012 / 1000000000000)))) (orderedInterval (6076695682 / 1000000000000) (6076695901 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (91624416872853 / 800000000000) 3 (IntervalRat.scale (785 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (59500829455 / 1000000000000) (59500887019 / 1000000000000), orderedInterval (-45183601293 / 1000000000000) (-45183543729 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (248778115297559 / 800000000000) 3 (IntervalRat.scale (785 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-30507643227 / 1000000000000) (-30507643226 / 1000000000000), orderedInterval (-33364612008 / 1000000000000) (-33364612007 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (339685247743543 / 800000000000) 3 (IntervalRat.scale (785 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-37057990976 / 1000000000000) (-37057990971 / 1000000000000), orderedInterval (-11182282788 / 1000000000000) (-11182282784 / 1000000000000)))) (orderedInterval (-1472797402 / 1000000000000) (-1472797331 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (143632111835541 / 800000000000) 3 (IntervalRat.scale (785 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-56584774424 / 1000000000000) (-56584774423 / 1000000000000), orderedInterval (-18389320341 / 1000000000000) (-18389320340 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (583856560395061 / 800000000000) 3 (IntervalRat.scale (785 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (29027218931 / 1000000000000) (29027233456 / 1000000000000), orderedInterval (-5471138285 / 1000000000000) (-5471123761 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (389989124058299 / 800000000000) 3 (IntervalRat.scale (785 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-35048626730 / 1000000000000) (-35048626715 / 1000000000000), orderedInterval (-8768385346 / 1000000000000) (-8768385331 / 1000000000000)))) (orderedInterval (-5999607091 / 1000000000000) (-5999599127 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate521_chunkChecks3 :
    compactCertificate521.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate521.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate521_chunkChecks3_0
    compactCertificate521_chunkChecks3_1 compactCertificate521_chunkChecks3_2

theorem compactCertificate521_chunkChecks4_0 :
    compactCertificate521.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (785 / 2) 4 (IntervalRat.scale (785 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-22272534822 / 1000000000000) (-22272534821 / 1000000000000), orderedInterval (-33525999790 / 1000000000000) (-33525999789 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (231290978820457 / 800000000000) 4 (IntervalRat.scale (785 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (35931658257 / 1000000000000) (35931658258 / 1000000000000), orderedInterval (30118738156 / 1000000000000) (30118738157 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (74794750377481 / 160000000000) 4 (IntervalRat.scale (785 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-5697679843 / 1000000000000) (-5697679842 / 1000000000000), orderedInterval (-36454655763 / 1000000000000) (-36454655762 / 1000000000000)))) (orderedInterval (-9487598368 / 1000000000000) (-9487598319 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (67490130771899 / 800000000000) 4 (IntervalRat.scale (785 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-27620741767 / 1000000000000) (-27620741766 / 1000000000000), orderedInterval (-82197865421 / 1000000000000) (-82197865420 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (181287984525503 / 800000000000) 4 (IntervalRat.scale (785 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (49403816719 / 1000000000000) (49403816720 / 1000000000000), orderedInterval (19089355182 / 1000000000000) (19089355183 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (492232143522051 / 800000000000) 4 (IntervalRat.scale (785 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (10216507483 / 1000000000000) (10216507484 / 1000000000000), orderedInterval (30492339711 / 1000000000000) (30492339712 / 1000000000000)))) (orderedInterval (-4226749871 / 1000000000000) (-4226749699 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (362575969051163 / 800000000000) 4 (IntervalRat.scale (785 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (37440928419 / 1000000000000) (37440929105 / 1000000000000), orderedInterval (-1725231976 / 1000000000000) (-1725231290 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (621280102878599 / 800000000000) 4 (IntervalRat.scale (785 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-28270996205 / 1000000000000) (-28270995788 / 1000000000000), orderedInterval (-4509818247 / 1000000000000) (-4509817830 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (457632111835541 / 800000000000) 4 (IntervalRat.scale (785 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (29027425424 / 1000000000000) (29027425425 / 1000000000000), orderedInterval (16415488492 / 1000000000000) (16415488493 / 1000000000000)))) (orderedInterval (16541024177 / 1000000000000) (16541024604 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate521_chunkChecks4_1 :
    compactCertificate521.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (702125344934843 / 800000000000) 4 (IntervalRat.scale (785 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-25141140935 / 1000000000000) (-25141050429 / 1000000000000), orderedInterval (9672862240 / 1000000000000) (9672952746 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (405372256902947 / 800000000000) 4 (IntervalRat.scale (785 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-35130990227 / 1000000000000) (-35130987603 / 1000000000000), orderedInterval (4744098294 / 1000000000000) (4744100918 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (719340183477823 / 800000000000) 4 (IntervalRat.scale (785 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (26459541764 / 1000000000000) (26459543436 / 1000000000000), orderedInterval (2795379062 / 1000000000000) (2795380733 / 1000000000000)))) (orderedInterval (207982206622 / 1000000000000) (207982620048 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (672100909759387 / 800000000000) 4 (IntervalRat.scale (785 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-23676173109 / 1000000000000) (-23676149030 / 1000000000000), orderedInterval (14057091566 / 1000000000000) (14057115644 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (479642922738571 / 800000000000) 4 (IntervalRat.scale (785 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-9462908225 / 1000000000000) (-9462908224 / 1000000000000), orderedInterval (-31173457459 / 1000000000000) (-31173457458 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (543863953576509 / 800000000000) 4 (IntervalRat.scale (785 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (27415608342 / 1000000000000) (27415704122 / 1000000000000), orderedInterval (-13615110869 / 1000000000000) (-13615015089 / 1000000000000)))) (orderedInterval (2786904880 / 1000000000000) (2786918771 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (453417063824621 / 800000000000) 4 (IntervalRat.scale (785 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (29427423360 / 1000000000000) (29427535218 / 1000000000000), orderedInterval (-16065414810 / 1000000000000) (-16065302952 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (400607726649041 / 800000000000) 4 (IntervalRat.scale (785 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-31936804157 / 1000000000000) (-31936741833 / 1000000000000), orderedInterval (15885881710 / 1000000000000) (15885944034 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (116111733619059 / 160000000000) 4 (IntervalRat.scale (785 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-20738407414 / 1000000000000) (-20738407413 / 1000000000000), orderedInterval (-21132099127 / 1000000000000) (-21132099126 / 1000000000000)))) (orderedInterval (84709319 / 1000000000000) (84724640 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate521_chunkChecks4_2 :
    compactCertificate521.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (321171165816073 / 800000000000) 4 (IntervalRat.scale (785 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (4972009699 / 1000000000000) (4972009700 / 1000000000000), orderedInterval (39503630260 / 1000000000000) (39503630261 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (272260354135553 / 800000000000) 4 (IntervalRat.scale (785 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (41930899652 / 1000000000000) (41930903298 / 1000000000000), orderedInterval (-10664354786 / 1000000000000) (-10664351140 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (170367888164459 / 800000000000) 4 (IntervalRat.scale (785 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (6348257987 / 1000000000000) (6348257988 / 1000000000000), orderedInterval (54290677010 / 1000000000000) (54290677012 / 1000000000000)))) (orderedInterval (-2224607651 / 1000000000000) (-2224607450 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (91624416872853 / 800000000000) 4 (IntervalRat.scale (785 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (59500829455 / 1000000000000) (59500887019 / 1000000000000), orderedInterval (-45183601293 / 1000000000000) (-45183543729 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (248778115297559 / 800000000000) 4 (IntervalRat.scale (785 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-30507643227 / 1000000000000) (-30507643226 / 1000000000000), orderedInterval (-33364612008 / 1000000000000) (-33364612007 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (339685247743543 / 800000000000) 4 (IntervalRat.scale (785 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-37057990976 / 1000000000000) (-37057990971 / 1000000000000), orderedInterval (-11182282788 / 1000000000000) (-11182282784 / 1000000000000)))) (orderedInterval (4161960106 / 1000000000000) (4161960160 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (143632111835541 / 800000000000) 4 (IntervalRat.scale (785 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-56584774424 / 1000000000000) (-56584774423 / 1000000000000), orderedInterval (-18389320341 / 1000000000000) (-18389320340 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (583856560395061 / 800000000000) 4 (IntervalRat.scale (785 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (29027218931 / 1000000000000) (29027233456 / 1000000000000), orderedInterval (-5471138285 / 1000000000000) (-5471123761 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (389989124058299 / 800000000000) 4 (IntervalRat.scale (785 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-35048626730 / 1000000000000) (-35048626715 / 1000000000000), orderedInterval (-8768385346 / 1000000000000) (-8768385331 / 1000000000000)))) (orderedInterval (-12581716414 / 1000000000000) (-12581701676 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate521_chunkChecks4 :
    compactCertificate521.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate521.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate521_chunkChecks4_0
    compactCertificate521_chunkChecks4_1 compactCertificate521_chunkChecks4_2

theorem compactCertificate521_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate521.chunkCheck r b = true :=
  compactCertificate521.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate521_chunkChecks0
    · exact compactCertificate521_chunkChecks1
    · exact compactCertificate521_chunkChecks2
    · exact compactCertificate521_chunkChecks3
    · exact compactCertificate521_chunkChecks4)

theorem compactCertificate521_coefficient0 :
    compactCertificate521.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate521_coefficient1 :
    compactCertificate521.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate521_coefficient2 :
    compactCertificate521.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate521_coefficient3 :
    compactCertificate521.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate521_coefficient4 :
    compactCertificate521.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate521_coefficients : ∀ r : Fin 5,
    compactCertificate521.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate521_coefficient0
  · exact compactCertificate521_coefficient1
  · exact compactCertificate521_coefficient2
  · exact compactCertificate521_coefficient3
  · exact compactCertificate521_coefficient4

theorem compactCertificate521_lower : (1 : ℚ) ≤ compactCertificate521.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate521, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate521_proves {t : ℝ} (ht : t ∈ compactCertificate521.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate521.proves compactCertificate521_states compactCertificate521_chunks
    compactCertificate521_coefficients compactCertificate521_lower ht

end Erdos232
