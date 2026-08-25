/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate283 : CompactCertificate where
  left := 157
  right := 158
  center := 315 / 2
  grid := fun i =>
    match i.val with
    | 0 => 50
    | 1 => 37
    | 2 => 60
    | 3 => 11
    | 4 => 29
    | 5 => 79
    | 6 => 58
    | 7 => 99
    | 8 => 73
    | 9 => 112
    | 10 => 65
    | 11 => 115
    | 12 => 107
    | 13 => 77
    | 14 => 87
    | 15 => 72
    | 16 => 64
    | 17 => 93
    | 18 => 51
    | 19 => 43
    | 20 => 27
    | 21 => 15
    | 22 => 40
    | 23 => 54
    | 24 => 23
    | 25 => 93
    | _ => 62
  point := fun i =>
    match i.val with
    | 0 => 315 / 2
    | 1 => 92811029717763 / 800000000000
    | 2 => 30013180087779 / 160000000000
    | 3 => 27082026997641 / 800000000000
    | 4 => 72746133917877 / 800000000000
    | 5 => 197519904725409 / 800000000000
    | 6 => 145492267835817 / 800000000000
    | 7 => 249303480772941 / 800000000000
    | 8 => 183635815577319 / 800000000000
    | 9 => 281744565164937 / 800000000000
    | 10 => 162665300540673 / 800000000000
    | 11 => 288652430312757 / 800000000000
    | 12 => 269696543406633 / 800000000000
    | 13 => 192468179188089 / 800000000000
    | 14 => 218238401753631 / 800000000000
    | 15 => 181944426885039 / 800000000000
    | 16 => 160753418973819 / 800000000000
    | 17 => 46592606484081 / 160000000000
    | 18 => 128877601569507 / 800000000000
    | 19 => 109250970130827 / 800000000000
    | 20 => 68364184422681 / 800000000000
    | 21 => 36766485751527 / 800000000000
    | 22 => 99828160915581 / 800000000000
    | 23 => 136306819158237 / 800000000000
    | 24 => 57635815577319 / 800000000000
    | 25 => 234286390476999 / 800000000000
    | _ => 156492451055241 / 800000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (59369872127 / 1000000000000) (59369872128 / 1000000000000), orderedInterval (22554292657 / 1000000000000) (22554292658 / 1000000000000))
    | 1 => (orderedInterval (-39297170772 / 1000000000000) (-39297170771 / 1000000000000), orderedInterval (-62625574406 / 1000000000000) (-62625574405 / 1000000000000))
    | 2 => (orderedInterval (-7462575510 / 1000000000000) (-7462575486 / 1000000000000), orderedInterval (57796496037 / 1000000000000) (57796496061 / 1000000000000))
    | 3 => (orderedInterval (-10510274855 / 1000000000000) (-10510274851 / 1000000000000), orderedInterval (-136582627944 / 1000000000000) (-136582627941 / 1000000000000))
    | 4 => (orderedInterval (-47967160115 / 1000000000000) (-47967160114 / 1000000000000), orderedInterval (-68294186224 / 1000000000000) (-68294186223 / 1000000000000))
    | 5 => (orderedInterval (24391105867 / 1000000000000) (24391108082 / 1000000000000), orderedInterval (-44586232968 / 1000000000000) (-44586230753 / 1000000000000))
    | 6 => (orderedInterval (25075975170 / 1000000000000) (25075975171 / 1000000000000), orderedInterval (53519349875 / 1000000000000) (53519349876 / 1000000000000))
    | 7 => (orderedInterval (-44514712048 / 1000000000000) (-44514712036 / 1000000000000), orderedInterval (-7758827868 / 1000000000000) (-7758827856 / 1000000000000))
    | 8 => (orderedInterval (-44124484184 / 1000000000000) (-44124484183 / 1000000000000), orderedInterval (-28651558332 / 1000000000000) (-28651558331 / 1000000000000))
    | 9 => (orderedInterval (38032128644 / 1000000000000) (38032128645 / 1000000000000), orderedInterval (18951451532 / 1000000000000) (18951451533 / 1000000000000))
    | 10 => (orderedInterval (4868245263 / 1000000000000) (4868245274 / 1000000000000), orderedInterval (-55754708041 / 1000000000000) (-55754708029 / 1000000000000))
    | 11 => (orderedInterval (-13110916728 / 1000000000000) (-13110916727 / 1000000000000), orderedInterval (-39887927126 / 1000000000000) (-39887927125 / 1000000000000))
    | 12 => (orderedInterval (-42718240981 / 1000000000000) (-42718239202 / 1000000000000), orderedInterval (8035384554 / 1000000000000) (8035386333 / 1000000000000))
    | 13 => (orderedInterval (26117165604 / 1000000000000) (26117168852 / 1000000000000), orderedInterval (-44371616251 / 1000000000000) (-44371613003 / 1000000000000))
    | 14 => (orderedInterval (-12623466169 / 1000000000000) (-12623466168 / 1000000000000), orderedInterval (-46606454183 / 1000000000000) (-46606454182 / 1000000000000))
    | 15 => (orderedInterval (47642128802 / 1000000000000) (47642144773 / 1000000000000), orderedInterval (-23113570676 / 1000000000000) (-23113554704 / 1000000000000))
    | 16 => (orderedInterval (34715266924 / 1000000000000) (34715266925 / 1000000000000), orderedInterval (44219746304 / 1000000000000) (44219746305 / 1000000000000))
    | 17 => (orderedInterval (8341216993 / 1000000000000) (8341217017 / 1000000000000), orderedInterval (-46020766393 / 1000000000000) (-46020766369 / 1000000000000))
    | 18 => (orderedInterval (-62610843869 / 1000000000000) (-62610843687 / 1000000000000), orderedInterval (5819505110 / 1000000000000) (5819505293 / 1000000000000))
    | 19 => (orderedInterval (-52705104800 / 1000000000000) (-52705013993 / 1000000000000), orderedInterval (43596555739 / 1000000000000) (43596646545 / 1000000000000))
    | 20 => (orderedInterval (-85281333074 / 1000000000000) (-85281333071 / 1000000000000), orderedInterval (-12794601116 / 1000000000000) (-12794601113 / 1000000000000))
    | 21 => (orderedInterval (43993297853 / 1000000000000) (43993299656 / 1000000000000), orderedInterval (-109645209406 / 1000000000000) (-109645207602 / 1000000000000))
    | 22 => (orderedInterval (-6711884888 / 1000000000000) (-6711884865 / 1000000000000), orderedInterval (71137481585 / 1000000000000) (71137481608 / 1000000000000))
    | 23 => (orderedInterval (61053701346 / 1000000000000) (61053701373 / 1000000000000), orderedInterval (2791078509 / 1000000000000) (2791078536 / 1000000000000))
    | 24 => (orderedInterval (-50868591573 / 1000000000000) (-50868591572 / 1000000000000), orderedInterval (-78697101513 / 1000000000000) (-78697101512 / 1000000000000))
    | 25 => (orderedInterval (-46409707824 / 1000000000000) (-46409707791 / 1000000000000), orderedInterval (-4387670485 / 1000000000000) (-4387670452 / 1000000000000))
    | _ => (orderedInterval (56974093396 / 1000000000000) (56974093532 / 1000000000000), orderedInterval (-3041391938 / 1000000000000) (-3041391802 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (22728053111 / 1000000000000) (22728053124 / 1000000000000)
      | 1 => orderedInterval (-3371290863 / 1000000000000) (-3371290686 / 1000000000000)
      | 2 => orderedInterval (306610093 / 1000000000000) (306610103 / 1000000000000)
      | 3 => orderedInterval (-8260947241 / 1000000000000) (-8260947177 / 1000000000000)
      | 4 => orderedInterval (3304792078 / 1000000000000) (3304792436 / 1000000000000)
      | 5 => orderedInterval (-1222915691 / 1000000000000) (-1222915490 / 1000000000000)
      | 6 => orderedInterval (10217745236 / 1000000000000) (10217750445 / 1000000000000)
      | 7 => orderedInterval (-5339156512 / 1000000000000) (-5339156457 / 1000000000000)
      | _ => orderedInterval (-7218671191 / 1000000000000) (-7218671119 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (12549242968 / 1000000000000) (12549242983 / 1000000000000)
      | 1 => orderedInterval (3847605486 / 1000000000000) (3847605755 / 1000000000000)
      | 2 => orderedInterval (-535692735 / 1000000000000) (-535692718 / 1000000000000)
      | 3 => orderedInterval (-25852942459 / 1000000000000) (-25852942327 / 1000000000000)
      | 4 => orderedInterval (-6311341453 / 1000000000000) (-6311340884 / 1000000000000)
      | 5 => orderedInterval (-5792542008 / 1000000000000) (-5792541718 / 1000000000000)
      | 6 => orderedInterval (-3317301852 / 1000000000000) (-3317297329 / 1000000000000)
      | 7 => orderedInterval (-919287037 / 1000000000000) (-919287007 / 1000000000000)
      | _ => orderedInterval (1155851893 / 1000000000000) (1155851992 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-22791971286 / 1000000000000) (-22791971269 / 1000000000000)
      | 1 => orderedInterval (4815159029 / 1000000000000) (4815159448 / 1000000000000)
      | 2 => orderedInterval (-3106602648 / 1000000000000) (-3106602618 / 1000000000000)
      | 3 => orderedInterval (43133775095 / 1000000000000) (43133775376 / 1000000000000)
      | 4 => orderedInterval (-9447491776 / 1000000000000) (-9447490857 / 1000000000000)
      | 5 => orderedInterval (1393234950 / 1000000000000) (1393235372 / 1000000000000)
      | 6 => orderedInterval (-11877842601 / 1000000000000) (-11877838643 / 1000000000000)
      | 7 => orderedInterval (5455316141 / 1000000000000) (5455316164 / 1000000000000)
      | _ => orderedInterval (3485118712 / 1000000000000) (3485118852 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-14291030163 / 1000000000000) (-14291030143 / 1000000000000)
      | 1 => orderedInterval (-11775598061 / 1000000000000) (-11775597407 / 1000000000000)
      | 2 => orderedInterval (309630299 / 1000000000000) (309630352 / 1000000000000)
      | 3 => orderedInterval (114436931052 / 1000000000000) (114436931666 / 1000000000000)
      | 4 => orderedInterval (15211913622 / 1000000000000) (15211915123 / 1000000000000)
      | 5 => orderedInterval (13497197189 / 1000000000000) (13497197802 / 1000000000000)
      | 6 => orderedInterval (2746068533 / 1000000000000) (2746071973 / 1000000000000)
      | 7 => orderedInterval (988471777 / 1000000000000) (988471798 / 1000000000000)
      | _ => orderedInterval (-3366098969 / 1000000000000) (-3366098763 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (22723778071 / 1000000000000) (22723778094 / 1000000000000)
      | 1 => orderedInterval (-10515893002 / 1000000000000) (-10515891974 / 1000000000000)
      | 2 => orderedInterval (16227472957 / 1000000000000) (16227473056 / 1000000000000)
      | 3 => orderedInterval (-220731098843 / 1000000000000) (-220731097483 / 1000000000000)
      | 4 => orderedInterval (30015274714 / 1000000000000) (30015277227 / 1000000000000)
      | 5 => orderedInterval (-547131692 / 1000000000000) (-547130796 / 1000000000000)
      | 6 => orderedInterval (12367497889 / 1000000000000) (12367500902 / 1000000000000)
      | 7 => orderedInterval (-6366616068 / 1000000000000) (-6366616046 / 1000000000000)
      | _ => orderedInterval (19752089338 / 1000000000000) (19752089657 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (11144219020 / 1000000000000) (11144225179 / 1000000000000)
    | 1 => orderedInterval (-25176407197 / 1000000000000) (-25176401253 / 1000000000000)
    | 2 => orderedInterval (11058695616 / 1000000000000) (11058701825 / 1000000000000)
    | 3 => orderedInterval (117757485279 / 1000000000000) (117757492401 / 1000000000000)
    | _ => orderedInterval (-137074626636 / 1000000000000) (-137074617363 / 1000000000000)

theorem compactCertificate283_stateChecks0 :
    compactCertificate283.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 50 12 (315 / 2)) (orderedInterval (59369872127 / 1000000000000) (59369872128 / 1000000000000), orderedInterval (22554292657 / 1000000000000) (22554292658 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (92811029717763 / 800000000000)) (orderedInterval (-39297170772 / 1000000000000) (-39297170771 / 1000000000000), orderedInterval (-62625574406 / 1000000000000) (-62625574405 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 60 12 (30013180087779 / 160000000000)) (orderedInterval (-7462575510 / 1000000000000) (-7462575486 / 1000000000000), orderedInterval (57796496037 / 1000000000000) (57796496061 / 1000000000000))) = true
  rfl'

theorem compactCertificate283_stateChecks1 :
    compactCertificate283.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 11 12 (27082026997641 / 800000000000)) (orderedInterval (-10510274855 / 1000000000000) (-10510274851 / 1000000000000), orderedInterval (-136582627944 / 1000000000000) (-136582627941 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 29 12 (72746133917877 / 800000000000)) (orderedInterval (-47967160115 / 1000000000000) (-47967160114 / 1000000000000), orderedInterval (-68294186224 / 1000000000000) (-68294186223 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 79 12 (197519904725409 / 800000000000)) (orderedInterval (24391105867 / 1000000000000) (24391108082 / 1000000000000), orderedInterval (-44586232968 / 1000000000000) (-44586230753 / 1000000000000))) = true
  rfl'

theorem compactCertificate283_stateChecks2 :
    compactCertificate283.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (145492267835817 / 800000000000)) (orderedInterval (25075975170 / 1000000000000) (25075975171 / 1000000000000), orderedInterval (53519349875 / 1000000000000) (53519349876 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 99 12 (249303480772941 / 800000000000)) (orderedInterval (-44514712048 / 1000000000000) (-44514712036 / 1000000000000), orderedInterval (-7758827868 / 1000000000000) (-7758827856 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 73 12 (183635815577319 / 800000000000)) (orderedInterval (-44124484184 / 1000000000000) (-44124484183 / 1000000000000), orderedInterval (-28651558332 / 1000000000000) (-28651558331 / 1000000000000))) = true
  rfl'

theorem compactCertificate283_stateChecks3 :
    compactCertificate283.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 112 12 (281744565164937 / 800000000000)) (orderedInterval (38032128644 / 1000000000000) (38032128645 / 1000000000000), orderedInterval (18951451532 / 1000000000000) (18951451533 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 65 12 (162665300540673 / 800000000000)) (orderedInterval (4868245263 / 1000000000000) (4868245274 / 1000000000000), orderedInterval (-55754708041 / 1000000000000) (-55754708029 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 115 12 (288652430312757 / 800000000000)) (orderedInterval (-13110916728 / 1000000000000) (-13110916727 / 1000000000000), orderedInterval (-39887927126 / 1000000000000) (-39887927125 / 1000000000000))) = true
  rfl'

theorem compactCertificate283_stateChecks4 :
    compactCertificate283.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 107 12 (269696543406633 / 800000000000)) (orderedInterval (-42718240981 / 1000000000000) (-42718239202 / 1000000000000), orderedInterval (8035384554 / 1000000000000) (8035386333 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 77 12 (192468179188089 / 800000000000)) (orderedInterval (26117165604 / 1000000000000) (26117168852 / 1000000000000), orderedInterval (-44371616251 / 1000000000000) (-44371613003 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 87 12 (218238401753631 / 800000000000)) (orderedInterval (-12623466169 / 1000000000000) (-12623466168 / 1000000000000), orderedInterval (-46606454183 / 1000000000000) (-46606454182 / 1000000000000))) = true
  rfl'

theorem compactCertificate283_stateChecks5 :
    compactCertificate283.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 72 12 (181944426885039 / 800000000000)) (orderedInterval (47642128802 / 1000000000000) (47642144773 / 1000000000000), orderedInterval (-23113570676 / 1000000000000) (-23113554704 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (160753418973819 / 800000000000)) (orderedInterval (34715266924 / 1000000000000) (34715266925 / 1000000000000), orderedInterval (44219746304 / 1000000000000) (44219746305 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 93 12 (46592606484081 / 160000000000)) (orderedInterval (8341216993 / 1000000000000) (8341217017 / 1000000000000), orderedInterval (-46020766393 / 1000000000000) (-46020766369 / 1000000000000))) = true
  rfl'

theorem compactCertificate283_stateChecks6 :
    compactCertificate283.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (128877601569507 / 800000000000)) (orderedInterval (-62610843869 / 1000000000000) (-62610843687 / 1000000000000), orderedInterval (5819505110 / 1000000000000) (5819505293 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (109250970130827 / 800000000000)) (orderedInterval (-52705104800 / 1000000000000) (-52705013993 / 1000000000000), orderedInterval (43596555739 / 1000000000000) (43596646545 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 27 12 (68364184422681 / 800000000000)) (orderedInterval (-85281333074 / 1000000000000) (-85281333071 / 1000000000000), orderedInterval (-12794601116 / 1000000000000) (-12794601113 / 1000000000000))) = true
  rfl'

theorem compactCertificate283_stateChecks7 :
    compactCertificate283.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 15 12 (36766485751527 / 800000000000)) (orderedInterval (43993297853 / 1000000000000) (43993299656 / 1000000000000), orderedInterval (-109645209406 / 1000000000000) (-109645207602 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 40 12 (99828160915581 / 800000000000)) (orderedInterval (-6711884888 / 1000000000000) (-6711884865 / 1000000000000), orderedInterval (71137481585 / 1000000000000) (71137481608 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (136306819158237 / 800000000000)) (orderedInterval (61053701346 / 1000000000000) (61053701373 / 1000000000000), orderedInterval (2791078509 / 1000000000000) (2791078536 / 1000000000000))) = true
  rfl'

theorem compactCertificate283_stateChecks8 :
    compactCertificate283.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 23 12 (57635815577319 / 800000000000)) (orderedInterval (-50868591573 / 1000000000000) (-50868591572 / 1000000000000), orderedInterval (-78697101513 / 1000000000000) (-78697101512 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 93 12 (234286390476999 / 800000000000)) (orderedInterval (-46409707824 / 1000000000000) (-46409707791 / 1000000000000), orderedInterval (-4387670485 / 1000000000000) (-4387670452 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (156492451055241 / 800000000000)) (orderedInterval (56974093396 / 1000000000000) (56974093532 / 1000000000000), orderedInterval (-3041391938 / 1000000000000) (-3041391802 / 1000000000000))) = true
  rfl'

theorem compactCertificate283_states : ∀ j,
    BesselStateValid (compactCertificate283.point j) (compactCertificate283.state j) :=
  compactCertificate283.statesValid_of_checks3 compactCertificate283_stateChecks0
    compactCertificate283_stateChecks1 compactCertificate283_stateChecks2
    compactCertificate283_stateChecks3 compactCertificate283_stateChecks4
    compactCertificate283_stateChecks5 compactCertificate283_stateChecks6
    compactCertificate283_stateChecks7 compactCertificate283_stateChecks8

theorem compactCertificate283_chunkChecks0_0 :
    compactCertificate283.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (315 / 2) 0 (IntervalRat.scale (315 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (59369872127 / 1000000000000) (59369872128 / 1000000000000), orderedInterval (22554292657 / 1000000000000) (22554292658 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (92811029717763 / 800000000000) 0 (IntervalRat.scale (315 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-39297170772 / 1000000000000) (-39297170771 / 1000000000000), orderedInterval (-62625574406 / 1000000000000) (-62625574405 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (30013180087779 / 160000000000) 0 (IntervalRat.scale (315 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-7462575510 / 1000000000000) (-7462575486 / 1000000000000), orderedInterval (57796496037 / 1000000000000) (57796496061 / 1000000000000)))) (orderedInterval (22728053111 / 1000000000000) (22728053124 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (27082026997641 / 800000000000) 0 (IntervalRat.scale (315 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-10510274855 / 1000000000000) (-10510274851 / 1000000000000), orderedInterval (-136582627944 / 1000000000000) (-136582627941 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (72746133917877 / 800000000000) 0 (IntervalRat.scale (315 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-47967160115 / 1000000000000) (-47967160114 / 1000000000000), orderedInterval (-68294186224 / 1000000000000) (-68294186223 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (197519904725409 / 800000000000) 0 (IntervalRat.scale (315 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (24391105867 / 1000000000000) (24391108082 / 1000000000000), orderedInterval (-44586232968 / 1000000000000) (-44586230753 / 1000000000000)))) (orderedInterval (-3371290863 / 1000000000000) (-3371290686 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (145492267835817 / 800000000000) 0 (IntervalRat.scale (315 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (25075975170 / 1000000000000) (25075975171 / 1000000000000), orderedInterval (53519349875 / 1000000000000) (53519349876 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (249303480772941 / 800000000000) 0 (IntervalRat.scale (315 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-44514712048 / 1000000000000) (-44514712036 / 1000000000000), orderedInterval (-7758827868 / 1000000000000) (-7758827856 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (183635815577319 / 800000000000) 0 (IntervalRat.scale (315 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-44124484184 / 1000000000000) (-44124484183 / 1000000000000), orderedInterval (-28651558332 / 1000000000000) (-28651558331 / 1000000000000)))) (orderedInterval (306610093 / 1000000000000) (306610103 / 1000000000000))) = true
  rfl'

theorem compactCertificate283_chunkChecks0_1 :
    compactCertificate283.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (281744565164937 / 800000000000) 0 (IntervalRat.scale (315 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (38032128644 / 1000000000000) (38032128645 / 1000000000000), orderedInterval (18951451532 / 1000000000000) (18951451533 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (162665300540673 / 800000000000) 0 (IntervalRat.scale (315 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (4868245263 / 1000000000000) (4868245274 / 1000000000000), orderedInterval (-55754708041 / 1000000000000) (-55754708029 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (288652430312757 / 800000000000) 0 (IntervalRat.scale (315 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-13110916728 / 1000000000000) (-13110916727 / 1000000000000), orderedInterval (-39887927126 / 1000000000000) (-39887927125 / 1000000000000)))) (orderedInterval (-8260947241 / 1000000000000) (-8260947177 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (269696543406633 / 800000000000) 0 (IntervalRat.scale (315 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-42718240981 / 1000000000000) (-42718239202 / 1000000000000), orderedInterval (8035384554 / 1000000000000) (8035386333 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (192468179188089 / 800000000000) 0 (IntervalRat.scale (315 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (26117165604 / 1000000000000) (26117168852 / 1000000000000), orderedInterval (-44371616251 / 1000000000000) (-44371613003 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (218238401753631 / 800000000000) 0 (IntervalRat.scale (315 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-12623466169 / 1000000000000) (-12623466168 / 1000000000000), orderedInterval (-46606454183 / 1000000000000) (-46606454182 / 1000000000000)))) (orderedInterval (3304792078 / 1000000000000) (3304792436 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (181944426885039 / 800000000000) 0 (IntervalRat.scale (315 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (47642128802 / 1000000000000) (47642144773 / 1000000000000), orderedInterval (-23113570676 / 1000000000000) (-23113554704 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (160753418973819 / 800000000000) 0 (IntervalRat.scale (315 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (34715266924 / 1000000000000) (34715266925 / 1000000000000), orderedInterval (44219746304 / 1000000000000) (44219746305 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (46592606484081 / 160000000000) 0 (IntervalRat.scale (315 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (8341216993 / 1000000000000) (8341217017 / 1000000000000), orderedInterval (-46020766393 / 1000000000000) (-46020766369 / 1000000000000)))) (orderedInterval (-1222915691 / 1000000000000) (-1222915490 / 1000000000000))) = true
  rfl'

theorem compactCertificate283_chunkChecks0_2 :
    compactCertificate283.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (128877601569507 / 800000000000) 0 (IntervalRat.scale (315 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-62610843869 / 1000000000000) (-62610843687 / 1000000000000), orderedInterval (5819505110 / 1000000000000) (5819505293 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (109250970130827 / 800000000000) 0 (IntervalRat.scale (315 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-52705104800 / 1000000000000) (-52705013993 / 1000000000000), orderedInterval (43596555739 / 1000000000000) (43596646545 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (68364184422681 / 800000000000) 0 (IntervalRat.scale (315 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-85281333074 / 1000000000000) (-85281333071 / 1000000000000), orderedInterval (-12794601116 / 1000000000000) (-12794601113 / 1000000000000)))) (orderedInterval (10217745236 / 1000000000000) (10217750445 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (36766485751527 / 800000000000) 0 (IntervalRat.scale (315 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (43993297853 / 1000000000000) (43993299656 / 1000000000000), orderedInterval (-109645209406 / 1000000000000) (-109645207602 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (99828160915581 / 800000000000) 0 (IntervalRat.scale (315 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-6711884888 / 1000000000000) (-6711884865 / 1000000000000), orderedInterval (71137481585 / 1000000000000) (71137481608 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (136306819158237 / 800000000000) 0 (IntervalRat.scale (315 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (61053701346 / 1000000000000) (61053701373 / 1000000000000), orderedInterval (2791078509 / 1000000000000) (2791078536 / 1000000000000)))) (orderedInterval (-5339156512 / 1000000000000) (-5339156457 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (57635815577319 / 800000000000) 0 (IntervalRat.scale (315 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-50868591573 / 1000000000000) (-50868591572 / 1000000000000), orderedInterval (-78697101513 / 1000000000000) (-78697101512 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (234286390476999 / 800000000000) 0 (IntervalRat.scale (315 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-46409707824 / 1000000000000) (-46409707791 / 1000000000000), orderedInterval (-4387670485 / 1000000000000) (-4387670452 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (156492451055241 / 800000000000) 0 (IntervalRat.scale (315 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (56974093396 / 1000000000000) (56974093532 / 1000000000000), orderedInterval (-3041391938 / 1000000000000) (-3041391802 / 1000000000000)))) (orderedInterval (-7218671191 / 1000000000000) (-7218671119 / 1000000000000))) = true
  rfl'

theorem compactCertificate283_chunkChecks0 :
    compactCertificate283.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate283.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate283_chunkChecks0_0
    compactCertificate283_chunkChecks0_1 compactCertificate283_chunkChecks0_2

theorem compactCertificate283_chunkChecks1_0 :
    compactCertificate283.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (315 / 2) 1 (IntervalRat.scale (315 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (59369872127 / 1000000000000) (59369872128 / 1000000000000), orderedInterval (22554292657 / 1000000000000) (22554292658 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (92811029717763 / 800000000000) 1 (IntervalRat.scale (315 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-39297170772 / 1000000000000) (-39297170771 / 1000000000000), orderedInterval (-62625574406 / 1000000000000) (-62625574405 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (30013180087779 / 160000000000) 1 (IntervalRat.scale (315 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-7462575510 / 1000000000000) (-7462575486 / 1000000000000), orderedInterval (57796496037 / 1000000000000) (57796496061 / 1000000000000)))) (orderedInterval (12549242968 / 1000000000000) (12549242983 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (27082026997641 / 800000000000) 1 (IntervalRat.scale (315 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-10510274855 / 1000000000000) (-10510274851 / 1000000000000), orderedInterval (-136582627944 / 1000000000000) (-136582627941 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (72746133917877 / 800000000000) 1 (IntervalRat.scale (315 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-47967160115 / 1000000000000) (-47967160114 / 1000000000000), orderedInterval (-68294186224 / 1000000000000) (-68294186223 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (197519904725409 / 800000000000) 1 (IntervalRat.scale (315 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (24391105867 / 1000000000000) (24391108082 / 1000000000000), orderedInterval (-44586232968 / 1000000000000) (-44586230753 / 1000000000000)))) (orderedInterval (3847605486 / 1000000000000) (3847605755 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (145492267835817 / 800000000000) 1 (IntervalRat.scale (315 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (25075975170 / 1000000000000) (25075975171 / 1000000000000), orderedInterval (53519349875 / 1000000000000) (53519349876 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (249303480772941 / 800000000000) 1 (IntervalRat.scale (315 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-44514712048 / 1000000000000) (-44514712036 / 1000000000000), orderedInterval (-7758827868 / 1000000000000) (-7758827856 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (183635815577319 / 800000000000) 1 (IntervalRat.scale (315 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-44124484184 / 1000000000000) (-44124484183 / 1000000000000), orderedInterval (-28651558332 / 1000000000000) (-28651558331 / 1000000000000)))) (orderedInterval (-535692735 / 1000000000000) (-535692718 / 1000000000000))) = true
  rfl'

theorem compactCertificate283_chunkChecks1_1 :
    compactCertificate283.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (281744565164937 / 800000000000) 1 (IntervalRat.scale (315 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (38032128644 / 1000000000000) (38032128645 / 1000000000000), orderedInterval (18951451532 / 1000000000000) (18951451533 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (162665300540673 / 800000000000) 1 (IntervalRat.scale (315 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (4868245263 / 1000000000000) (4868245274 / 1000000000000), orderedInterval (-55754708041 / 1000000000000) (-55754708029 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (288652430312757 / 800000000000) 1 (IntervalRat.scale (315 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-13110916728 / 1000000000000) (-13110916727 / 1000000000000), orderedInterval (-39887927126 / 1000000000000) (-39887927125 / 1000000000000)))) (orderedInterval (-25852942459 / 1000000000000) (-25852942327 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (269696543406633 / 800000000000) 1 (IntervalRat.scale (315 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-42718240981 / 1000000000000) (-42718239202 / 1000000000000), orderedInterval (8035384554 / 1000000000000) (8035386333 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (192468179188089 / 800000000000) 1 (IntervalRat.scale (315 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (26117165604 / 1000000000000) (26117168852 / 1000000000000), orderedInterval (-44371616251 / 1000000000000) (-44371613003 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (218238401753631 / 800000000000) 1 (IntervalRat.scale (315 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-12623466169 / 1000000000000) (-12623466168 / 1000000000000), orderedInterval (-46606454183 / 1000000000000) (-46606454182 / 1000000000000)))) (orderedInterval (-6311341453 / 1000000000000) (-6311340884 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (181944426885039 / 800000000000) 1 (IntervalRat.scale (315 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (47642128802 / 1000000000000) (47642144773 / 1000000000000), orderedInterval (-23113570676 / 1000000000000) (-23113554704 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (160753418973819 / 800000000000) 1 (IntervalRat.scale (315 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (34715266924 / 1000000000000) (34715266925 / 1000000000000), orderedInterval (44219746304 / 1000000000000) (44219746305 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (46592606484081 / 160000000000) 1 (IntervalRat.scale (315 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (8341216993 / 1000000000000) (8341217017 / 1000000000000), orderedInterval (-46020766393 / 1000000000000) (-46020766369 / 1000000000000)))) (orderedInterval (-5792542008 / 1000000000000) (-5792541718 / 1000000000000))) = true
  rfl'

theorem compactCertificate283_chunkChecks1_2 :
    compactCertificate283.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (128877601569507 / 800000000000) 1 (IntervalRat.scale (315 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-62610843869 / 1000000000000) (-62610843687 / 1000000000000), orderedInterval (5819505110 / 1000000000000) (5819505293 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (109250970130827 / 800000000000) 1 (IntervalRat.scale (315 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-52705104800 / 1000000000000) (-52705013993 / 1000000000000), orderedInterval (43596555739 / 1000000000000) (43596646545 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (68364184422681 / 800000000000) 1 (IntervalRat.scale (315 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-85281333074 / 1000000000000) (-85281333071 / 1000000000000), orderedInterval (-12794601116 / 1000000000000) (-12794601113 / 1000000000000)))) (orderedInterval (-3317301852 / 1000000000000) (-3317297329 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (36766485751527 / 800000000000) 1 (IntervalRat.scale (315 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (43993297853 / 1000000000000) (43993299656 / 1000000000000), orderedInterval (-109645209406 / 1000000000000) (-109645207602 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (99828160915581 / 800000000000) 1 (IntervalRat.scale (315 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-6711884888 / 1000000000000) (-6711884865 / 1000000000000), orderedInterval (71137481585 / 1000000000000) (71137481608 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (136306819158237 / 800000000000) 1 (IntervalRat.scale (315 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (61053701346 / 1000000000000) (61053701373 / 1000000000000), orderedInterval (2791078509 / 1000000000000) (2791078536 / 1000000000000)))) (orderedInterval (-919287037 / 1000000000000) (-919287007 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (57635815577319 / 800000000000) 1 (IntervalRat.scale (315 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-50868591573 / 1000000000000) (-50868591572 / 1000000000000), orderedInterval (-78697101513 / 1000000000000) (-78697101512 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (234286390476999 / 800000000000) 1 (IntervalRat.scale (315 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-46409707824 / 1000000000000) (-46409707791 / 1000000000000), orderedInterval (-4387670485 / 1000000000000) (-4387670452 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (156492451055241 / 800000000000) 1 (IntervalRat.scale (315 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (56974093396 / 1000000000000) (56974093532 / 1000000000000), orderedInterval (-3041391938 / 1000000000000) (-3041391802 / 1000000000000)))) (orderedInterval (1155851893 / 1000000000000) (1155851992 / 1000000000000))) = true
  rfl'

theorem compactCertificate283_chunkChecks1 :
    compactCertificate283.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate283.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate283_chunkChecks1_0
    compactCertificate283_chunkChecks1_1 compactCertificate283_chunkChecks1_2

theorem compactCertificate283_chunkChecks2_0 :
    compactCertificate283.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (315 / 2) 2 (IntervalRat.scale (315 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (59369872127 / 1000000000000) (59369872128 / 1000000000000), orderedInterval (22554292657 / 1000000000000) (22554292658 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (92811029717763 / 800000000000) 2 (IntervalRat.scale (315 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-39297170772 / 1000000000000) (-39297170771 / 1000000000000), orderedInterval (-62625574406 / 1000000000000) (-62625574405 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (30013180087779 / 160000000000) 2 (IntervalRat.scale (315 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-7462575510 / 1000000000000) (-7462575486 / 1000000000000), orderedInterval (57796496037 / 1000000000000) (57796496061 / 1000000000000)))) (orderedInterval (-22791971286 / 1000000000000) (-22791971269 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (27082026997641 / 800000000000) 2 (IntervalRat.scale (315 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-10510274855 / 1000000000000) (-10510274851 / 1000000000000), orderedInterval (-136582627944 / 1000000000000) (-136582627941 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (72746133917877 / 800000000000) 2 (IntervalRat.scale (315 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-47967160115 / 1000000000000) (-47967160114 / 1000000000000), orderedInterval (-68294186224 / 1000000000000) (-68294186223 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (197519904725409 / 800000000000) 2 (IntervalRat.scale (315 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (24391105867 / 1000000000000) (24391108082 / 1000000000000), orderedInterval (-44586232968 / 1000000000000) (-44586230753 / 1000000000000)))) (orderedInterval (4815159029 / 1000000000000) (4815159448 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (145492267835817 / 800000000000) 2 (IntervalRat.scale (315 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (25075975170 / 1000000000000) (25075975171 / 1000000000000), orderedInterval (53519349875 / 1000000000000) (53519349876 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (249303480772941 / 800000000000) 2 (IntervalRat.scale (315 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-44514712048 / 1000000000000) (-44514712036 / 1000000000000), orderedInterval (-7758827868 / 1000000000000) (-7758827856 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (183635815577319 / 800000000000) 2 (IntervalRat.scale (315 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-44124484184 / 1000000000000) (-44124484183 / 1000000000000), orderedInterval (-28651558332 / 1000000000000) (-28651558331 / 1000000000000)))) (orderedInterval (-3106602648 / 1000000000000) (-3106602618 / 1000000000000))) = true
  rfl'

theorem compactCertificate283_chunkChecks2_1 :
    compactCertificate283.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (281744565164937 / 800000000000) 2 (IntervalRat.scale (315 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (38032128644 / 1000000000000) (38032128645 / 1000000000000), orderedInterval (18951451532 / 1000000000000) (18951451533 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (162665300540673 / 800000000000) 2 (IntervalRat.scale (315 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (4868245263 / 1000000000000) (4868245274 / 1000000000000), orderedInterval (-55754708041 / 1000000000000) (-55754708029 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (288652430312757 / 800000000000) 2 (IntervalRat.scale (315 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-13110916728 / 1000000000000) (-13110916727 / 1000000000000), orderedInterval (-39887927126 / 1000000000000) (-39887927125 / 1000000000000)))) (orderedInterval (43133775095 / 1000000000000) (43133775376 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (269696543406633 / 800000000000) 2 (IntervalRat.scale (315 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-42718240981 / 1000000000000) (-42718239202 / 1000000000000), orderedInterval (8035384554 / 1000000000000) (8035386333 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (192468179188089 / 800000000000) 2 (IntervalRat.scale (315 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (26117165604 / 1000000000000) (26117168852 / 1000000000000), orderedInterval (-44371616251 / 1000000000000) (-44371613003 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (218238401753631 / 800000000000) 2 (IntervalRat.scale (315 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-12623466169 / 1000000000000) (-12623466168 / 1000000000000), orderedInterval (-46606454183 / 1000000000000) (-46606454182 / 1000000000000)))) (orderedInterval (-9447491776 / 1000000000000) (-9447490857 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (181944426885039 / 800000000000) 2 (IntervalRat.scale (315 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (47642128802 / 1000000000000) (47642144773 / 1000000000000), orderedInterval (-23113570676 / 1000000000000) (-23113554704 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (160753418973819 / 800000000000) 2 (IntervalRat.scale (315 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (34715266924 / 1000000000000) (34715266925 / 1000000000000), orderedInterval (44219746304 / 1000000000000) (44219746305 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (46592606484081 / 160000000000) 2 (IntervalRat.scale (315 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (8341216993 / 1000000000000) (8341217017 / 1000000000000), orderedInterval (-46020766393 / 1000000000000) (-46020766369 / 1000000000000)))) (orderedInterval (1393234950 / 1000000000000) (1393235372 / 1000000000000))) = true
  rfl'

theorem compactCertificate283_chunkChecks2_2 :
    compactCertificate283.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (128877601569507 / 800000000000) 2 (IntervalRat.scale (315 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-62610843869 / 1000000000000) (-62610843687 / 1000000000000), orderedInterval (5819505110 / 1000000000000) (5819505293 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (109250970130827 / 800000000000) 2 (IntervalRat.scale (315 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-52705104800 / 1000000000000) (-52705013993 / 1000000000000), orderedInterval (43596555739 / 1000000000000) (43596646545 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (68364184422681 / 800000000000) 2 (IntervalRat.scale (315 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-85281333074 / 1000000000000) (-85281333071 / 1000000000000), orderedInterval (-12794601116 / 1000000000000) (-12794601113 / 1000000000000)))) (orderedInterval (-11877842601 / 1000000000000) (-11877838643 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (36766485751527 / 800000000000) 2 (IntervalRat.scale (315 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (43993297853 / 1000000000000) (43993299656 / 1000000000000), orderedInterval (-109645209406 / 1000000000000) (-109645207602 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (99828160915581 / 800000000000) 2 (IntervalRat.scale (315 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-6711884888 / 1000000000000) (-6711884865 / 1000000000000), orderedInterval (71137481585 / 1000000000000) (71137481608 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (136306819158237 / 800000000000) 2 (IntervalRat.scale (315 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (61053701346 / 1000000000000) (61053701373 / 1000000000000), orderedInterval (2791078509 / 1000000000000) (2791078536 / 1000000000000)))) (orderedInterval (5455316141 / 1000000000000) (5455316164 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (57635815577319 / 800000000000) 2 (IntervalRat.scale (315 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-50868591573 / 1000000000000) (-50868591572 / 1000000000000), orderedInterval (-78697101513 / 1000000000000) (-78697101512 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (234286390476999 / 800000000000) 2 (IntervalRat.scale (315 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-46409707824 / 1000000000000) (-46409707791 / 1000000000000), orderedInterval (-4387670485 / 1000000000000) (-4387670452 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (156492451055241 / 800000000000) 2 (IntervalRat.scale (315 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (56974093396 / 1000000000000) (56974093532 / 1000000000000), orderedInterval (-3041391938 / 1000000000000) (-3041391802 / 1000000000000)))) (orderedInterval (3485118712 / 1000000000000) (3485118852 / 1000000000000))) = true
  rfl'

theorem compactCertificate283_chunkChecks2 :
    compactCertificate283.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate283.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate283_chunkChecks2_0
    compactCertificate283_chunkChecks2_1 compactCertificate283_chunkChecks2_2

theorem compactCertificate283_chunkChecks3_0 :
    compactCertificate283.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (315 / 2) 3 (IntervalRat.scale (315 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (59369872127 / 1000000000000) (59369872128 / 1000000000000), orderedInterval (22554292657 / 1000000000000) (22554292658 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (92811029717763 / 800000000000) 3 (IntervalRat.scale (315 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-39297170772 / 1000000000000) (-39297170771 / 1000000000000), orderedInterval (-62625574406 / 1000000000000) (-62625574405 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (30013180087779 / 160000000000) 3 (IntervalRat.scale (315 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-7462575510 / 1000000000000) (-7462575486 / 1000000000000), orderedInterval (57796496037 / 1000000000000) (57796496061 / 1000000000000)))) (orderedInterval (-14291030163 / 1000000000000) (-14291030143 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (27082026997641 / 800000000000) 3 (IntervalRat.scale (315 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-10510274855 / 1000000000000) (-10510274851 / 1000000000000), orderedInterval (-136582627944 / 1000000000000) (-136582627941 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (72746133917877 / 800000000000) 3 (IntervalRat.scale (315 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-47967160115 / 1000000000000) (-47967160114 / 1000000000000), orderedInterval (-68294186224 / 1000000000000) (-68294186223 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (197519904725409 / 800000000000) 3 (IntervalRat.scale (315 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (24391105867 / 1000000000000) (24391108082 / 1000000000000), orderedInterval (-44586232968 / 1000000000000) (-44586230753 / 1000000000000)))) (orderedInterval (-11775598061 / 1000000000000) (-11775597407 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (145492267835817 / 800000000000) 3 (IntervalRat.scale (315 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (25075975170 / 1000000000000) (25075975171 / 1000000000000), orderedInterval (53519349875 / 1000000000000) (53519349876 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (249303480772941 / 800000000000) 3 (IntervalRat.scale (315 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-44514712048 / 1000000000000) (-44514712036 / 1000000000000), orderedInterval (-7758827868 / 1000000000000) (-7758827856 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (183635815577319 / 800000000000) 3 (IntervalRat.scale (315 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-44124484184 / 1000000000000) (-44124484183 / 1000000000000), orderedInterval (-28651558332 / 1000000000000) (-28651558331 / 1000000000000)))) (orderedInterval (309630299 / 1000000000000) (309630352 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate283_chunkChecks3_1 :
    compactCertificate283.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (281744565164937 / 800000000000) 3 (IntervalRat.scale (315 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (38032128644 / 1000000000000) (38032128645 / 1000000000000), orderedInterval (18951451532 / 1000000000000) (18951451533 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (162665300540673 / 800000000000) 3 (IntervalRat.scale (315 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (4868245263 / 1000000000000) (4868245274 / 1000000000000), orderedInterval (-55754708041 / 1000000000000) (-55754708029 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (288652430312757 / 800000000000) 3 (IntervalRat.scale (315 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-13110916728 / 1000000000000) (-13110916727 / 1000000000000), orderedInterval (-39887927126 / 1000000000000) (-39887927125 / 1000000000000)))) (orderedInterval (114436931052 / 1000000000000) (114436931666 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (269696543406633 / 800000000000) 3 (IntervalRat.scale (315 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-42718240981 / 1000000000000) (-42718239202 / 1000000000000), orderedInterval (8035384554 / 1000000000000) (8035386333 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (192468179188089 / 800000000000) 3 (IntervalRat.scale (315 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (26117165604 / 1000000000000) (26117168852 / 1000000000000), orderedInterval (-44371616251 / 1000000000000) (-44371613003 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (218238401753631 / 800000000000) 3 (IntervalRat.scale (315 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-12623466169 / 1000000000000) (-12623466168 / 1000000000000), orderedInterval (-46606454183 / 1000000000000) (-46606454182 / 1000000000000)))) (orderedInterval (15211913622 / 1000000000000) (15211915123 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (181944426885039 / 800000000000) 3 (IntervalRat.scale (315 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (47642128802 / 1000000000000) (47642144773 / 1000000000000), orderedInterval (-23113570676 / 1000000000000) (-23113554704 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (160753418973819 / 800000000000) 3 (IntervalRat.scale (315 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (34715266924 / 1000000000000) (34715266925 / 1000000000000), orderedInterval (44219746304 / 1000000000000) (44219746305 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (46592606484081 / 160000000000) 3 (IntervalRat.scale (315 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (8341216993 / 1000000000000) (8341217017 / 1000000000000), orderedInterval (-46020766393 / 1000000000000) (-46020766369 / 1000000000000)))) (orderedInterval (13497197189 / 1000000000000) (13497197802 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate283_chunkChecks3_2 :
    compactCertificate283.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (128877601569507 / 800000000000) 3 (IntervalRat.scale (315 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-62610843869 / 1000000000000) (-62610843687 / 1000000000000), orderedInterval (5819505110 / 1000000000000) (5819505293 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (109250970130827 / 800000000000) 3 (IntervalRat.scale (315 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-52705104800 / 1000000000000) (-52705013993 / 1000000000000), orderedInterval (43596555739 / 1000000000000) (43596646545 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (68364184422681 / 800000000000) 3 (IntervalRat.scale (315 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-85281333074 / 1000000000000) (-85281333071 / 1000000000000), orderedInterval (-12794601116 / 1000000000000) (-12794601113 / 1000000000000)))) (orderedInterval (2746068533 / 1000000000000) (2746071973 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (36766485751527 / 800000000000) 3 (IntervalRat.scale (315 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (43993297853 / 1000000000000) (43993299656 / 1000000000000), orderedInterval (-109645209406 / 1000000000000) (-109645207602 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (99828160915581 / 800000000000) 3 (IntervalRat.scale (315 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-6711884888 / 1000000000000) (-6711884865 / 1000000000000), orderedInterval (71137481585 / 1000000000000) (71137481608 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (136306819158237 / 800000000000) 3 (IntervalRat.scale (315 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (61053701346 / 1000000000000) (61053701373 / 1000000000000), orderedInterval (2791078509 / 1000000000000) (2791078536 / 1000000000000)))) (orderedInterval (988471777 / 1000000000000) (988471798 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (57635815577319 / 800000000000) 3 (IntervalRat.scale (315 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-50868591573 / 1000000000000) (-50868591572 / 1000000000000), orderedInterval (-78697101513 / 1000000000000) (-78697101512 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (234286390476999 / 800000000000) 3 (IntervalRat.scale (315 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-46409707824 / 1000000000000) (-46409707791 / 1000000000000), orderedInterval (-4387670485 / 1000000000000) (-4387670452 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (156492451055241 / 800000000000) 3 (IntervalRat.scale (315 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (56974093396 / 1000000000000) (56974093532 / 1000000000000), orderedInterval (-3041391938 / 1000000000000) (-3041391802 / 1000000000000)))) (orderedInterval (-3366098969 / 1000000000000) (-3366098763 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate283_chunkChecks3 :
    compactCertificate283.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate283.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate283_chunkChecks3_0
    compactCertificate283_chunkChecks3_1 compactCertificate283_chunkChecks3_2

theorem compactCertificate283_chunkChecks4_0 :
    compactCertificate283.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (315 / 2) 4 (IntervalRat.scale (315 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (59369872127 / 1000000000000) (59369872128 / 1000000000000), orderedInterval (22554292657 / 1000000000000) (22554292658 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (92811029717763 / 800000000000) 4 (IntervalRat.scale (315 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-39297170772 / 1000000000000) (-39297170771 / 1000000000000), orderedInterval (-62625574406 / 1000000000000) (-62625574405 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (30013180087779 / 160000000000) 4 (IntervalRat.scale (315 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-7462575510 / 1000000000000) (-7462575486 / 1000000000000), orderedInterval (57796496037 / 1000000000000) (57796496061 / 1000000000000)))) (orderedInterval (22723778071 / 1000000000000) (22723778094 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (27082026997641 / 800000000000) 4 (IntervalRat.scale (315 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-10510274855 / 1000000000000) (-10510274851 / 1000000000000), orderedInterval (-136582627944 / 1000000000000) (-136582627941 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (72746133917877 / 800000000000) 4 (IntervalRat.scale (315 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-47967160115 / 1000000000000) (-47967160114 / 1000000000000), orderedInterval (-68294186224 / 1000000000000) (-68294186223 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (197519904725409 / 800000000000) 4 (IntervalRat.scale (315 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (24391105867 / 1000000000000) (24391108082 / 1000000000000), orderedInterval (-44586232968 / 1000000000000) (-44586230753 / 1000000000000)))) (orderedInterval (-10515893002 / 1000000000000) (-10515891974 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (145492267835817 / 800000000000) 4 (IntervalRat.scale (315 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (25075975170 / 1000000000000) (25075975171 / 1000000000000), orderedInterval (53519349875 / 1000000000000) (53519349876 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (249303480772941 / 800000000000) 4 (IntervalRat.scale (315 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-44514712048 / 1000000000000) (-44514712036 / 1000000000000), orderedInterval (-7758827868 / 1000000000000) (-7758827856 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (183635815577319 / 800000000000) 4 (IntervalRat.scale (315 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-44124484184 / 1000000000000) (-44124484183 / 1000000000000), orderedInterval (-28651558332 / 1000000000000) (-28651558331 / 1000000000000)))) (orderedInterval (16227472957 / 1000000000000) (16227473056 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate283_chunkChecks4_1 :
    compactCertificate283.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (281744565164937 / 800000000000) 4 (IntervalRat.scale (315 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (38032128644 / 1000000000000) (38032128645 / 1000000000000), orderedInterval (18951451532 / 1000000000000) (18951451533 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (162665300540673 / 800000000000) 4 (IntervalRat.scale (315 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (4868245263 / 1000000000000) (4868245274 / 1000000000000), orderedInterval (-55754708041 / 1000000000000) (-55754708029 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (288652430312757 / 800000000000) 4 (IntervalRat.scale (315 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-13110916728 / 1000000000000) (-13110916727 / 1000000000000), orderedInterval (-39887927126 / 1000000000000) (-39887927125 / 1000000000000)))) (orderedInterval (-220731098843 / 1000000000000) (-220731097483 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (269696543406633 / 800000000000) 4 (IntervalRat.scale (315 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-42718240981 / 1000000000000) (-42718239202 / 1000000000000), orderedInterval (8035384554 / 1000000000000) (8035386333 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (192468179188089 / 800000000000) 4 (IntervalRat.scale (315 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (26117165604 / 1000000000000) (26117168852 / 1000000000000), orderedInterval (-44371616251 / 1000000000000) (-44371613003 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (218238401753631 / 800000000000) 4 (IntervalRat.scale (315 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-12623466169 / 1000000000000) (-12623466168 / 1000000000000), orderedInterval (-46606454183 / 1000000000000) (-46606454182 / 1000000000000)))) (orderedInterval (30015274714 / 1000000000000) (30015277227 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (181944426885039 / 800000000000) 4 (IntervalRat.scale (315 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (47642128802 / 1000000000000) (47642144773 / 1000000000000), orderedInterval (-23113570676 / 1000000000000) (-23113554704 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (160753418973819 / 800000000000) 4 (IntervalRat.scale (315 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (34715266924 / 1000000000000) (34715266925 / 1000000000000), orderedInterval (44219746304 / 1000000000000) (44219746305 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (46592606484081 / 160000000000) 4 (IntervalRat.scale (315 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (8341216993 / 1000000000000) (8341217017 / 1000000000000), orderedInterval (-46020766393 / 1000000000000) (-46020766369 / 1000000000000)))) (orderedInterval (-547131692 / 1000000000000) (-547130796 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate283_chunkChecks4_2 :
    compactCertificate283.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (128877601569507 / 800000000000) 4 (IntervalRat.scale (315 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-62610843869 / 1000000000000) (-62610843687 / 1000000000000), orderedInterval (5819505110 / 1000000000000) (5819505293 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (109250970130827 / 800000000000) 4 (IntervalRat.scale (315 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-52705104800 / 1000000000000) (-52705013993 / 1000000000000), orderedInterval (43596555739 / 1000000000000) (43596646545 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (68364184422681 / 800000000000) 4 (IntervalRat.scale (315 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-85281333074 / 1000000000000) (-85281333071 / 1000000000000), orderedInterval (-12794601116 / 1000000000000) (-12794601113 / 1000000000000)))) (orderedInterval (12367497889 / 1000000000000) (12367500902 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (36766485751527 / 800000000000) 4 (IntervalRat.scale (315 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (43993297853 / 1000000000000) (43993299656 / 1000000000000), orderedInterval (-109645209406 / 1000000000000) (-109645207602 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (99828160915581 / 800000000000) 4 (IntervalRat.scale (315 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-6711884888 / 1000000000000) (-6711884865 / 1000000000000), orderedInterval (71137481585 / 1000000000000) (71137481608 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (136306819158237 / 800000000000) 4 (IntervalRat.scale (315 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (61053701346 / 1000000000000) (61053701373 / 1000000000000), orderedInterval (2791078509 / 1000000000000) (2791078536 / 1000000000000)))) (orderedInterval (-6366616068 / 1000000000000) (-6366616046 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (57635815577319 / 800000000000) 4 (IntervalRat.scale (315 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-50868591573 / 1000000000000) (-50868591572 / 1000000000000), orderedInterval (-78697101513 / 1000000000000) (-78697101512 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (234286390476999 / 800000000000) 4 (IntervalRat.scale (315 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-46409707824 / 1000000000000) (-46409707791 / 1000000000000), orderedInterval (-4387670485 / 1000000000000) (-4387670452 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (156492451055241 / 800000000000) 4 (IntervalRat.scale (315 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (56974093396 / 1000000000000) (56974093532 / 1000000000000), orderedInterval (-3041391938 / 1000000000000) (-3041391802 / 1000000000000)))) (orderedInterval (19752089338 / 1000000000000) (19752089657 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate283_chunkChecks4 :
    compactCertificate283.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate283.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate283_chunkChecks4_0
    compactCertificate283_chunkChecks4_1 compactCertificate283_chunkChecks4_2

theorem compactCertificate283_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate283.chunkCheck r b = true :=
  compactCertificate283.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate283_chunkChecks0
    · exact compactCertificate283_chunkChecks1
    · exact compactCertificate283_chunkChecks2
    · exact compactCertificate283_chunkChecks3
    · exact compactCertificate283_chunkChecks4)

theorem compactCertificate283_coefficient0 :
    compactCertificate283.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate283_coefficient1 :
    compactCertificate283.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate283_coefficient2 :
    compactCertificate283.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate283_coefficient3 :
    compactCertificate283.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate283_coefficient4 :
    compactCertificate283.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate283_coefficients : ∀ r : Fin 5,
    compactCertificate283.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate283_coefficient0
  · exact compactCertificate283_coefficient1
  · exact compactCertificate283_coefficient2
  · exact compactCertificate283_coefficient3
  · exact compactCertificate283_coefficient4

theorem compactCertificate283_lower : (1 : ℚ) ≤ compactCertificate283.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate283, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate283_proves {t : ℝ} (ht : t ∈ compactCertificate283.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate283.proves compactCertificate283_states compactCertificate283_chunks
    compactCertificate283_coefficients compactCertificate283_lower ht

end Erdos232
