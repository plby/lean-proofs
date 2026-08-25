/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate284 : CompactCertificate where
  left := 158
  right := 159
  center := 317 / 2
  grid := fun i =>
    match i.val with
    | 0 => 50
    | 1 => 37
    | 2 => 60
    | 3 => 11
    | 4 => 29
    | 5 => 79
    | 6 => 58
    | 7 => 100
    | 8 => 74
    | 9 => 113
    | 10 => 65
    | 11 => 116
    | 12 => 108
    | 13 => 77
    | 14 => 87
    | 15 => 73
    | 16 => 64
    | 17 => 93
    | 18 => 52
    | 19 => 44
    | 20 => 27
    | 21 => 15
    | 22 => 40
    | 23 => 55
    | 24 => 23
    | 25 => 94
    | _ => 63
  point := fun i =>
    match i.val with
    | 0 => 317 / 2
    | 1 => 467001530484617 / 4000000000000
    | 2 => 151018699806761 / 800000000000
    | 3 => 136269881877019 / 4000000000000
    | 4 => 366040070666143 / 4000000000000
    | 5 => 993869996792931 / 4000000000000
    | 6 => 732080141332603 / 4000000000000
    | 7 => 1254431800079719 / 4000000000000
    | 8 => 924008786317621 / 4000000000000
    | 9 => 1417667097734683 / 4000000000000
    | 10 => 818490480498307 / 4000000000000
    | 11 => 1452425720780063 / 4000000000000
    | 12 => 1357044512061947 / 4000000000000
    | 13 => 968450996867051 / 4000000000000
    | 14 => 1098120211998429 / 4000000000000
    | 15 => 915498147977101 / 4000000000000
    | 16 => 808870378011121 / 4000000000000
    | 17 => 234442162784979 / 800000000000
    | 18 => 648479360278313 / 4000000000000
    | 19 => 549723135420193 / 4000000000000
    | 20 => 343991213682379 / 4000000000000
    | 21 => 184999618781493 / 4000000000000
    | 22 => 502309952543479 / 4000000000000
    | 23 => 685861296399383 / 4000000000000
    | 24 => 290008786317621 / 4000000000000
    | 25 => 1178869615574741 / 4000000000000
    | _ => 787430269595419 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (51052924563 / 1000000000000) (51052987072 / 1000000000000), orderedInterval (-37712618411 / 1000000000000) (-37712555902 / 1000000000000))
    | 1 => (orderedInterval (-71068007788 / 1000000000000) (-71068007787 / 1000000000000), orderedInterval (-19748671266 / 1000000000000) (-19748671265 / 1000000000000))
    | 2 => (orderedInterval (50731951167 / 1000000000000) (50731951168 / 1000000000000), orderedInterval (28126294490 / 1000000000000) (28126294491 / 1000000000000))
    | 3 => (orderedInterval (-39307959751 / 1000000000000) (-39307959750 / 1000000000000), orderedInterval (-130356742522 / 1000000000000) (-130356742521 / 1000000000000))
    | 4 => (orderedInterval (-77366048532 / 1000000000000) (-77366048531 / 1000000000000), orderedInterval (-30742196756 / 1000000000000) (-30742196755 / 1000000000000))
    | 5 => (orderedInterval (-44318613004 / 1000000000000) (-44318613003 / 1000000000000), orderedInterval (-24365735555 / 1000000000000) (-24365735554 / 1000000000000))
    | 6 => (orderedInterval (58964252626 / 1000000000000) (58964252709 / 1000000000000), orderedInterval (-1433753521 / 1000000000000) (-1433753438 / 1000000000000))
    | 7 => (orderedInterval (10433157765 / 1000000000000) (10433157766 / 1000000000000), orderedInterval (43814149667 / 1000000000000) (43814149668 / 1000000000000))
    | 8 => (orderedInterval (-33448561098 / 1000000000000) (-33448543972 / 1000000000000), orderedInterval (40533470519 / 1000000000000) (40533487645 / 1000000000000))
    | 9 => (orderedInterval (-8496859748 / 1000000000000) (-8496859747 / 1000000000000), orderedInterval (-41509708271 / 1000000000000) (-41509708270 / 1000000000000))
    | 10 => (orderedInterval (-52065362866 / 1000000000000) (-52065362865 / 1000000000000), orderedInterval (-19882293491 / 1000000000000) (-19882293490 / 1000000000000))
    | 11 => (orderedInterval (-21285449222 / 1000000000000) (-21285447582 / 1000000000000), orderedInterval (36087455645 / 1000000000000) (36087457285 / 1000000000000))
    | 12 => (orderedInterval (29658843774 / 1000000000000) (29658843775 / 1000000000000), orderedInterval (31529095588 / 1000000000000) (31529095589 / 1000000000000))
    | 13 => (orderedInterval (-43009761463 / 1000000000000) (-43009761462 / 1000000000000), orderedInterval (-27832376371 / 1000000000000) (-27832376370 / 1000000000000))
    | 14 => (orderedInterval (-43858728298 / 1000000000000) (-43858712400 / 1000000000000), orderedInterval (19963379899 / 1000000000000) (19963395797 / 1000000000000))
    | 15 => (orderedInterval (-16746646190 / 1000000000000) (-16746646189 / 1000000000000), orderedInterval (-49974194925 / 1000000000000) (-49974194924 / 1000000000000))
    | 16 => (orderedInterval (52318769702 / 1000000000000) (52318776024 / 1000000000000), orderedInterval (-20400790017 / 1000000000000) (-20400783695 / 1000000000000))
    | 17 => (orderedInterval (-46381564111 / 1000000000000) (-46381563622 / 1000000000000), orderedInterval (4674828776 / 1000000000000) (4674829265 / 1000000000000))
    | 18 => (orderedInterval (-27727103757 / 1000000000000) (-27727101540 / 1000000000000), orderedInterval (56282184049 / 1000000000000) (56282186265 / 1000000000000))
    | 19 => (orderedInterval (-1007552181 / 1000000000000) (-1007552175 / 1000000000000), orderedInterval (68057389340 / 1000000000000) (68057389346 / 1000000000000))
    | 20 => (orderedInterval (-79644652456 / 1000000000000) (-79644648293 / 1000000000000), orderedInterval (33011238223 / 1000000000000) (33011242385 / 1000000000000))
    | 21 => (orderedInterval (10695153254 / 1000000000000) (10695153293 / 1000000000000), orderedInterval (-116953892824 / 1000000000000) (-116953892784 / 1000000000000))
    | 22 => (orderedInterval (45769631496 / 1000000000000) (45769631497 / 1000000000000), orderedInterval (54358441037 / 1000000000000) (54358441038 / 1000000000000))
    | 23 => (orderedInterval (31202352235 / 1000000000000) (31202357212 / 1000000000000), orderedInterval (-52428737352 / 1000000000000) (-52428732374 / 1000000000000))
    | 24 => (orderedInterval (-80295867988 / 1000000000000) (-80295867987 / 1000000000000), orderedInterval (-47749198888 / 1000000000000) (-47749198887 / 1000000000000))
    | 25 => (orderedInterval (8899329642 / 1000000000000) (8899329643 / 1000000000000), orderedInterval (45601863899 / 1000000000000) (45601863900 / 1000000000000))
    | _ => (orderedInterval (15606647779 / 1000000000000) (15606647975 / 1000000000000), orderedInterval (-54723750260 / 1000000000000) (-54723750064 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (22550384849 / 1000000000000) (22550409638 / 1000000000000)
      | 1 => orderedInterval (752288259 / 1000000000000) (752288279 / 1000000000000)
      | 2 => orderedInterval (-1130186061 / 1000000000000) (-1130185638 / 1000000000000)
      | 3 => orderedInterval (-5373677609 / 1000000000000) (-5373677312 / 1000000000000)
      | 4 => orderedInterval (-4380609630 / 1000000000000) (-4380609529 / 1000000000000)
      | 5 => orderedInterval (-4374965697 / 1000000000000) (-4374965306 / 1000000000000)
      | 6 => orderedInterval (1897528119 / 1000000000000) (1897528650 / 1000000000000)
      | 7 => orderedInterval (-3627169978 / 1000000000000) (-3627169577 / 1000000000000)
      | _ => orderedInterval (-4136692256 / 1000000000000) (-4136692175 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-13117785547 / 1000000000000) (-13117760758 / 1000000000000)
      | 1 => orderedInterval (2371284976 / 1000000000000) (2371284998 / 1000000000000)
      | 2 => orderedInterval (-1246170030 / 1000000000000) (-1246169410 / 1000000000000)
      | 3 => orderedInterval (26343328834 / 1000000000000) (26343329500 / 1000000000000)
      | 4 => orderedInterval (-5413628523 / 1000000000000) (-5413628352 / 1000000000000)
      | 5 => orderedInterval (877471786 / 1000000000000) (877472294 / 1000000000000)
      | 6 => orderedInterval (-11961518452 / 1000000000000) (-11961517978 / 1000000000000)
      | 7 => orderedInterval (3999848504 / 1000000000000) (3999848935 / 1000000000000)
      | _ => orderedInterval (5718473543 / 1000000000000) (5718473652 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-24016379260 / 1000000000000) (-24016354312 / 1000000000000)
      | 1 => orderedInterval (-6835428448 / 1000000000000) (-6835428417 / 1000000000000)
      | 2 => orderedInterval (2984749839 / 1000000000000) (2984750750 / 1000000000000)
      | 3 => orderedInterval (14594444872 / 1000000000000) (14594446380 / 1000000000000)
      | 4 => orderedInterval (11311365946 / 1000000000000) (11311366240 / 1000000000000)
      | 5 => orderedInterval (9330755832 / 1000000000000) (9330756500 / 1000000000000)
      | 6 => orderedInterval (-3842274513 / 1000000000000) (-3842274063 / 1000000000000)
      | 7 => orderedInterval (3441916832 / 1000000000000) (3441917299 / 1000000000000)
      | _ => orderedInterval (7086831809 / 1000000000000) (7086831958 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (12384143671 / 1000000000000) (12384168620 / 1000000000000)
      | 1 => orderedInterval (-6427587395 / 1000000000000) (-6427587349 / 1000000000000)
      | 2 => orderedInterval (7416389174 / 1000000000000) (7416390512 / 1000000000000)
      | 3 => orderedInterval (-141063746521 / 1000000000000) (-141063743096 / 1000000000000)
      | 4 => orderedInterval (15415926293 / 1000000000000) (15415926800 / 1000000000000)
      | 5 => orderedInterval (-1502234473 / 1000000000000) (-1502233588 / 1000000000000)
      | 6 => orderedInterval (11993012835 / 1000000000000) (11993013273 / 1000000000000)
      | 7 => orderedInterval (-4548863904 / 1000000000000) (-4548863400 / 1000000000000)
      | _ => orderedInterval (4175666917 / 1000000000000) (4175667130 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (25873414286 / 1000000000000) (25873439393 / 1000000000000)
      | 1 => orderedInterval (18794154424 / 1000000000000) (18794154494 / 1000000000000)
      | 2 => orderedInterval (-8672655855 / 1000000000000) (-8672653878 / 1000000000000)
      | 3 => orderedInterval (-54532776696 / 1000000000000) (-54532768876 / 1000000000000)
      | 4 => orderedInterval (-31578692399 / 1000000000000) (-31578691519 / 1000000000000)
      | 5 => orderedInterval (-22631787191 / 1000000000000) (-22631785995 / 1000000000000)
      | 6 => orderedInterval (4508486200 / 1000000000000) (4508486639 / 1000000000000)
      | 7 => orderedInterval (-3628146909 / 1000000000000) (-3628146361 / 1000000000000)
      | _ => orderedInterval (-15700983234 / 1000000000000) (-15700982919 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (2176899996 / 1000000000000) (2176927030 / 1000000000000)
    | 1 => orderedInterval (7571305091 / 1000000000000) (7571332881 / 1000000000000)
    | 2 => orderedInterval (14055982909 / 1000000000000) (14056012335 / 1000000000000)
    | 3 => orderedInterval (-102157293403 / 1000000000000) (-102157261098 / 1000000000000)
    | _ => orderedInterval (-87568987374 / 1000000000000) (-87568949022 / 1000000000000)

theorem compactCertificate284_stateChecks0 :
    compactCertificate284.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 50 12 (317 / 2)) (orderedInterval (51052924563 / 1000000000000) (51052987072 / 1000000000000), orderedInterval (-37712618411 / 1000000000000) (-37712555902 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (467001530484617 / 4000000000000)) (orderedInterval (-71068007788 / 1000000000000) (-71068007787 / 1000000000000), orderedInterval (-19748671266 / 1000000000000) (-19748671265 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 60 12 (151018699806761 / 800000000000)) (orderedInterval (50731951167 / 1000000000000) (50731951168 / 1000000000000), orderedInterval (28126294490 / 1000000000000) (28126294491 / 1000000000000))) = true
  rfl'

theorem compactCertificate284_stateChecks1 :
    compactCertificate284.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 11 12 (136269881877019 / 4000000000000)) (orderedInterval (-39307959751 / 1000000000000) (-39307959750 / 1000000000000), orderedInterval (-130356742522 / 1000000000000) (-130356742521 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 29 12 (366040070666143 / 4000000000000)) (orderedInterval (-77366048532 / 1000000000000) (-77366048531 / 1000000000000), orderedInterval (-30742196756 / 1000000000000) (-30742196755 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 79 12 (993869996792931 / 4000000000000)) (orderedInterval (-44318613004 / 1000000000000) (-44318613003 / 1000000000000), orderedInterval (-24365735555 / 1000000000000) (-24365735554 / 1000000000000))) = true
  rfl'

theorem compactCertificate284_stateChecks2 :
    compactCertificate284.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (732080141332603 / 4000000000000)) (orderedInterval (58964252626 / 1000000000000) (58964252709 / 1000000000000), orderedInterval (-1433753521 / 1000000000000) (-1433753438 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 100 12 (1254431800079719 / 4000000000000)) (orderedInterval (10433157765 / 1000000000000) (10433157766 / 1000000000000), orderedInterval (43814149667 / 1000000000000) (43814149668 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 74 12 (924008786317621 / 4000000000000)) (orderedInterval (-33448561098 / 1000000000000) (-33448543972 / 1000000000000), orderedInterval (40533470519 / 1000000000000) (40533487645 / 1000000000000))) = true
  rfl'

theorem compactCertificate284_stateChecks3 :
    compactCertificate284.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 113 12 (1417667097734683 / 4000000000000)) (orderedInterval (-8496859748 / 1000000000000) (-8496859747 / 1000000000000), orderedInterval (-41509708271 / 1000000000000) (-41509708270 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 65 12 (818490480498307 / 4000000000000)) (orderedInterval (-52065362866 / 1000000000000) (-52065362865 / 1000000000000), orderedInterval (-19882293491 / 1000000000000) (-19882293490 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 116 12 (1452425720780063 / 4000000000000)) (orderedInterval (-21285449222 / 1000000000000) (-21285447582 / 1000000000000), orderedInterval (36087455645 / 1000000000000) (36087457285 / 1000000000000))) = true
  rfl'

theorem compactCertificate284_stateChecks4 :
    compactCertificate284.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 108 12 (1357044512061947 / 4000000000000)) (orderedInterval (29658843774 / 1000000000000) (29658843775 / 1000000000000), orderedInterval (31529095588 / 1000000000000) (31529095589 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 77 12 (968450996867051 / 4000000000000)) (orderedInterval (-43009761463 / 1000000000000) (-43009761462 / 1000000000000), orderedInterval (-27832376371 / 1000000000000) (-27832376370 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 87 12 (1098120211998429 / 4000000000000)) (orderedInterval (-43858728298 / 1000000000000) (-43858712400 / 1000000000000), orderedInterval (19963379899 / 1000000000000) (19963395797 / 1000000000000))) = true
  rfl'

theorem compactCertificate284_stateChecks5 :
    compactCertificate284.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 73 12 (915498147977101 / 4000000000000)) (orderedInterval (-16746646190 / 1000000000000) (-16746646189 / 1000000000000), orderedInterval (-49974194925 / 1000000000000) (-49974194924 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (808870378011121 / 4000000000000)) (orderedInterval (52318769702 / 1000000000000) (52318776024 / 1000000000000), orderedInterval (-20400790017 / 1000000000000) (-20400783695 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 93 12 (234442162784979 / 800000000000)) (orderedInterval (-46381564111 / 1000000000000) (-46381563622 / 1000000000000), orderedInterval (4674828776 / 1000000000000) (4674829265 / 1000000000000))) = true
  rfl'

theorem compactCertificate284_stateChecks6 :
    compactCertificate284.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 52 12 (648479360278313 / 4000000000000)) (orderedInterval (-27727103757 / 1000000000000) (-27727101540 / 1000000000000), orderedInterval (56282184049 / 1000000000000) (56282186265 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 44 12 (549723135420193 / 4000000000000)) (orderedInterval (-1007552181 / 1000000000000) (-1007552175 / 1000000000000), orderedInterval (68057389340 / 1000000000000) (68057389346 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 27 12 (343991213682379 / 4000000000000)) (orderedInterval (-79644652456 / 1000000000000) (-79644648293 / 1000000000000), orderedInterval (33011238223 / 1000000000000) (33011242385 / 1000000000000))) = true
  rfl'

theorem compactCertificate284_stateChecks7 :
    compactCertificate284.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 15 12 (184999618781493 / 4000000000000)) (orderedInterval (10695153254 / 1000000000000) (10695153293 / 1000000000000), orderedInterval (-116953892824 / 1000000000000) (-116953892784 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 40 12 (502309952543479 / 4000000000000)) (orderedInterval (45769631496 / 1000000000000) (45769631497 / 1000000000000), orderedInterval (54358441037 / 1000000000000) (54358441038 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (685861296399383 / 4000000000000)) (orderedInterval (31202352235 / 1000000000000) (31202357212 / 1000000000000), orderedInterval (-52428737352 / 1000000000000) (-52428732374 / 1000000000000))) = true
  rfl'

theorem compactCertificate284_stateChecks8 :
    compactCertificate284.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 23 12 (290008786317621 / 4000000000000)) (orderedInterval (-80295867988 / 1000000000000) (-80295867987 / 1000000000000), orderedInterval (-47749198888 / 1000000000000) (-47749198887 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 94 12 (1178869615574741 / 4000000000000)) (orderedInterval (8899329642 / 1000000000000) (8899329643 / 1000000000000), orderedInterval (45601863899 / 1000000000000) (45601863900 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (787430269595419 / 4000000000000)) (orderedInterval (15606647779 / 1000000000000) (15606647975 / 1000000000000), orderedInterval (-54723750260 / 1000000000000) (-54723750064 / 1000000000000))) = true
  rfl'

theorem compactCertificate284_states : ∀ j,
    BesselStateValid (compactCertificate284.point j) (compactCertificate284.state j) :=
  compactCertificate284.statesValid_of_checks3 compactCertificate284_stateChecks0
    compactCertificate284_stateChecks1 compactCertificate284_stateChecks2
    compactCertificate284_stateChecks3 compactCertificate284_stateChecks4
    compactCertificate284_stateChecks5 compactCertificate284_stateChecks6
    compactCertificate284_stateChecks7 compactCertificate284_stateChecks8

theorem compactCertificate284_chunkChecks0_0 :
    compactCertificate284.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (317 / 2) 0 (IntervalRat.scale (317 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (51052924563 / 1000000000000) (51052987072 / 1000000000000), orderedInterval (-37712618411 / 1000000000000) (-37712555902 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (467001530484617 / 4000000000000) 0 (IntervalRat.scale (317 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-71068007788 / 1000000000000) (-71068007787 / 1000000000000), orderedInterval (-19748671266 / 1000000000000) (-19748671265 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (151018699806761 / 800000000000) 0 (IntervalRat.scale (317 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (50731951167 / 1000000000000) (50731951168 / 1000000000000), orderedInterval (28126294490 / 1000000000000) (28126294491 / 1000000000000)))) (orderedInterval (22550384849 / 1000000000000) (22550409638 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (136269881877019 / 4000000000000) 0 (IntervalRat.scale (317 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-39307959751 / 1000000000000) (-39307959750 / 1000000000000), orderedInterval (-130356742522 / 1000000000000) (-130356742521 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (366040070666143 / 4000000000000) 0 (IntervalRat.scale (317 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-77366048532 / 1000000000000) (-77366048531 / 1000000000000), orderedInterval (-30742196756 / 1000000000000) (-30742196755 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (993869996792931 / 4000000000000) 0 (IntervalRat.scale (317 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-44318613004 / 1000000000000) (-44318613003 / 1000000000000), orderedInterval (-24365735555 / 1000000000000) (-24365735554 / 1000000000000)))) (orderedInterval (752288259 / 1000000000000) (752288279 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (732080141332603 / 4000000000000) 0 (IntervalRat.scale (317 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (58964252626 / 1000000000000) (58964252709 / 1000000000000), orderedInterval (-1433753521 / 1000000000000) (-1433753438 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1254431800079719 / 4000000000000) 0 (IntervalRat.scale (317 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (10433157765 / 1000000000000) (10433157766 / 1000000000000), orderedInterval (43814149667 / 1000000000000) (43814149668 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (924008786317621 / 4000000000000) 0 (IntervalRat.scale (317 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-33448561098 / 1000000000000) (-33448543972 / 1000000000000), orderedInterval (40533470519 / 1000000000000) (40533487645 / 1000000000000)))) (orderedInterval (-1130186061 / 1000000000000) (-1130185638 / 1000000000000))) = true
  rfl'

theorem compactCertificate284_chunkChecks0_1 :
    compactCertificate284.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1417667097734683 / 4000000000000) 0 (IntervalRat.scale (317 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-8496859748 / 1000000000000) (-8496859747 / 1000000000000), orderedInterval (-41509708271 / 1000000000000) (-41509708270 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (818490480498307 / 4000000000000) 0 (IntervalRat.scale (317 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-52065362866 / 1000000000000) (-52065362865 / 1000000000000), orderedInterval (-19882293491 / 1000000000000) (-19882293490 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1452425720780063 / 4000000000000) 0 (IntervalRat.scale (317 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-21285449222 / 1000000000000) (-21285447582 / 1000000000000), orderedInterval (36087455645 / 1000000000000) (36087457285 / 1000000000000)))) (orderedInterval (-5373677609 / 1000000000000) (-5373677312 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1357044512061947 / 4000000000000) 0 (IntervalRat.scale (317 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (29658843774 / 1000000000000) (29658843775 / 1000000000000), orderedInterval (31529095588 / 1000000000000) (31529095589 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (968450996867051 / 4000000000000) 0 (IntervalRat.scale (317 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-43009761463 / 1000000000000) (-43009761462 / 1000000000000), orderedInterval (-27832376371 / 1000000000000) (-27832376370 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1098120211998429 / 4000000000000) 0 (IntervalRat.scale (317 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-43858728298 / 1000000000000) (-43858712400 / 1000000000000), orderedInterval (19963379899 / 1000000000000) (19963395797 / 1000000000000)))) (orderedInterval (-4380609630 / 1000000000000) (-4380609529 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (915498147977101 / 4000000000000) 0 (IntervalRat.scale (317 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-16746646190 / 1000000000000) (-16746646189 / 1000000000000), orderedInterval (-49974194925 / 1000000000000) (-49974194924 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (808870378011121 / 4000000000000) 0 (IntervalRat.scale (317 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (52318769702 / 1000000000000) (52318776024 / 1000000000000), orderedInterval (-20400790017 / 1000000000000) (-20400783695 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (234442162784979 / 800000000000) 0 (IntervalRat.scale (317 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-46381564111 / 1000000000000) (-46381563622 / 1000000000000), orderedInterval (4674828776 / 1000000000000) (4674829265 / 1000000000000)))) (orderedInterval (-4374965697 / 1000000000000) (-4374965306 / 1000000000000))) = true
  rfl'

theorem compactCertificate284_chunkChecks0_2 :
    compactCertificate284.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (648479360278313 / 4000000000000) 0 (IntervalRat.scale (317 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-27727103757 / 1000000000000) (-27727101540 / 1000000000000), orderedInterval (56282184049 / 1000000000000) (56282186265 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (549723135420193 / 4000000000000) 0 (IntervalRat.scale (317 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-1007552181 / 1000000000000) (-1007552175 / 1000000000000), orderedInterval (68057389340 / 1000000000000) (68057389346 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (343991213682379 / 4000000000000) 0 (IntervalRat.scale (317 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-79644652456 / 1000000000000) (-79644648293 / 1000000000000), orderedInterval (33011238223 / 1000000000000) (33011242385 / 1000000000000)))) (orderedInterval (1897528119 / 1000000000000) (1897528650 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (184999618781493 / 4000000000000) 0 (IntervalRat.scale (317 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (10695153254 / 1000000000000) (10695153293 / 1000000000000), orderedInterval (-116953892824 / 1000000000000) (-116953892784 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (502309952543479 / 4000000000000) 0 (IntervalRat.scale (317 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (45769631496 / 1000000000000) (45769631497 / 1000000000000), orderedInterval (54358441037 / 1000000000000) (54358441038 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (685861296399383 / 4000000000000) 0 (IntervalRat.scale (317 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (31202352235 / 1000000000000) (31202357212 / 1000000000000), orderedInterval (-52428737352 / 1000000000000) (-52428732374 / 1000000000000)))) (orderedInterval (-3627169978 / 1000000000000) (-3627169577 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (290008786317621 / 4000000000000) 0 (IntervalRat.scale (317 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-80295867988 / 1000000000000) (-80295867987 / 1000000000000), orderedInterval (-47749198888 / 1000000000000) (-47749198887 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1178869615574741 / 4000000000000) 0 (IntervalRat.scale (317 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (8899329642 / 1000000000000) (8899329643 / 1000000000000), orderedInterval (45601863899 / 1000000000000) (45601863900 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (787430269595419 / 4000000000000) 0 (IntervalRat.scale (317 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (15606647779 / 1000000000000) (15606647975 / 1000000000000), orderedInterval (-54723750260 / 1000000000000) (-54723750064 / 1000000000000)))) (orderedInterval (-4136692256 / 1000000000000) (-4136692175 / 1000000000000))) = true
  rfl'

theorem compactCertificate284_chunkChecks0 :
    compactCertificate284.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate284.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate284_chunkChecks0_0
    compactCertificate284_chunkChecks0_1 compactCertificate284_chunkChecks0_2

theorem compactCertificate284_chunkChecks1_0 :
    compactCertificate284.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (317 / 2) 1 (IntervalRat.scale (317 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (51052924563 / 1000000000000) (51052987072 / 1000000000000), orderedInterval (-37712618411 / 1000000000000) (-37712555902 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (467001530484617 / 4000000000000) 1 (IntervalRat.scale (317 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-71068007788 / 1000000000000) (-71068007787 / 1000000000000), orderedInterval (-19748671266 / 1000000000000) (-19748671265 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (151018699806761 / 800000000000) 1 (IntervalRat.scale (317 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (50731951167 / 1000000000000) (50731951168 / 1000000000000), orderedInterval (28126294490 / 1000000000000) (28126294491 / 1000000000000)))) (orderedInterval (-13117785547 / 1000000000000) (-13117760758 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (136269881877019 / 4000000000000) 1 (IntervalRat.scale (317 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-39307959751 / 1000000000000) (-39307959750 / 1000000000000), orderedInterval (-130356742522 / 1000000000000) (-130356742521 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (366040070666143 / 4000000000000) 1 (IntervalRat.scale (317 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-77366048532 / 1000000000000) (-77366048531 / 1000000000000), orderedInterval (-30742196756 / 1000000000000) (-30742196755 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (993869996792931 / 4000000000000) 1 (IntervalRat.scale (317 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-44318613004 / 1000000000000) (-44318613003 / 1000000000000), orderedInterval (-24365735555 / 1000000000000) (-24365735554 / 1000000000000)))) (orderedInterval (2371284976 / 1000000000000) (2371284998 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (732080141332603 / 4000000000000) 1 (IntervalRat.scale (317 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (58964252626 / 1000000000000) (58964252709 / 1000000000000), orderedInterval (-1433753521 / 1000000000000) (-1433753438 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1254431800079719 / 4000000000000) 1 (IntervalRat.scale (317 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (10433157765 / 1000000000000) (10433157766 / 1000000000000), orderedInterval (43814149667 / 1000000000000) (43814149668 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (924008786317621 / 4000000000000) 1 (IntervalRat.scale (317 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-33448561098 / 1000000000000) (-33448543972 / 1000000000000), orderedInterval (40533470519 / 1000000000000) (40533487645 / 1000000000000)))) (orderedInterval (-1246170030 / 1000000000000) (-1246169410 / 1000000000000))) = true
  rfl'

theorem compactCertificate284_chunkChecks1_1 :
    compactCertificate284.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1417667097734683 / 4000000000000) 1 (IntervalRat.scale (317 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-8496859748 / 1000000000000) (-8496859747 / 1000000000000), orderedInterval (-41509708271 / 1000000000000) (-41509708270 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (818490480498307 / 4000000000000) 1 (IntervalRat.scale (317 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-52065362866 / 1000000000000) (-52065362865 / 1000000000000), orderedInterval (-19882293491 / 1000000000000) (-19882293490 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1452425720780063 / 4000000000000) 1 (IntervalRat.scale (317 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-21285449222 / 1000000000000) (-21285447582 / 1000000000000), orderedInterval (36087455645 / 1000000000000) (36087457285 / 1000000000000)))) (orderedInterval (26343328834 / 1000000000000) (26343329500 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1357044512061947 / 4000000000000) 1 (IntervalRat.scale (317 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (29658843774 / 1000000000000) (29658843775 / 1000000000000), orderedInterval (31529095588 / 1000000000000) (31529095589 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (968450996867051 / 4000000000000) 1 (IntervalRat.scale (317 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-43009761463 / 1000000000000) (-43009761462 / 1000000000000), orderedInterval (-27832376371 / 1000000000000) (-27832376370 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1098120211998429 / 4000000000000) 1 (IntervalRat.scale (317 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-43858728298 / 1000000000000) (-43858712400 / 1000000000000), orderedInterval (19963379899 / 1000000000000) (19963395797 / 1000000000000)))) (orderedInterval (-5413628523 / 1000000000000) (-5413628352 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (915498147977101 / 4000000000000) 1 (IntervalRat.scale (317 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-16746646190 / 1000000000000) (-16746646189 / 1000000000000), orderedInterval (-49974194925 / 1000000000000) (-49974194924 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (808870378011121 / 4000000000000) 1 (IntervalRat.scale (317 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (52318769702 / 1000000000000) (52318776024 / 1000000000000), orderedInterval (-20400790017 / 1000000000000) (-20400783695 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (234442162784979 / 800000000000) 1 (IntervalRat.scale (317 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-46381564111 / 1000000000000) (-46381563622 / 1000000000000), orderedInterval (4674828776 / 1000000000000) (4674829265 / 1000000000000)))) (orderedInterval (877471786 / 1000000000000) (877472294 / 1000000000000))) = true
  rfl'

theorem compactCertificate284_chunkChecks1_2 :
    compactCertificate284.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (648479360278313 / 4000000000000) 1 (IntervalRat.scale (317 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-27727103757 / 1000000000000) (-27727101540 / 1000000000000), orderedInterval (56282184049 / 1000000000000) (56282186265 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (549723135420193 / 4000000000000) 1 (IntervalRat.scale (317 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-1007552181 / 1000000000000) (-1007552175 / 1000000000000), orderedInterval (68057389340 / 1000000000000) (68057389346 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (343991213682379 / 4000000000000) 1 (IntervalRat.scale (317 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-79644652456 / 1000000000000) (-79644648293 / 1000000000000), orderedInterval (33011238223 / 1000000000000) (33011242385 / 1000000000000)))) (orderedInterval (-11961518452 / 1000000000000) (-11961517978 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (184999618781493 / 4000000000000) 1 (IntervalRat.scale (317 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (10695153254 / 1000000000000) (10695153293 / 1000000000000), orderedInterval (-116953892824 / 1000000000000) (-116953892784 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (502309952543479 / 4000000000000) 1 (IntervalRat.scale (317 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (45769631496 / 1000000000000) (45769631497 / 1000000000000), orderedInterval (54358441037 / 1000000000000) (54358441038 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (685861296399383 / 4000000000000) 1 (IntervalRat.scale (317 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (31202352235 / 1000000000000) (31202357212 / 1000000000000), orderedInterval (-52428737352 / 1000000000000) (-52428732374 / 1000000000000)))) (orderedInterval (3999848504 / 1000000000000) (3999848935 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (290008786317621 / 4000000000000) 1 (IntervalRat.scale (317 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-80295867988 / 1000000000000) (-80295867987 / 1000000000000), orderedInterval (-47749198888 / 1000000000000) (-47749198887 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1178869615574741 / 4000000000000) 1 (IntervalRat.scale (317 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (8899329642 / 1000000000000) (8899329643 / 1000000000000), orderedInterval (45601863899 / 1000000000000) (45601863900 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (787430269595419 / 4000000000000) 1 (IntervalRat.scale (317 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (15606647779 / 1000000000000) (15606647975 / 1000000000000), orderedInterval (-54723750260 / 1000000000000) (-54723750064 / 1000000000000)))) (orderedInterval (5718473543 / 1000000000000) (5718473652 / 1000000000000))) = true
  rfl'

theorem compactCertificate284_chunkChecks1 :
    compactCertificate284.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate284.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate284_chunkChecks1_0
    compactCertificate284_chunkChecks1_1 compactCertificate284_chunkChecks1_2

theorem compactCertificate284_chunkChecks2_0 :
    compactCertificate284.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (317 / 2) 2 (IntervalRat.scale (317 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (51052924563 / 1000000000000) (51052987072 / 1000000000000), orderedInterval (-37712618411 / 1000000000000) (-37712555902 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (467001530484617 / 4000000000000) 2 (IntervalRat.scale (317 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-71068007788 / 1000000000000) (-71068007787 / 1000000000000), orderedInterval (-19748671266 / 1000000000000) (-19748671265 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (151018699806761 / 800000000000) 2 (IntervalRat.scale (317 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (50731951167 / 1000000000000) (50731951168 / 1000000000000), orderedInterval (28126294490 / 1000000000000) (28126294491 / 1000000000000)))) (orderedInterval (-24016379260 / 1000000000000) (-24016354312 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (136269881877019 / 4000000000000) 2 (IntervalRat.scale (317 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-39307959751 / 1000000000000) (-39307959750 / 1000000000000), orderedInterval (-130356742522 / 1000000000000) (-130356742521 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (366040070666143 / 4000000000000) 2 (IntervalRat.scale (317 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-77366048532 / 1000000000000) (-77366048531 / 1000000000000), orderedInterval (-30742196756 / 1000000000000) (-30742196755 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (993869996792931 / 4000000000000) 2 (IntervalRat.scale (317 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-44318613004 / 1000000000000) (-44318613003 / 1000000000000), orderedInterval (-24365735555 / 1000000000000) (-24365735554 / 1000000000000)))) (orderedInterval (-6835428448 / 1000000000000) (-6835428417 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (732080141332603 / 4000000000000) 2 (IntervalRat.scale (317 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (58964252626 / 1000000000000) (58964252709 / 1000000000000), orderedInterval (-1433753521 / 1000000000000) (-1433753438 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1254431800079719 / 4000000000000) 2 (IntervalRat.scale (317 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (10433157765 / 1000000000000) (10433157766 / 1000000000000), orderedInterval (43814149667 / 1000000000000) (43814149668 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (924008786317621 / 4000000000000) 2 (IntervalRat.scale (317 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-33448561098 / 1000000000000) (-33448543972 / 1000000000000), orderedInterval (40533470519 / 1000000000000) (40533487645 / 1000000000000)))) (orderedInterval (2984749839 / 1000000000000) (2984750750 / 1000000000000))) = true
  rfl'

theorem compactCertificate284_chunkChecks2_1 :
    compactCertificate284.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1417667097734683 / 4000000000000) 2 (IntervalRat.scale (317 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-8496859748 / 1000000000000) (-8496859747 / 1000000000000), orderedInterval (-41509708271 / 1000000000000) (-41509708270 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (818490480498307 / 4000000000000) 2 (IntervalRat.scale (317 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-52065362866 / 1000000000000) (-52065362865 / 1000000000000), orderedInterval (-19882293491 / 1000000000000) (-19882293490 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1452425720780063 / 4000000000000) 2 (IntervalRat.scale (317 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-21285449222 / 1000000000000) (-21285447582 / 1000000000000), orderedInterval (36087455645 / 1000000000000) (36087457285 / 1000000000000)))) (orderedInterval (14594444872 / 1000000000000) (14594446380 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1357044512061947 / 4000000000000) 2 (IntervalRat.scale (317 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (29658843774 / 1000000000000) (29658843775 / 1000000000000), orderedInterval (31529095588 / 1000000000000) (31529095589 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (968450996867051 / 4000000000000) 2 (IntervalRat.scale (317 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-43009761463 / 1000000000000) (-43009761462 / 1000000000000), orderedInterval (-27832376371 / 1000000000000) (-27832376370 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1098120211998429 / 4000000000000) 2 (IntervalRat.scale (317 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-43858728298 / 1000000000000) (-43858712400 / 1000000000000), orderedInterval (19963379899 / 1000000000000) (19963395797 / 1000000000000)))) (orderedInterval (11311365946 / 1000000000000) (11311366240 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (915498147977101 / 4000000000000) 2 (IntervalRat.scale (317 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-16746646190 / 1000000000000) (-16746646189 / 1000000000000), orderedInterval (-49974194925 / 1000000000000) (-49974194924 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (808870378011121 / 4000000000000) 2 (IntervalRat.scale (317 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (52318769702 / 1000000000000) (52318776024 / 1000000000000), orderedInterval (-20400790017 / 1000000000000) (-20400783695 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (234442162784979 / 800000000000) 2 (IntervalRat.scale (317 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-46381564111 / 1000000000000) (-46381563622 / 1000000000000), orderedInterval (4674828776 / 1000000000000) (4674829265 / 1000000000000)))) (orderedInterval (9330755832 / 1000000000000) (9330756500 / 1000000000000))) = true
  rfl'

theorem compactCertificate284_chunkChecks2_2 :
    compactCertificate284.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (648479360278313 / 4000000000000) 2 (IntervalRat.scale (317 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-27727103757 / 1000000000000) (-27727101540 / 1000000000000), orderedInterval (56282184049 / 1000000000000) (56282186265 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (549723135420193 / 4000000000000) 2 (IntervalRat.scale (317 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-1007552181 / 1000000000000) (-1007552175 / 1000000000000), orderedInterval (68057389340 / 1000000000000) (68057389346 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (343991213682379 / 4000000000000) 2 (IntervalRat.scale (317 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-79644652456 / 1000000000000) (-79644648293 / 1000000000000), orderedInterval (33011238223 / 1000000000000) (33011242385 / 1000000000000)))) (orderedInterval (-3842274513 / 1000000000000) (-3842274063 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (184999618781493 / 4000000000000) 2 (IntervalRat.scale (317 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (10695153254 / 1000000000000) (10695153293 / 1000000000000), orderedInterval (-116953892824 / 1000000000000) (-116953892784 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (502309952543479 / 4000000000000) 2 (IntervalRat.scale (317 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (45769631496 / 1000000000000) (45769631497 / 1000000000000), orderedInterval (54358441037 / 1000000000000) (54358441038 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (685861296399383 / 4000000000000) 2 (IntervalRat.scale (317 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (31202352235 / 1000000000000) (31202357212 / 1000000000000), orderedInterval (-52428737352 / 1000000000000) (-52428732374 / 1000000000000)))) (orderedInterval (3441916832 / 1000000000000) (3441917299 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (290008786317621 / 4000000000000) 2 (IntervalRat.scale (317 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-80295867988 / 1000000000000) (-80295867987 / 1000000000000), orderedInterval (-47749198888 / 1000000000000) (-47749198887 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1178869615574741 / 4000000000000) 2 (IntervalRat.scale (317 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (8899329642 / 1000000000000) (8899329643 / 1000000000000), orderedInterval (45601863899 / 1000000000000) (45601863900 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (787430269595419 / 4000000000000) 2 (IntervalRat.scale (317 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (15606647779 / 1000000000000) (15606647975 / 1000000000000), orderedInterval (-54723750260 / 1000000000000) (-54723750064 / 1000000000000)))) (orderedInterval (7086831809 / 1000000000000) (7086831958 / 1000000000000))) = true
  rfl'

theorem compactCertificate284_chunkChecks2 :
    compactCertificate284.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate284.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate284_chunkChecks2_0
    compactCertificate284_chunkChecks2_1 compactCertificate284_chunkChecks2_2

theorem compactCertificate284_chunkChecks3_0 :
    compactCertificate284.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (317 / 2) 3 (IntervalRat.scale (317 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (51052924563 / 1000000000000) (51052987072 / 1000000000000), orderedInterval (-37712618411 / 1000000000000) (-37712555902 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (467001530484617 / 4000000000000) 3 (IntervalRat.scale (317 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-71068007788 / 1000000000000) (-71068007787 / 1000000000000), orderedInterval (-19748671266 / 1000000000000) (-19748671265 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (151018699806761 / 800000000000) 3 (IntervalRat.scale (317 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (50731951167 / 1000000000000) (50731951168 / 1000000000000), orderedInterval (28126294490 / 1000000000000) (28126294491 / 1000000000000)))) (orderedInterval (12384143671 / 1000000000000) (12384168620 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (136269881877019 / 4000000000000) 3 (IntervalRat.scale (317 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-39307959751 / 1000000000000) (-39307959750 / 1000000000000), orderedInterval (-130356742522 / 1000000000000) (-130356742521 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (366040070666143 / 4000000000000) 3 (IntervalRat.scale (317 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-77366048532 / 1000000000000) (-77366048531 / 1000000000000), orderedInterval (-30742196756 / 1000000000000) (-30742196755 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (993869996792931 / 4000000000000) 3 (IntervalRat.scale (317 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-44318613004 / 1000000000000) (-44318613003 / 1000000000000), orderedInterval (-24365735555 / 1000000000000) (-24365735554 / 1000000000000)))) (orderedInterval (-6427587395 / 1000000000000) (-6427587349 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (732080141332603 / 4000000000000) 3 (IntervalRat.scale (317 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (58964252626 / 1000000000000) (58964252709 / 1000000000000), orderedInterval (-1433753521 / 1000000000000) (-1433753438 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1254431800079719 / 4000000000000) 3 (IntervalRat.scale (317 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (10433157765 / 1000000000000) (10433157766 / 1000000000000), orderedInterval (43814149667 / 1000000000000) (43814149668 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (924008786317621 / 4000000000000) 3 (IntervalRat.scale (317 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-33448561098 / 1000000000000) (-33448543972 / 1000000000000), orderedInterval (40533470519 / 1000000000000) (40533487645 / 1000000000000)))) (orderedInterval (7416389174 / 1000000000000) (7416390512 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate284_chunkChecks3_1 :
    compactCertificate284.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1417667097734683 / 4000000000000) 3 (IntervalRat.scale (317 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-8496859748 / 1000000000000) (-8496859747 / 1000000000000), orderedInterval (-41509708271 / 1000000000000) (-41509708270 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (818490480498307 / 4000000000000) 3 (IntervalRat.scale (317 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-52065362866 / 1000000000000) (-52065362865 / 1000000000000), orderedInterval (-19882293491 / 1000000000000) (-19882293490 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1452425720780063 / 4000000000000) 3 (IntervalRat.scale (317 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-21285449222 / 1000000000000) (-21285447582 / 1000000000000), orderedInterval (36087455645 / 1000000000000) (36087457285 / 1000000000000)))) (orderedInterval (-141063746521 / 1000000000000) (-141063743096 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1357044512061947 / 4000000000000) 3 (IntervalRat.scale (317 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (29658843774 / 1000000000000) (29658843775 / 1000000000000), orderedInterval (31529095588 / 1000000000000) (31529095589 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (968450996867051 / 4000000000000) 3 (IntervalRat.scale (317 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-43009761463 / 1000000000000) (-43009761462 / 1000000000000), orderedInterval (-27832376371 / 1000000000000) (-27832376370 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1098120211998429 / 4000000000000) 3 (IntervalRat.scale (317 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-43858728298 / 1000000000000) (-43858712400 / 1000000000000), orderedInterval (19963379899 / 1000000000000) (19963395797 / 1000000000000)))) (orderedInterval (15415926293 / 1000000000000) (15415926800 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (915498147977101 / 4000000000000) 3 (IntervalRat.scale (317 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-16746646190 / 1000000000000) (-16746646189 / 1000000000000), orderedInterval (-49974194925 / 1000000000000) (-49974194924 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (808870378011121 / 4000000000000) 3 (IntervalRat.scale (317 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (52318769702 / 1000000000000) (52318776024 / 1000000000000), orderedInterval (-20400790017 / 1000000000000) (-20400783695 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (234442162784979 / 800000000000) 3 (IntervalRat.scale (317 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-46381564111 / 1000000000000) (-46381563622 / 1000000000000), orderedInterval (4674828776 / 1000000000000) (4674829265 / 1000000000000)))) (orderedInterval (-1502234473 / 1000000000000) (-1502233588 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate284_chunkChecks3_2 :
    compactCertificate284.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (648479360278313 / 4000000000000) 3 (IntervalRat.scale (317 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-27727103757 / 1000000000000) (-27727101540 / 1000000000000), orderedInterval (56282184049 / 1000000000000) (56282186265 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (549723135420193 / 4000000000000) 3 (IntervalRat.scale (317 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-1007552181 / 1000000000000) (-1007552175 / 1000000000000), orderedInterval (68057389340 / 1000000000000) (68057389346 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (343991213682379 / 4000000000000) 3 (IntervalRat.scale (317 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-79644652456 / 1000000000000) (-79644648293 / 1000000000000), orderedInterval (33011238223 / 1000000000000) (33011242385 / 1000000000000)))) (orderedInterval (11993012835 / 1000000000000) (11993013273 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (184999618781493 / 4000000000000) 3 (IntervalRat.scale (317 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (10695153254 / 1000000000000) (10695153293 / 1000000000000), orderedInterval (-116953892824 / 1000000000000) (-116953892784 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (502309952543479 / 4000000000000) 3 (IntervalRat.scale (317 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (45769631496 / 1000000000000) (45769631497 / 1000000000000), orderedInterval (54358441037 / 1000000000000) (54358441038 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (685861296399383 / 4000000000000) 3 (IntervalRat.scale (317 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (31202352235 / 1000000000000) (31202357212 / 1000000000000), orderedInterval (-52428737352 / 1000000000000) (-52428732374 / 1000000000000)))) (orderedInterval (-4548863904 / 1000000000000) (-4548863400 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (290008786317621 / 4000000000000) 3 (IntervalRat.scale (317 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-80295867988 / 1000000000000) (-80295867987 / 1000000000000), orderedInterval (-47749198888 / 1000000000000) (-47749198887 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1178869615574741 / 4000000000000) 3 (IntervalRat.scale (317 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (8899329642 / 1000000000000) (8899329643 / 1000000000000), orderedInterval (45601863899 / 1000000000000) (45601863900 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (787430269595419 / 4000000000000) 3 (IntervalRat.scale (317 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (15606647779 / 1000000000000) (15606647975 / 1000000000000), orderedInterval (-54723750260 / 1000000000000) (-54723750064 / 1000000000000)))) (orderedInterval (4175666917 / 1000000000000) (4175667130 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate284_chunkChecks3 :
    compactCertificate284.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate284.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate284_chunkChecks3_0
    compactCertificate284_chunkChecks3_1 compactCertificate284_chunkChecks3_2

theorem compactCertificate284_chunkChecks4_0 :
    compactCertificate284.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (317 / 2) 4 (IntervalRat.scale (317 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (51052924563 / 1000000000000) (51052987072 / 1000000000000), orderedInterval (-37712618411 / 1000000000000) (-37712555902 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (467001530484617 / 4000000000000) 4 (IntervalRat.scale (317 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-71068007788 / 1000000000000) (-71068007787 / 1000000000000), orderedInterval (-19748671266 / 1000000000000) (-19748671265 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (151018699806761 / 800000000000) 4 (IntervalRat.scale (317 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (50731951167 / 1000000000000) (50731951168 / 1000000000000), orderedInterval (28126294490 / 1000000000000) (28126294491 / 1000000000000)))) (orderedInterval (25873414286 / 1000000000000) (25873439393 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (136269881877019 / 4000000000000) 4 (IntervalRat.scale (317 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-39307959751 / 1000000000000) (-39307959750 / 1000000000000), orderedInterval (-130356742522 / 1000000000000) (-130356742521 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (366040070666143 / 4000000000000) 4 (IntervalRat.scale (317 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-77366048532 / 1000000000000) (-77366048531 / 1000000000000), orderedInterval (-30742196756 / 1000000000000) (-30742196755 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (993869996792931 / 4000000000000) 4 (IntervalRat.scale (317 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-44318613004 / 1000000000000) (-44318613003 / 1000000000000), orderedInterval (-24365735555 / 1000000000000) (-24365735554 / 1000000000000)))) (orderedInterval (18794154424 / 1000000000000) (18794154494 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (732080141332603 / 4000000000000) 4 (IntervalRat.scale (317 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (58964252626 / 1000000000000) (58964252709 / 1000000000000), orderedInterval (-1433753521 / 1000000000000) (-1433753438 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1254431800079719 / 4000000000000) 4 (IntervalRat.scale (317 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (10433157765 / 1000000000000) (10433157766 / 1000000000000), orderedInterval (43814149667 / 1000000000000) (43814149668 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (924008786317621 / 4000000000000) 4 (IntervalRat.scale (317 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-33448561098 / 1000000000000) (-33448543972 / 1000000000000), orderedInterval (40533470519 / 1000000000000) (40533487645 / 1000000000000)))) (orderedInterval (-8672655855 / 1000000000000) (-8672653878 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate284_chunkChecks4_1 :
    compactCertificate284.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1417667097734683 / 4000000000000) 4 (IntervalRat.scale (317 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-8496859748 / 1000000000000) (-8496859747 / 1000000000000), orderedInterval (-41509708271 / 1000000000000) (-41509708270 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (818490480498307 / 4000000000000) 4 (IntervalRat.scale (317 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-52065362866 / 1000000000000) (-52065362865 / 1000000000000), orderedInterval (-19882293491 / 1000000000000) (-19882293490 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1452425720780063 / 4000000000000) 4 (IntervalRat.scale (317 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-21285449222 / 1000000000000) (-21285447582 / 1000000000000), orderedInterval (36087455645 / 1000000000000) (36087457285 / 1000000000000)))) (orderedInterval (-54532776696 / 1000000000000) (-54532768876 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1357044512061947 / 4000000000000) 4 (IntervalRat.scale (317 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (29658843774 / 1000000000000) (29658843775 / 1000000000000), orderedInterval (31529095588 / 1000000000000) (31529095589 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (968450996867051 / 4000000000000) 4 (IntervalRat.scale (317 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-43009761463 / 1000000000000) (-43009761462 / 1000000000000), orderedInterval (-27832376371 / 1000000000000) (-27832376370 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1098120211998429 / 4000000000000) 4 (IntervalRat.scale (317 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-43858728298 / 1000000000000) (-43858712400 / 1000000000000), orderedInterval (19963379899 / 1000000000000) (19963395797 / 1000000000000)))) (orderedInterval (-31578692399 / 1000000000000) (-31578691519 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (915498147977101 / 4000000000000) 4 (IntervalRat.scale (317 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-16746646190 / 1000000000000) (-16746646189 / 1000000000000), orderedInterval (-49974194925 / 1000000000000) (-49974194924 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (808870378011121 / 4000000000000) 4 (IntervalRat.scale (317 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (52318769702 / 1000000000000) (52318776024 / 1000000000000), orderedInterval (-20400790017 / 1000000000000) (-20400783695 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (234442162784979 / 800000000000) 4 (IntervalRat.scale (317 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-46381564111 / 1000000000000) (-46381563622 / 1000000000000), orderedInterval (4674828776 / 1000000000000) (4674829265 / 1000000000000)))) (orderedInterval (-22631787191 / 1000000000000) (-22631785995 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate284_chunkChecks4_2 :
    compactCertificate284.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (648479360278313 / 4000000000000) 4 (IntervalRat.scale (317 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-27727103757 / 1000000000000) (-27727101540 / 1000000000000), orderedInterval (56282184049 / 1000000000000) (56282186265 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (549723135420193 / 4000000000000) 4 (IntervalRat.scale (317 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-1007552181 / 1000000000000) (-1007552175 / 1000000000000), orderedInterval (68057389340 / 1000000000000) (68057389346 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (343991213682379 / 4000000000000) 4 (IntervalRat.scale (317 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-79644652456 / 1000000000000) (-79644648293 / 1000000000000), orderedInterval (33011238223 / 1000000000000) (33011242385 / 1000000000000)))) (orderedInterval (4508486200 / 1000000000000) (4508486639 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (184999618781493 / 4000000000000) 4 (IntervalRat.scale (317 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (10695153254 / 1000000000000) (10695153293 / 1000000000000), orderedInterval (-116953892824 / 1000000000000) (-116953892784 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (502309952543479 / 4000000000000) 4 (IntervalRat.scale (317 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (45769631496 / 1000000000000) (45769631497 / 1000000000000), orderedInterval (54358441037 / 1000000000000) (54358441038 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (685861296399383 / 4000000000000) 4 (IntervalRat.scale (317 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (31202352235 / 1000000000000) (31202357212 / 1000000000000), orderedInterval (-52428737352 / 1000000000000) (-52428732374 / 1000000000000)))) (orderedInterval (-3628146909 / 1000000000000) (-3628146361 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (290008786317621 / 4000000000000) 4 (IntervalRat.scale (317 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-80295867988 / 1000000000000) (-80295867987 / 1000000000000), orderedInterval (-47749198888 / 1000000000000) (-47749198887 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1178869615574741 / 4000000000000) 4 (IntervalRat.scale (317 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (8899329642 / 1000000000000) (8899329643 / 1000000000000), orderedInterval (45601863899 / 1000000000000) (45601863900 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (787430269595419 / 4000000000000) 4 (IntervalRat.scale (317 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (15606647779 / 1000000000000) (15606647975 / 1000000000000), orderedInterval (-54723750260 / 1000000000000) (-54723750064 / 1000000000000)))) (orderedInterval (-15700983234 / 1000000000000) (-15700982919 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate284_chunkChecks4 :
    compactCertificate284.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate284.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate284_chunkChecks4_0
    compactCertificate284_chunkChecks4_1 compactCertificate284_chunkChecks4_2

theorem compactCertificate284_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate284.chunkCheck r b = true :=
  compactCertificate284.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate284_chunkChecks0
    · exact compactCertificate284_chunkChecks1
    · exact compactCertificate284_chunkChecks2
    · exact compactCertificate284_chunkChecks3
    · exact compactCertificate284_chunkChecks4)

theorem compactCertificate284_coefficient0 :
    compactCertificate284.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate284_coefficient1 :
    compactCertificate284.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate284_coefficient2 :
    compactCertificate284.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate284_coefficient3 :
    compactCertificate284.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate284_coefficient4 :
    compactCertificate284.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate284_coefficients : ∀ r : Fin 5,
    compactCertificate284.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate284_coefficient0
  · exact compactCertificate284_coefficient1
  · exact compactCertificate284_coefficient2
  · exact compactCertificate284_coefficient3
  · exact compactCertificate284_coefficient4

theorem compactCertificate284_lower : (1 : ℚ) ≤ compactCertificate284.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate284, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate284_proves {t : ℝ} (ht : t ∈ compactCertificate284.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate284.proves compactCertificate284_states compactCertificate284_chunks
    compactCertificate284_coefficients compactCertificate284_lower ht

end Erdos232
