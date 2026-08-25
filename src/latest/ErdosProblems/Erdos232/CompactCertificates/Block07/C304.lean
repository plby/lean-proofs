/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate304 : CompactCertificate where
  left := 177
  right := 178
  center := 355 / 2
  grid := fun i =>
    match i.val with
    | 0 => 57
    | 1 => 42
    | 2 => 67
    | 3 => 12
    | 4 => 33
    | 5 => 89
    | 6 => 65
    | 7 => 112
    | 8 => 82
    | 9 => 126
    | 10 => 73
    | 11 => 130
    | 12 => 121
    | 13 => 86
    | 14 => 98
    | 15 => 82
    | 16 => 72
    | 17 => 105
    | 18 => 58
    | 19 => 49
    | 20 => 31
    | 21 => 16
    | 22 => 45
    | 23 => 61
    | 24 => 26
    | 25 => 105
    | _ => 70
  point := fun i =>
    match i.val with
    | 0 => 355 / 2
    | 1 => 104596557300971 / 800000000000
    | 2 => 33824377559243 / 160000000000
    | 3 => 30521014552897 / 800000000000
    | 4 => 81983738224909 / 800000000000
    | 5 => 222601797388953 / 800000000000
    | 6 => 163967476449889 / 800000000000
    | 7 => 280961065632997 / 800000000000
    | 8 => 206954649301423 / 800000000000
    | 9 => 317521652804929 / 800000000000
    | 10 => 183321211720441 / 800000000000
    | 11 => 325306707177869 / 800000000000
    | 12 => 303943723521761 / 800000000000
    | 13 => 216908582894513 / 800000000000
    | 14 => 245951214674727 / 800000000000
    | 15 => 205048481092663 / 800000000000
    | 16 => 181166551541923 / 800000000000
    | 17 => 52509127942377 / 160000000000
    | 18 => 145243011292619 / 800000000000
    | 19 => 123124109195059 / 800000000000
    | 20 => 77045350698577 / 800000000000
    | 21 => 41435245846959 / 800000000000
    | 22 => 112504752777877 / 800000000000
    | 23 => 153615621591029 / 800000000000
    | 24 => 64954649301423 / 800000000000
    | 25 => 264037043235983 / 800000000000
    | _ => 176364508332097 / 800000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (42376377204 / 1000000000000) (42376429704 / 1000000000000), orderedInterval (-42437600679 / 1000000000000) (-42437548179 / 1000000000000))
    | 1 => (orderedInterval (-28246069042 / 1000000000000) (-28246067388 / 1000000000000), orderedInterval (63914980985 / 1000000000000) (63914982639 / 1000000000000))
    | 2 => (orderedInterval (-54415610472 / 1000000000000) (-54415610043 / 1000000000000), orderedInterval (7224193501 / 1000000000000) (7224193930 / 1000000000000))
    | 3 => (orderedInterval (121926397086 / 1000000000000) (121926397087 / 1000000000000), orderedInterval (41058650321 / 1000000000000) (41058650322 / 1000000000000))
    | 4 => (orderedInterval (31323557836 / 1000000000000) (31323559608 / 1000000000000), orderedInterval (-72478766828 / 1000000000000) (-72478765056 / 1000000000000))
    | 5 => (orderedInterval (25591953575 / 1000000000000) (25591957313 / 1000000000000), orderedInterval (-40456093782 / 1000000000000) (-40456090045 / 1000000000000))
    | 6 => (orderedInterval (-55706730892 / 1000000000000) (-55706730846 / 1000000000000), orderedInterval (-1546124789 / 1000000000000) (-1546124744 / 1000000000000))
    | 7 => (orderedInterval (5434696907 / 1000000000000) (5434696908 / 1000000000000), orderedInterval (42219713980 / 1000000000000) (42219713981 / 1000000000000))
    | 8 => (orderedInterval (47438016907 / 1000000000000) (47438020875 / 1000000000000), orderedInterval (-14601546865 / 1000000000000) (-14601542898 / 1000000000000))
    | 9 => (orderedInterval (38537354772 / 1000000000000) (38537361392 / 1000000000000), orderedInterval (-10950058483 / 1000000000000) (-10950051863 / 1000000000000))
    | 10 => (orderedInterval (-29765795326 / 1000000000000) (-29765795325 / 1000000000000), orderedInterval (-43434025994 / 1000000000000) (-43434025993 / 1000000000000))
    | 11 => (orderedInterval (-33048419081 / 1000000000000) (-33048309113 / 1000000000000), orderedInterval (21798145283 / 1000000000000) (21798255251 / 1000000000000))
    | 12 => (orderedInterval (-22501885004 / 1000000000000) (-22501885003 / 1000000000000), orderedInterval (-34165285972 / 1000000000000) (-34165285971 / 1000000000000))
    | 13 => (orderedInterval (47733373343 / 1000000000000) (47733374398 / 1000000000000), orderedInterval (-8424435865 / 1000000000000) (-8424434809 / 1000000000000))
    | 14 => (orderedInterval (15515082924 / 1000000000000) (15515082925 / 1000000000000), orderedInterval (42753303488 / 1000000000000) (42753303489 / 1000000000000))
    | 15 => (orderedInterval (-24550432408 / 1000000000000) (-24550429951 / 1000000000000), orderedInterval (43419092989 / 1000000000000) (43419095447 / 1000000000000))
    | 16 => (orderedInterval (45948185970 / 1000000000000) (45948185971 / 1000000000000), orderedInterval (26355365127 / 1000000000000) (26355365128 / 1000000000000))
    | 17 => (orderedInterval (34504893281 / 1000000000000) (34504966244 / 1000000000000), orderedInterval (-27424972595 / 1000000000000) (-27424899632 / 1000000000000))
    | 18 => (orderedInterval (7447314732 / 1000000000000) (7447314733 / 1000000000000), orderedInterval (58725201829 / 1000000000000) (58725201830 / 1000000000000))
    | 19 => (orderedInterval (-43918717495 / 1000000000000) (-43918717494 / 1000000000000), orderedInterval (-46842322086 / 1000000000000) (-46842322085 / 1000000000000))
    | 20 => (orderedInterval (23916768785 / 1000000000000) (23916769278 / 1000000000000), orderedInterval (-77831308762 / 1000000000000) (-77831308269 / 1000000000000))
    | 21 => (orderedInterval (81812302546 / 1000000000000) (81812401590 / 1000000000000), orderedInterval (-75609905288 / 1000000000000) (-75609806245 / 1000000000000))
    | 22 => (orderedInterval (-2944720956 / 1000000000000) (-2944720953 / 1000000000000), orderedInterval (-67207383804 / 1000000000000) (-67207383801 / 1000000000000))
    | 23 => (orderedInterval (-52951339383 / 1000000000000) (-52951339382 / 1000000000000), orderedInterval (-22479341769 / 1000000000000) (-22479341767 / 1000000000000))
    | 24 => (orderedInterval (25808756692 / 1000000000000) (25808756693 / 1000000000000), orderedInterval (84545394690 / 1000000000000) (84545394691 / 1000000000000))
    | 25 => (orderedInterval (-36080909731 / 1000000000000) (-36080909730 / 1000000000000), orderedInterval (-24986253326 / 1000000000000) (-24986253325 / 1000000000000))
    | _ => (orderedInterval (52174171311 / 1000000000000) (52174171313 / 1000000000000), orderedInterval (12750031843 / 1000000000000) (12750031845 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (13340143825 / 1000000000000) (13340164688 / 1000000000000)
      | 1 => orderedInterval (-1998460244 / 1000000000000) (-1998459891 / 1000000000000)
      | 2 => orderedInterval (978855471 / 1000000000000) (978855578 / 1000000000000)
      | 3 => orderedInterval (-13751051839 / 1000000000000) (-13751034959 / 1000000000000)
      | 4 => orderedInterval (4841517785 / 1000000000000) (4841517907 / 1000000000000)
      | 5 => orderedInterval (-2029500736 / 1000000000000) (-2029498821 / 1000000000000)
      | 6 => orderedInterval (2073645005 / 1000000000000) (2073645067 / 1000000000000)
      | 7 => orderedInterval (2614261715 / 1000000000000) (2614263566 / 1000000000000)
      | _ => orderedInterval (-6696624769 / 1000000000000) (-6696624719 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-15877196789 / 1000000000000) (-15877175924 / 1000000000000)
      | 1 => orderedInterval (2884881837 / 1000000000000) (2884882316 / 1000000000000)
      | 2 => orderedInterval (-3090893260 / 1000000000000) (-3090893102 / 1000000000000)
      | 3 => orderedInterval (7295012909 / 1000000000000) (7295051498 / 1000000000000)
      | 4 => orderedInterval (-271421142 / 1000000000000) (-271420955 / 1000000000000)
      | 5 => orderedInterval (-2498507024 / 1000000000000) (-2498503504 / 1000000000000)
      | 6 => orderedInterval (-8680098226 / 1000000000000) (-8680098175 / 1000000000000)
      | 7 => orderedInterval (3479126748 / 1000000000000) (3479127302 / 1000000000000)
      | _ => orderedInterval (1043872842 / 1000000000000) (1043872913 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-12034834985 / 1000000000000) (-12034813998 / 1000000000000)
      | 1 => orderedInterval (4134485455 / 1000000000000) (4134486167 / 1000000000000)
      | 2 => orderedInterval (-1761586334 / 1000000000000) (-1761586098 / 1000000000000)
      | 3 => orderedInterval (62528729015 / 1000000000000) (62528817469 / 1000000000000)
      | 4 => orderedInterval (-12156280260 / 1000000000000) (-12156279969 / 1000000000000)
      | 5 => orderedInterval (1865138551 / 1000000000000) (1865145053 / 1000000000000)
      | 6 => orderedInterval (-803384702 / 1000000000000) (-803384657 / 1000000000000)
      | 7 => orderedInterval (-4682105179 / 1000000000000) (-4682105001 / 1000000000000)
      | _ => orderedInterval (4907572746 / 1000000000000) (4907572850 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (15933855008 / 1000000000000) (15933876001 / 1000000000000)
      | 1 => orderedInterval (-10588764676 / 1000000000000) (-10588763586 / 1000000000000)
      | 2 => orderedInterval (11189212360 / 1000000000000) (11189212715 / 1000000000000)
      | 3 => orderedInterval (-52437674672 / 1000000000000) (-52437472391 / 1000000000000)
      | 4 => orderedInterval (-2016448453 / 1000000000000) (-2016447998 / 1000000000000)
      | 5 => orderedInterval (6050001863 / 1000000000000) (6050013849 / 1000000000000)
      | 6 => orderedInterval (8728517804 / 1000000000000) (8728517845 / 1000000000000)
      | 7 => orderedInterval (-2947586686 / 1000000000000) (-2947586619 / 1000000000000)
      | _ => orderedInterval (-8568829851 / 1000000000000) (-8568829692 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (10114191659 / 1000000000000) (10114212779 / 1000000000000)
      | 1 => orderedInterval (-10743104528 / 1000000000000) (-10743102827 / 1000000000000)
      | 2 => orderedInterval (2477465176 / 1000000000000) (2477465717 / 1000000000000)
      | 3 => orderedInterval (-306123871905 / 1000000000000) (-306123408142 / 1000000000000)
      | 4 => orderedInterval (32417726668 / 1000000000000) (32417727384 / 1000000000000)
      | 5 => orderedInterval (2056734223 / 1000000000000) (2056756401 / 1000000000000)
      | 6 => orderedInterval (70798373 / 1000000000000) (70798413 / 1000000000000)
      | 7 => orderedInterval (5606379070 / 1000000000000) (5606379105 / 1000000000000)
      | _ => orderedInterval (11918588589 / 1000000000000) (11918588844 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-627213787 / 1000000000000) (-627171584 / 1000000000000)
    | 1 => orderedInterval (-15715222105 / 1000000000000) (-15715157631 / 1000000000000)
    | 2 => orderedInterval (41997734307 / 1000000000000) (41997851816 / 1000000000000)
    | 3 => orderedInterval (-34657717303 / 1000000000000) (-34657479876 / 1000000000000)
    | _ => orderedInterval (-252205092675 / 1000000000000) (-252204582326 / 1000000000000)

theorem compactCertificate304_stateChecks0 :
    compactCertificate304.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 57 12 (355 / 2)) (orderedInterval (42376377204 / 1000000000000) (42376429704 / 1000000000000), orderedInterval (-42437600679 / 1000000000000) (-42437548179 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 42 12 (104596557300971 / 800000000000)) (orderedInterval (-28246069042 / 1000000000000) (-28246067388 / 1000000000000), orderedInterval (63914980985 / 1000000000000) (63914982639 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (33824377559243 / 160000000000)) (orderedInterval (-54415610472 / 1000000000000) (-54415610043 / 1000000000000), orderedInterval (7224193501 / 1000000000000) (7224193930 / 1000000000000))) = true
  rfl'

theorem compactCertificate304_stateChecks1 :
    compactCertificate304.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 12 12 (30521014552897 / 800000000000)) (orderedInterval (121926397086 / 1000000000000) (121926397087 / 1000000000000), orderedInterval (41058650321 / 1000000000000) (41058650322 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 33 12 (81983738224909 / 800000000000)) (orderedInterval (31323557836 / 1000000000000) (31323559608 / 1000000000000), orderedInterval (-72478766828 / 1000000000000) (-72478765056 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 89 12 (222601797388953 / 800000000000)) (orderedInterval (25591953575 / 1000000000000) (25591957313 / 1000000000000), orderedInterval (-40456093782 / 1000000000000) (-40456090045 / 1000000000000))) = true
  rfl'

theorem compactCertificate304_stateChecks2 :
    compactCertificate304.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 65 12 (163967476449889 / 800000000000)) (orderedInterval (-55706730892 / 1000000000000) (-55706730846 / 1000000000000), orderedInterval (-1546124789 / 1000000000000) (-1546124744 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 112 12 (280961065632997 / 800000000000)) (orderedInterval (5434696907 / 1000000000000) (5434696908 / 1000000000000), orderedInterval (42219713980 / 1000000000000) (42219713981 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 82 12 (206954649301423 / 800000000000)) (orderedInterval (47438016907 / 1000000000000) (47438020875 / 1000000000000), orderedInterval (-14601546865 / 1000000000000) (-14601542898 / 1000000000000))) = true
  rfl'

theorem compactCertificate304_stateChecks3 :
    compactCertificate304.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 126 12 (317521652804929 / 800000000000)) (orderedInterval (38537354772 / 1000000000000) (38537361392 / 1000000000000), orderedInterval (-10950058483 / 1000000000000) (-10950051863 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 73 12 (183321211720441 / 800000000000)) (orderedInterval (-29765795326 / 1000000000000) (-29765795325 / 1000000000000), orderedInterval (-43434025994 / 1000000000000) (-43434025993 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 130 12 (325306707177869 / 800000000000)) (orderedInterval (-33048419081 / 1000000000000) (-33048309113 / 1000000000000), orderedInterval (21798145283 / 1000000000000) (21798255251 / 1000000000000))) = true
  rfl'

theorem compactCertificate304_stateChecks4 :
    compactCertificate304.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 121 12 (303943723521761 / 800000000000)) (orderedInterval (-22501885004 / 1000000000000) (-22501885003 / 1000000000000), orderedInterval (-34165285972 / 1000000000000) (-34165285971 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 86 12 (216908582894513 / 800000000000)) (orderedInterval (47733373343 / 1000000000000) (47733374398 / 1000000000000), orderedInterval (-8424435865 / 1000000000000) (-8424434809 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 98 12 (245951214674727 / 800000000000)) (orderedInterval (15515082924 / 1000000000000) (15515082925 / 1000000000000), orderedInterval (42753303488 / 1000000000000) (42753303489 / 1000000000000))) = true
  rfl'

theorem compactCertificate304_stateChecks5 :
    compactCertificate304.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 82 12 (205048481092663 / 800000000000)) (orderedInterval (-24550432408 / 1000000000000) (-24550429951 / 1000000000000), orderedInterval (43419092989 / 1000000000000) (43419095447 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 72 12 (181166551541923 / 800000000000)) (orderedInterval (45948185970 / 1000000000000) (45948185971 / 1000000000000), orderedInterval (26355365127 / 1000000000000) (26355365128 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 105 12 (52509127942377 / 160000000000)) (orderedInterval (34504893281 / 1000000000000) (34504966244 / 1000000000000), orderedInterval (-27424972595 / 1000000000000) (-27424899632 / 1000000000000))) = true
  rfl'

theorem compactCertificate304_stateChecks6 :
    compactCertificate304.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (145243011292619 / 800000000000)) (orderedInterval (7447314732 / 1000000000000) (7447314733 / 1000000000000), orderedInterval (58725201829 / 1000000000000) (58725201830 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 49 12 (123124109195059 / 800000000000)) (orderedInterval (-43918717495 / 1000000000000) (-43918717494 / 1000000000000), orderedInterval (-46842322086 / 1000000000000) (-46842322085 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 31 12 (77045350698577 / 800000000000)) (orderedInterval (23916768785 / 1000000000000) (23916769278 / 1000000000000), orderedInterval (-77831308762 / 1000000000000) (-77831308269 / 1000000000000))) = true
  rfl'

theorem compactCertificate304_stateChecks7 :
    compactCertificate304.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 16 12 (41435245846959 / 800000000000)) (orderedInterval (81812302546 / 1000000000000) (81812401590 / 1000000000000), orderedInterval (-75609905288 / 1000000000000) (-75609806245 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (112504752777877 / 800000000000)) (orderedInterval (-2944720956 / 1000000000000) (-2944720953 / 1000000000000), orderedInterval (-67207383804 / 1000000000000) (-67207383801 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 61 12 (153615621591029 / 800000000000)) (orderedInterval (-52951339383 / 1000000000000) (-52951339382 / 1000000000000), orderedInterval (-22479341769 / 1000000000000) (-22479341767 / 1000000000000))) = true
  rfl'

theorem compactCertificate304_stateChecks8 :
    compactCertificate304.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 26 12 (64954649301423 / 800000000000)) (orderedInterval (25808756692 / 1000000000000) (25808756693 / 1000000000000), orderedInterval (84545394690 / 1000000000000) (84545394691 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 105 12 (264037043235983 / 800000000000)) (orderedInterval (-36080909731 / 1000000000000) (-36080909730 / 1000000000000), orderedInterval (-24986253326 / 1000000000000) (-24986253325 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (176364508332097 / 800000000000)) (orderedInterval (52174171311 / 1000000000000) (52174171313 / 1000000000000), orderedInterval (12750031843 / 1000000000000) (12750031845 / 1000000000000))) = true
  rfl'

theorem compactCertificate304_states : ∀ j,
    BesselStateValid (compactCertificate304.point j) (compactCertificate304.state j) :=
  compactCertificate304.statesValid_of_checks3 compactCertificate304_stateChecks0
    compactCertificate304_stateChecks1 compactCertificate304_stateChecks2
    compactCertificate304_stateChecks3 compactCertificate304_stateChecks4
    compactCertificate304_stateChecks5 compactCertificate304_stateChecks6
    compactCertificate304_stateChecks7 compactCertificate304_stateChecks8

theorem compactCertificate304_chunkChecks0_0 :
    compactCertificate304.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (355 / 2) 0 (IntervalRat.scale (355 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (42376377204 / 1000000000000) (42376429704 / 1000000000000), orderedInterval (-42437600679 / 1000000000000) (-42437548179 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (104596557300971 / 800000000000) 0 (IntervalRat.scale (355 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-28246069042 / 1000000000000) (-28246067388 / 1000000000000), orderedInterval (63914980985 / 1000000000000) (63914982639 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (33824377559243 / 160000000000) 0 (IntervalRat.scale (355 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-54415610472 / 1000000000000) (-54415610043 / 1000000000000), orderedInterval (7224193501 / 1000000000000) (7224193930 / 1000000000000)))) (orderedInterval (13340143825 / 1000000000000) (13340164688 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (30521014552897 / 800000000000) 0 (IntervalRat.scale (355 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (121926397086 / 1000000000000) (121926397087 / 1000000000000), orderedInterval (41058650321 / 1000000000000) (41058650322 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (81983738224909 / 800000000000) 0 (IntervalRat.scale (355 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (31323557836 / 1000000000000) (31323559608 / 1000000000000), orderedInterval (-72478766828 / 1000000000000) (-72478765056 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (222601797388953 / 800000000000) 0 (IntervalRat.scale (355 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (25591953575 / 1000000000000) (25591957313 / 1000000000000), orderedInterval (-40456093782 / 1000000000000) (-40456090045 / 1000000000000)))) (orderedInterval (-1998460244 / 1000000000000) (-1998459891 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (163967476449889 / 800000000000) 0 (IntervalRat.scale (355 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-55706730892 / 1000000000000) (-55706730846 / 1000000000000), orderedInterval (-1546124789 / 1000000000000) (-1546124744 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (280961065632997 / 800000000000) 0 (IntervalRat.scale (355 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (5434696907 / 1000000000000) (5434696908 / 1000000000000), orderedInterval (42219713980 / 1000000000000) (42219713981 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (206954649301423 / 800000000000) 0 (IntervalRat.scale (355 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (47438016907 / 1000000000000) (47438020875 / 1000000000000), orderedInterval (-14601546865 / 1000000000000) (-14601542898 / 1000000000000)))) (orderedInterval (978855471 / 1000000000000) (978855578 / 1000000000000))) = true
  rfl'

theorem compactCertificate304_chunkChecks0_1 :
    compactCertificate304.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (317521652804929 / 800000000000) 0 (IntervalRat.scale (355 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (38537354772 / 1000000000000) (38537361392 / 1000000000000), orderedInterval (-10950058483 / 1000000000000) (-10950051863 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (183321211720441 / 800000000000) 0 (IntervalRat.scale (355 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-29765795326 / 1000000000000) (-29765795325 / 1000000000000), orderedInterval (-43434025994 / 1000000000000) (-43434025993 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (325306707177869 / 800000000000) 0 (IntervalRat.scale (355 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-33048419081 / 1000000000000) (-33048309113 / 1000000000000), orderedInterval (21798145283 / 1000000000000) (21798255251 / 1000000000000)))) (orderedInterval (-13751051839 / 1000000000000) (-13751034959 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (303943723521761 / 800000000000) 0 (IntervalRat.scale (355 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-22501885004 / 1000000000000) (-22501885003 / 1000000000000), orderedInterval (-34165285972 / 1000000000000) (-34165285971 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (216908582894513 / 800000000000) 0 (IntervalRat.scale (355 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (47733373343 / 1000000000000) (47733374398 / 1000000000000), orderedInterval (-8424435865 / 1000000000000) (-8424434809 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (245951214674727 / 800000000000) 0 (IntervalRat.scale (355 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (15515082924 / 1000000000000) (15515082925 / 1000000000000), orderedInterval (42753303488 / 1000000000000) (42753303489 / 1000000000000)))) (orderedInterval (4841517785 / 1000000000000) (4841517907 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (205048481092663 / 800000000000) 0 (IntervalRat.scale (355 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-24550432408 / 1000000000000) (-24550429951 / 1000000000000), orderedInterval (43419092989 / 1000000000000) (43419095447 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (181166551541923 / 800000000000) 0 (IntervalRat.scale (355 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (45948185970 / 1000000000000) (45948185971 / 1000000000000), orderedInterval (26355365127 / 1000000000000) (26355365128 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (52509127942377 / 160000000000) 0 (IntervalRat.scale (355 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (34504893281 / 1000000000000) (34504966244 / 1000000000000), orderedInterval (-27424972595 / 1000000000000) (-27424899632 / 1000000000000)))) (orderedInterval (-2029500736 / 1000000000000) (-2029498821 / 1000000000000))) = true
  rfl'

theorem compactCertificate304_chunkChecks0_2 :
    compactCertificate304.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (145243011292619 / 800000000000) 0 (IntervalRat.scale (355 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (7447314732 / 1000000000000) (7447314733 / 1000000000000), orderedInterval (58725201829 / 1000000000000) (58725201830 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (123124109195059 / 800000000000) 0 (IntervalRat.scale (355 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-43918717495 / 1000000000000) (-43918717494 / 1000000000000), orderedInterval (-46842322086 / 1000000000000) (-46842322085 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (77045350698577 / 800000000000) 0 (IntervalRat.scale (355 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (23916768785 / 1000000000000) (23916769278 / 1000000000000), orderedInterval (-77831308762 / 1000000000000) (-77831308269 / 1000000000000)))) (orderedInterval (2073645005 / 1000000000000) (2073645067 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (41435245846959 / 800000000000) 0 (IntervalRat.scale (355 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (81812302546 / 1000000000000) (81812401590 / 1000000000000), orderedInterval (-75609905288 / 1000000000000) (-75609806245 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (112504752777877 / 800000000000) 0 (IntervalRat.scale (355 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-2944720956 / 1000000000000) (-2944720953 / 1000000000000), orderedInterval (-67207383804 / 1000000000000) (-67207383801 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (153615621591029 / 800000000000) 0 (IntervalRat.scale (355 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-52951339383 / 1000000000000) (-52951339382 / 1000000000000), orderedInterval (-22479341769 / 1000000000000) (-22479341767 / 1000000000000)))) (orderedInterval (2614261715 / 1000000000000) (2614263566 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (64954649301423 / 800000000000) 0 (IntervalRat.scale (355 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (25808756692 / 1000000000000) (25808756693 / 1000000000000), orderedInterval (84545394690 / 1000000000000) (84545394691 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (264037043235983 / 800000000000) 0 (IntervalRat.scale (355 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-36080909731 / 1000000000000) (-36080909730 / 1000000000000), orderedInterval (-24986253326 / 1000000000000) (-24986253325 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (176364508332097 / 800000000000) 0 (IntervalRat.scale (355 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (52174171311 / 1000000000000) (52174171313 / 1000000000000), orderedInterval (12750031843 / 1000000000000) (12750031845 / 1000000000000)))) (orderedInterval (-6696624769 / 1000000000000) (-6696624719 / 1000000000000))) = true
  rfl'

theorem compactCertificate304_chunkChecks0 :
    compactCertificate304.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate304.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate304_chunkChecks0_0
    compactCertificate304_chunkChecks0_1 compactCertificate304_chunkChecks0_2

theorem compactCertificate304_chunkChecks1_0 :
    compactCertificate304.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (355 / 2) 1 (IntervalRat.scale (355 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (42376377204 / 1000000000000) (42376429704 / 1000000000000), orderedInterval (-42437600679 / 1000000000000) (-42437548179 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (104596557300971 / 800000000000) 1 (IntervalRat.scale (355 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-28246069042 / 1000000000000) (-28246067388 / 1000000000000), orderedInterval (63914980985 / 1000000000000) (63914982639 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (33824377559243 / 160000000000) 1 (IntervalRat.scale (355 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-54415610472 / 1000000000000) (-54415610043 / 1000000000000), orderedInterval (7224193501 / 1000000000000) (7224193930 / 1000000000000)))) (orderedInterval (-15877196789 / 1000000000000) (-15877175924 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (30521014552897 / 800000000000) 1 (IntervalRat.scale (355 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (121926397086 / 1000000000000) (121926397087 / 1000000000000), orderedInterval (41058650321 / 1000000000000) (41058650322 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (81983738224909 / 800000000000) 1 (IntervalRat.scale (355 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (31323557836 / 1000000000000) (31323559608 / 1000000000000), orderedInterval (-72478766828 / 1000000000000) (-72478765056 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (222601797388953 / 800000000000) 1 (IntervalRat.scale (355 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (25591953575 / 1000000000000) (25591957313 / 1000000000000), orderedInterval (-40456093782 / 1000000000000) (-40456090045 / 1000000000000)))) (orderedInterval (2884881837 / 1000000000000) (2884882316 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (163967476449889 / 800000000000) 1 (IntervalRat.scale (355 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-55706730892 / 1000000000000) (-55706730846 / 1000000000000), orderedInterval (-1546124789 / 1000000000000) (-1546124744 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (280961065632997 / 800000000000) 1 (IntervalRat.scale (355 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (5434696907 / 1000000000000) (5434696908 / 1000000000000), orderedInterval (42219713980 / 1000000000000) (42219713981 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (206954649301423 / 800000000000) 1 (IntervalRat.scale (355 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (47438016907 / 1000000000000) (47438020875 / 1000000000000), orderedInterval (-14601546865 / 1000000000000) (-14601542898 / 1000000000000)))) (orderedInterval (-3090893260 / 1000000000000) (-3090893102 / 1000000000000))) = true
  rfl'

theorem compactCertificate304_chunkChecks1_1 :
    compactCertificate304.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (317521652804929 / 800000000000) 1 (IntervalRat.scale (355 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (38537354772 / 1000000000000) (38537361392 / 1000000000000), orderedInterval (-10950058483 / 1000000000000) (-10950051863 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (183321211720441 / 800000000000) 1 (IntervalRat.scale (355 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-29765795326 / 1000000000000) (-29765795325 / 1000000000000), orderedInterval (-43434025994 / 1000000000000) (-43434025993 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (325306707177869 / 800000000000) 1 (IntervalRat.scale (355 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-33048419081 / 1000000000000) (-33048309113 / 1000000000000), orderedInterval (21798145283 / 1000000000000) (21798255251 / 1000000000000)))) (orderedInterval (7295012909 / 1000000000000) (7295051498 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (303943723521761 / 800000000000) 1 (IntervalRat.scale (355 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-22501885004 / 1000000000000) (-22501885003 / 1000000000000), orderedInterval (-34165285972 / 1000000000000) (-34165285971 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (216908582894513 / 800000000000) 1 (IntervalRat.scale (355 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (47733373343 / 1000000000000) (47733374398 / 1000000000000), orderedInterval (-8424435865 / 1000000000000) (-8424434809 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (245951214674727 / 800000000000) 1 (IntervalRat.scale (355 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (15515082924 / 1000000000000) (15515082925 / 1000000000000), orderedInterval (42753303488 / 1000000000000) (42753303489 / 1000000000000)))) (orderedInterval (-271421142 / 1000000000000) (-271420955 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (205048481092663 / 800000000000) 1 (IntervalRat.scale (355 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-24550432408 / 1000000000000) (-24550429951 / 1000000000000), orderedInterval (43419092989 / 1000000000000) (43419095447 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (181166551541923 / 800000000000) 1 (IntervalRat.scale (355 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (45948185970 / 1000000000000) (45948185971 / 1000000000000), orderedInterval (26355365127 / 1000000000000) (26355365128 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (52509127942377 / 160000000000) 1 (IntervalRat.scale (355 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (34504893281 / 1000000000000) (34504966244 / 1000000000000), orderedInterval (-27424972595 / 1000000000000) (-27424899632 / 1000000000000)))) (orderedInterval (-2498507024 / 1000000000000) (-2498503504 / 1000000000000))) = true
  rfl'

theorem compactCertificate304_chunkChecks1_2 :
    compactCertificate304.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (145243011292619 / 800000000000) 1 (IntervalRat.scale (355 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (7447314732 / 1000000000000) (7447314733 / 1000000000000), orderedInterval (58725201829 / 1000000000000) (58725201830 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (123124109195059 / 800000000000) 1 (IntervalRat.scale (355 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-43918717495 / 1000000000000) (-43918717494 / 1000000000000), orderedInterval (-46842322086 / 1000000000000) (-46842322085 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (77045350698577 / 800000000000) 1 (IntervalRat.scale (355 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (23916768785 / 1000000000000) (23916769278 / 1000000000000), orderedInterval (-77831308762 / 1000000000000) (-77831308269 / 1000000000000)))) (orderedInterval (-8680098226 / 1000000000000) (-8680098175 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (41435245846959 / 800000000000) 1 (IntervalRat.scale (355 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (81812302546 / 1000000000000) (81812401590 / 1000000000000), orderedInterval (-75609905288 / 1000000000000) (-75609806245 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (112504752777877 / 800000000000) 1 (IntervalRat.scale (355 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-2944720956 / 1000000000000) (-2944720953 / 1000000000000), orderedInterval (-67207383804 / 1000000000000) (-67207383801 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (153615621591029 / 800000000000) 1 (IntervalRat.scale (355 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-52951339383 / 1000000000000) (-52951339382 / 1000000000000), orderedInterval (-22479341769 / 1000000000000) (-22479341767 / 1000000000000)))) (orderedInterval (3479126748 / 1000000000000) (3479127302 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (64954649301423 / 800000000000) 1 (IntervalRat.scale (355 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (25808756692 / 1000000000000) (25808756693 / 1000000000000), orderedInterval (84545394690 / 1000000000000) (84545394691 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (264037043235983 / 800000000000) 1 (IntervalRat.scale (355 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-36080909731 / 1000000000000) (-36080909730 / 1000000000000), orderedInterval (-24986253326 / 1000000000000) (-24986253325 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (176364508332097 / 800000000000) 1 (IntervalRat.scale (355 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (52174171311 / 1000000000000) (52174171313 / 1000000000000), orderedInterval (12750031843 / 1000000000000) (12750031845 / 1000000000000)))) (orderedInterval (1043872842 / 1000000000000) (1043872913 / 1000000000000))) = true
  rfl'

theorem compactCertificate304_chunkChecks1 :
    compactCertificate304.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate304.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate304_chunkChecks1_0
    compactCertificate304_chunkChecks1_1 compactCertificate304_chunkChecks1_2

theorem compactCertificate304_chunkChecks2_0 :
    compactCertificate304.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (355 / 2) 2 (IntervalRat.scale (355 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (42376377204 / 1000000000000) (42376429704 / 1000000000000), orderedInterval (-42437600679 / 1000000000000) (-42437548179 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (104596557300971 / 800000000000) 2 (IntervalRat.scale (355 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-28246069042 / 1000000000000) (-28246067388 / 1000000000000), orderedInterval (63914980985 / 1000000000000) (63914982639 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (33824377559243 / 160000000000) 2 (IntervalRat.scale (355 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-54415610472 / 1000000000000) (-54415610043 / 1000000000000), orderedInterval (7224193501 / 1000000000000) (7224193930 / 1000000000000)))) (orderedInterval (-12034834985 / 1000000000000) (-12034813998 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (30521014552897 / 800000000000) 2 (IntervalRat.scale (355 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (121926397086 / 1000000000000) (121926397087 / 1000000000000), orderedInterval (41058650321 / 1000000000000) (41058650322 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (81983738224909 / 800000000000) 2 (IntervalRat.scale (355 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (31323557836 / 1000000000000) (31323559608 / 1000000000000), orderedInterval (-72478766828 / 1000000000000) (-72478765056 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (222601797388953 / 800000000000) 2 (IntervalRat.scale (355 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (25591953575 / 1000000000000) (25591957313 / 1000000000000), orderedInterval (-40456093782 / 1000000000000) (-40456090045 / 1000000000000)))) (orderedInterval (4134485455 / 1000000000000) (4134486167 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (163967476449889 / 800000000000) 2 (IntervalRat.scale (355 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-55706730892 / 1000000000000) (-55706730846 / 1000000000000), orderedInterval (-1546124789 / 1000000000000) (-1546124744 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (280961065632997 / 800000000000) 2 (IntervalRat.scale (355 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (5434696907 / 1000000000000) (5434696908 / 1000000000000), orderedInterval (42219713980 / 1000000000000) (42219713981 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (206954649301423 / 800000000000) 2 (IntervalRat.scale (355 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (47438016907 / 1000000000000) (47438020875 / 1000000000000), orderedInterval (-14601546865 / 1000000000000) (-14601542898 / 1000000000000)))) (orderedInterval (-1761586334 / 1000000000000) (-1761586098 / 1000000000000))) = true
  rfl'

theorem compactCertificate304_chunkChecks2_1 :
    compactCertificate304.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (317521652804929 / 800000000000) 2 (IntervalRat.scale (355 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (38537354772 / 1000000000000) (38537361392 / 1000000000000), orderedInterval (-10950058483 / 1000000000000) (-10950051863 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (183321211720441 / 800000000000) 2 (IntervalRat.scale (355 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-29765795326 / 1000000000000) (-29765795325 / 1000000000000), orderedInterval (-43434025994 / 1000000000000) (-43434025993 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (325306707177869 / 800000000000) 2 (IntervalRat.scale (355 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-33048419081 / 1000000000000) (-33048309113 / 1000000000000), orderedInterval (21798145283 / 1000000000000) (21798255251 / 1000000000000)))) (orderedInterval (62528729015 / 1000000000000) (62528817469 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (303943723521761 / 800000000000) 2 (IntervalRat.scale (355 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-22501885004 / 1000000000000) (-22501885003 / 1000000000000), orderedInterval (-34165285972 / 1000000000000) (-34165285971 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (216908582894513 / 800000000000) 2 (IntervalRat.scale (355 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (47733373343 / 1000000000000) (47733374398 / 1000000000000), orderedInterval (-8424435865 / 1000000000000) (-8424434809 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (245951214674727 / 800000000000) 2 (IntervalRat.scale (355 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (15515082924 / 1000000000000) (15515082925 / 1000000000000), orderedInterval (42753303488 / 1000000000000) (42753303489 / 1000000000000)))) (orderedInterval (-12156280260 / 1000000000000) (-12156279969 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (205048481092663 / 800000000000) 2 (IntervalRat.scale (355 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-24550432408 / 1000000000000) (-24550429951 / 1000000000000), orderedInterval (43419092989 / 1000000000000) (43419095447 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (181166551541923 / 800000000000) 2 (IntervalRat.scale (355 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (45948185970 / 1000000000000) (45948185971 / 1000000000000), orderedInterval (26355365127 / 1000000000000) (26355365128 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (52509127942377 / 160000000000) 2 (IntervalRat.scale (355 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (34504893281 / 1000000000000) (34504966244 / 1000000000000), orderedInterval (-27424972595 / 1000000000000) (-27424899632 / 1000000000000)))) (orderedInterval (1865138551 / 1000000000000) (1865145053 / 1000000000000))) = true
  rfl'

theorem compactCertificate304_chunkChecks2_2 :
    compactCertificate304.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (145243011292619 / 800000000000) 2 (IntervalRat.scale (355 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (7447314732 / 1000000000000) (7447314733 / 1000000000000), orderedInterval (58725201829 / 1000000000000) (58725201830 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (123124109195059 / 800000000000) 2 (IntervalRat.scale (355 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-43918717495 / 1000000000000) (-43918717494 / 1000000000000), orderedInterval (-46842322086 / 1000000000000) (-46842322085 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (77045350698577 / 800000000000) 2 (IntervalRat.scale (355 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (23916768785 / 1000000000000) (23916769278 / 1000000000000), orderedInterval (-77831308762 / 1000000000000) (-77831308269 / 1000000000000)))) (orderedInterval (-803384702 / 1000000000000) (-803384657 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (41435245846959 / 800000000000) 2 (IntervalRat.scale (355 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (81812302546 / 1000000000000) (81812401590 / 1000000000000), orderedInterval (-75609905288 / 1000000000000) (-75609806245 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (112504752777877 / 800000000000) 2 (IntervalRat.scale (355 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-2944720956 / 1000000000000) (-2944720953 / 1000000000000), orderedInterval (-67207383804 / 1000000000000) (-67207383801 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (153615621591029 / 800000000000) 2 (IntervalRat.scale (355 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-52951339383 / 1000000000000) (-52951339382 / 1000000000000), orderedInterval (-22479341769 / 1000000000000) (-22479341767 / 1000000000000)))) (orderedInterval (-4682105179 / 1000000000000) (-4682105001 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (64954649301423 / 800000000000) 2 (IntervalRat.scale (355 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (25808756692 / 1000000000000) (25808756693 / 1000000000000), orderedInterval (84545394690 / 1000000000000) (84545394691 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (264037043235983 / 800000000000) 2 (IntervalRat.scale (355 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-36080909731 / 1000000000000) (-36080909730 / 1000000000000), orderedInterval (-24986253326 / 1000000000000) (-24986253325 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (176364508332097 / 800000000000) 2 (IntervalRat.scale (355 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (52174171311 / 1000000000000) (52174171313 / 1000000000000), orderedInterval (12750031843 / 1000000000000) (12750031845 / 1000000000000)))) (orderedInterval (4907572746 / 1000000000000) (4907572850 / 1000000000000))) = true
  rfl'

theorem compactCertificate304_chunkChecks2 :
    compactCertificate304.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate304.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate304_chunkChecks2_0
    compactCertificate304_chunkChecks2_1 compactCertificate304_chunkChecks2_2

theorem compactCertificate304_chunkChecks3_0 :
    compactCertificate304.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (355 / 2) 3 (IntervalRat.scale (355 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (42376377204 / 1000000000000) (42376429704 / 1000000000000), orderedInterval (-42437600679 / 1000000000000) (-42437548179 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (104596557300971 / 800000000000) 3 (IntervalRat.scale (355 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-28246069042 / 1000000000000) (-28246067388 / 1000000000000), orderedInterval (63914980985 / 1000000000000) (63914982639 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (33824377559243 / 160000000000) 3 (IntervalRat.scale (355 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-54415610472 / 1000000000000) (-54415610043 / 1000000000000), orderedInterval (7224193501 / 1000000000000) (7224193930 / 1000000000000)))) (orderedInterval (15933855008 / 1000000000000) (15933876001 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (30521014552897 / 800000000000) 3 (IntervalRat.scale (355 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (121926397086 / 1000000000000) (121926397087 / 1000000000000), orderedInterval (41058650321 / 1000000000000) (41058650322 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (81983738224909 / 800000000000) 3 (IntervalRat.scale (355 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (31323557836 / 1000000000000) (31323559608 / 1000000000000), orderedInterval (-72478766828 / 1000000000000) (-72478765056 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (222601797388953 / 800000000000) 3 (IntervalRat.scale (355 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (25591953575 / 1000000000000) (25591957313 / 1000000000000), orderedInterval (-40456093782 / 1000000000000) (-40456090045 / 1000000000000)))) (orderedInterval (-10588764676 / 1000000000000) (-10588763586 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (163967476449889 / 800000000000) 3 (IntervalRat.scale (355 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-55706730892 / 1000000000000) (-55706730846 / 1000000000000), orderedInterval (-1546124789 / 1000000000000) (-1546124744 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (280961065632997 / 800000000000) 3 (IntervalRat.scale (355 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (5434696907 / 1000000000000) (5434696908 / 1000000000000), orderedInterval (42219713980 / 1000000000000) (42219713981 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (206954649301423 / 800000000000) 3 (IntervalRat.scale (355 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (47438016907 / 1000000000000) (47438020875 / 1000000000000), orderedInterval (-14601546865 / 1000000000000) (-14601542898 / 1000000000000)))) (orderedInterval (11189212360 / 1000000000000) (11189212715 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate304_chunkChecks3_1 :
    compactCertificate304.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (317521652804929 / 800000000000) 3 (IntervalRat.scale (355 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (38537354772 / 1000000000000) (38537361392 / 1000000000000), orderedInterval (-10950058483 / 1000000000000) (-10950051863 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (183321211720441 / 800000000000) 3 (IntervalRat.scale (355 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-29765795326 / 1000000000000) (-29765795325 / 1000000000000), orderedInterval (-43434025994 / 1000000000000) (-43434025993 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (325306707177869 / 800000000000) 3 (IntervalRat.scale (355 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-33048419081 / 1000000000000) (-33048309113 / 1000000000000), orderedInterval (21798145283 / 1000000000000) (21798255251 / 1000000000000)))) (orderedInterval (-52437674672 / 1000000000000) (-52437472391 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (303943723521761 / 800000000000) 3 (IntervalRat.scale (355 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-22501885004 / 1000000000000) (-22501885003 / 1000000000000), orderedInterval (-34165285972 / 1000000000000) (-34165285971 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (216908582894513 / 800000000000) 3 (IntervalRat.scale (355 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (47733373343 / 1000000000000) (47733374398 / 1000000000000), orderedInterval (-8424435865 / 1000000000000) (-8424434809 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (245951214674727 / 800000000000) 3 (IntervalRat.scale (355 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (15515082924 / 1000000000000) (15515082925 / 1000000000000), orderedInterval (42753303488 / 1000000000000) (42753303489 / 1000000000000)))) (orderedInterval (-2016448453 / 1000000000000) (-2016447998 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (205048481092663 / 800000000000) 3 (IntervalRat.scale (355 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-24550432408 / 1000000000000) (-24550429951 / 1000000000000), orderedInterval (43419092989 / 1000000000000) (43419095447 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (181166551541923 / 800000000000) 3 (IntervalRat.scale (355 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (45948185970 / 1000000000000) (45948185971 / 1000000000000), orderedInterval (26355365127 / 1000000000000) (26355365128 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (52509127942377 / 160000000000) 3 (IntervalRat.scale (355 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (34504893281 / 1000000000000) (34504966244 / 1000000000000), orderedInterval (-27424972595 / 1000000000000) (-27424899632 / 1000000000000)))) (orderedInterval (6050001863 / 1000000000000) (6050013849 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate304_chunkChecks3_2 :
    compactCertificate304.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (145243011292619 / 800000000000) 3 (IntervalRat.scale (355 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (7447314732 / 1000000000000) (7447314733 / 1000000000000), orderedInterval (58725201829 / 1000000000000) (58725201830 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (123124109195059 / 800000000000) 3 (IntervalRat.scale (355 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-43918717495 / 1000000000000) (-43918717494 / 1000000000000), orderedInterval (-46842322086 / 1000000000000) (-46842322085 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (77045350698577 / 800000000000) 3 (IntervalRat.scale (355 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (23916768785 / 1000000000000) (23916769278 / 1000000000000), orderedInterval (-77831308762 / 1000000000000) (-77831308269 / 1000000000000)))) (orderedInterval (8728517804 / 1000000000000) (8728517845 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (41435245846959 / 800000000000) 3 (IntervalRat.scale (355 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (81812302546 / 1000000000000) (81812401590 / 1000000000000), orderedInterval (-75609905288 / 1000000000000) (-75609806245 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (112504752777877 / 800000000000) 3 (IntervalRat.scale (355 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-2944720956 / 1000000000000) (-2944720953 / 1000000000000), orderedInterval (-67207383804 / 1000000000000) (-67207383801 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (153615621591029 / 800000000000) 3 (IntervalRat.scale (355 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-52951339383 / 1000000000000) (-52951339382 / 1000000000000), orderedInterval (-22479341769 / 1000000000000) (-22479341767 / 1000000000000)))) (orderedInterval (-2947586686 / 1000000000000) (-2947586619 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (64954649301423 / 800000000000) 3 (IntervalRat.scale (355 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (25808756692 / 1000000000000) (25808756693 / 1000000000000), orderedInterval (84545394690 / 1000000000000) (84545394691 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (264037043235983 / 800000000000) 3 (IntervalRat.scale (355 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-36080909731 / 1000000000000) (-36080909730 / 1000000000000), orderedInterval (-24986253326 / 1000000000000) (-24986253325 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (176364508332097 / 800000000000) 3 (IntervalRat.scale (355 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (52174171311 / 1000000000000) (52174171313 / 1000000000000), orderedInterval (12750031843 / 1000000000000) (12750031845 / 1000000000000)))) (orderedInterval (-8568829851 / 1000000000000) (-8568829692 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate304_chunkChecks3 :
    compactCertificate304.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate304.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate304_chunkChecks3_0
    compactCertificate304_chunkChecks3_1 compactCertificate304_chunkChecks3_2

theorem compactCertificate304_chunkChecks4_0 :
    compactCertificate304.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (355 / 2) 4 (IntervalRat.scale (355 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (42376377204 / 1000000000000) (42376429704 / 1000000000000), orderedInterval (-42437600679 / 1000000000000) (-42437548179 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (104596557300971 / 800000000000) 4 (IntervalRat.scale (355 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-28246069042 / 1000000000000) (-28246067388 / 1000000000000), orderedInterval (63914980985 / 1000000000000) (63914982639 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (33824377559243 / 160000000000) 4 (IntervalRat.scale (355 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-54415610472 / 1000000000000) (-54415610043 / 1000000000000), orderedInterval (7224193501 / 1000000000000) (7224193930 / 1000000000000)))) (orderedInterval (10114191659 / 1000000000000) (10114212779 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (30521014552897 / 800000000000) 4 (IntervalRat.scale (355 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (121926397086 / 1000000000000) (121926397087 / 1000000000000), orderedInterval (41058650321 / 1000000000000) (41058650322 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (81983738224909 / 800000000000) 4 (IntervalRat.scale (355 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (31323557836 / 1000000000000) (31323559608 / 1000000000000), orderedInterval (-72478766828 / 1000000000000) (-72478765056 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (222601797388953 / 800000000000) 4 (IntervalRat.scale (355 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (25591953575 / 1000000000000) (25591957313 / 1000000000000), orderedInterval (-40456093782 / 1000000000000) (-40456090045 / 1000000000000)))) (orderedInterval (-10743104528 / 1000000000000) (-10743102827 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (163967476449889 / 800000000000) 4 (IntervalRat.scale (355 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-55706730892 / 1000000000000) (-55706730846 / 1000000000000), orderedInterval (-1546124789 / 1000000000000) (-1546124744 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (280961065632997 / 800000000000) 4 (IntervalRat.scale (355 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (5434696907 / 1000000000000) (5434696908 / 1000000000000), orderedInterval (42219713980 / 1000000000000) (42219713981 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (206954649301423 / 800000000000) 4 (IntervalRat.scale (355 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (47438016907 / 1000000000000) (47438020875 / 1000000000000), orderedInterval (-14601546865 / 1000000000000) (-14601542898 / 1000000000000)))) (orderedInterval (2477465176 / 1000000000000) (2477465717 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate304_chunkChecks4_1 :
    compactCertificate304.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (317521652804929 / 800000000000) 4 (IntervalRat.scale (355 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (38537354772 / 1000000000000) (38537361392 / 1000000000000), orderedInterval (-10950058483 / 1000000000000) (-10950051863 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (183321211720441 / 800000000000) 4 (IntervalRat.scale (355 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-29765795326 / 1000000000000) (-29765795325 / 1000000000000), orderedInterval (-43434025994 / 1000000000000) (-43434025993 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (325306707177869 / 800000000000) 4 (IntervalRat.scale (355 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-33048419081 / 1000000000000) (-33048309113 / 1000000000000), orderedInterval (21798145283 / 1000000000000) (21798255251 / 1000000000000)))) (orderedInterval (-306123871905 / 1000000000000) (-306123408142 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (303943723521761 / 800000000000) 4 (IntervalRat.scale (355 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-22501885004 / 1000000000000) (-22501885003 / 1000000000000), orderedInterval (-34165285972 / 1000000000000) (-34165285971 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (216908582894513 / 800000000000) 4 (IntervalRat.scale (355 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (47733373343 / 1000000000000) (47733374398 / 1000000000000), orderedInterval (-8424435865 / 1000000000000) (-8424434809 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (245951214674727 / 800000000000) 4 (IntervalRat.scale (355 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (15515082924 / 1000000000000) (15515082925 / 1000000000000), orderedInterval (42753303488 / 1000000000000) (42753303489 / 1000000000000)))) (orderedInterval (32417726668 / 1000000000000) (32417727384 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (205048481092663 / 800000000000) 4 (IntervalRat.scale (355 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-24550432408 / 1000000000000) (-24550429951 / 1000000000000), orderedInterval (43419092989 / 1000000000000) (43419095447 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (181166551541923 / 800000000000) 4 (IntervalRat.scale (355 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (45948185970 / 1000000000000) (45948185971 / 1000000000000), orderedInterval (26355365127 / 1000000000000) (26355365128 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (52509127942377 / 160000000000) 4 (IntervalRat.scale (355 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (34504893281 / 1000000000000) (34504966244 / 1000000000000), orderedInterval (-27424972595 / 1000000000000) (-27424899632 / 1000000000000)))) (orderedInterval (2056734223 / 1000000000000) (2056756401 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate304_chunkChecks4_2 :
    compactCertificate304.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (145243011292619 / 800000000000) 4 (IntervalRat.scale (355 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (7447314732 / 1000000000000) (7447314733 / 1000000000000), orderedInterval (58725201829 / 1000000000000) (58725201830 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (123124109195059 / 800000000000) 4 (IntervalRat.scale (355 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-43918717495 / 1000000000000) (-43918717494 / 1000000000000), orderedInterval (-46842322086 / 1000000000000) (-46842322085 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (77045350698577 / 800000000000) 4 (IntervalRat.scale (355 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (23916768785 / 1000000000000) (23916769278 / 1000000000000), orderedInterval (-77831308762 / 1000000000000) (-77831308269 / 1000000000000)))) (orderedInterval (70798373 / 1000000000000) (70798413 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (41435245846959 / 800000000000) 4 (IntervalRat.scale (355 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (81812302546 / 1000000000000) (81812401590 / 1000000000000), orderedInterval (-75609905288 / 1000000000000) (-75609806245 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (112504752777877 / 800000000000) 4 (IntervalRat.scale (355 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-2944720956 / 1000000000000) (-2944720953 / 1000000000000), orderedInterval (-67207383804 / 1000000000000) (-67207383801 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (153615621591029 / 800000000000) 4 (IntervalRat.scale (355 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-52951339383 / 1000000000000) (-52951339382 / 1000000000000), orderedInterval (-22479341769 / 1000000000000) (-22479341767 / 1000000000000)))) (orderedInterval (5606379070 / 1000000000000) (5606379105 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (64954649301423 / 800000000000) 4 (IntervalRat.scale (355 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (25808756692 / 1000000000000) (25808756693 / 1000000000000), orderedInterval (84545394690 / 1000000000000) (84545394691 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (264037043235983 / 800000000000) 4 (IntervalRat.scale (355 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-36080909731 / 1000000000000) (-36080909730 / 1000000000000), orderedInterval (-24986253326 / 1000000000000) (-24986253325 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (176364508332097 / 800000000000) 4 (IntervalRat.scale (355 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (52174171311 / 1000000000000) (52174171313 / 1000000000000), orderedInterval (12750031843 / 1000000000000) (12750031845 / 1000000000000)))) (orderedInterval (11918588589 / 1000000000000) (11918588844 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate304_chunkChecks4 :
    compactCertificate304.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate304.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate304_chunkChecks4_0
    compactCertificate304_chunkChecks4_1 compactCertificate304_chunkChecks4_2

theorem compactCertificate304_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate304.chunkCheck r b = true :=
  compactCertificate304.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate304_chunkChecks0
    · exact compactCertificate304_chunkChecks1
    · exact compactCertificate304_chunkChecks2
    · exact compactCertificate304_chunkChecks3
    · exact compactCertificate304_chunkChecks4)

theorem compactCertificate304_coefficient0 :
    compactCertificate304.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate304_coefficient1 :
    compactCertificate304.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate304_coefficient2 :
    compactCertificate304.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate304_coefficient3 :
    compactCertificate304.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate304_coefficient4 :
    compactCertificate304.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate304_coefficients : ∀ r : Fin 5,
    compactCertificate304.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate304_coefficient0
  · exact compactCertificate304_coefficient1
  · exact compactCertificate304_coefficient2
  · exact compactCertificate304_coefficient3
  · exact compactCertificate304_coefficient4

theorem compactCertificate304_lower : (1 : ℚ) ≤ compactCertificate304.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate304, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate304_proves {t : ℝ} (ht : t ∈ compactCertificate304.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate304.proves compactCertificate304_states compactCertificate304_chunks
    compactCertificate304_coefficients compactCertificate304_lower ht

end Erdos232
