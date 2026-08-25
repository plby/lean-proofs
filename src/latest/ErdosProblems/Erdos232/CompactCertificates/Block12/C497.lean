/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate497 : CompactCertificate where
  left := 368
  right := 369
  center := 737 / 2
  grid := fun i =>
    match i.val with
    | 0 => 117
    | 1 => 86
    | 2 => 140
    | 3 => 25
    | 4 => 68
    | 5 => 184
    | 6 => 136
    | 7 => 232
    | 8 => 171
    | 9 => 262
    | 10 => 152
    | 11 => 269
    | 12 => 251
    | 13 => 179
    | 14 => 203
    | 15 => 169
    | 16 => 150
    | 17 => 217
    | 18 => 120
    | 19 => 102
    | 20 => 64
    | 21 => 34
    | 22 => 93
    | 23 => 127
    | 24 => 54
    | 25 => 218
    | _ => 146
  point := fun i =>
    match i.val with
    | 0 => 737 / 2
    | 1 => 1085741728603037 / 4000000000000
    | 2 => 351106567058621 / 800000000000
    | 3 => 316816728527959 / 4000000000000
    | 4 => 851014296785323 / 4000000000000
    | 5 => 2310669361628991 / 4000000000000
    | 6 => 1702028593571383 / 4000000000000
    | 7 => 2916455005232659 / 4000000000000
    | 8 => 2148247556833081 / 4000000000000
    | 9 => 3295964198834263 / 4000000000000
    | 10 => 1902925817436127 / 4000000000000
    | 11 => 3376775256198443 / 4000000000000
    | 12 => 3155021468106167 / 4000000000000
    | 13 => 2251572191454311 / 4000000000000
    | 14 => 2553042890355969 / 4000000000000
    | 15 => 2128460993877361 / 4000000000000
    | 16 => 1880559837836581 / 4000000000000
    | 17 => 545059539345519 / 800000000000
    | 18 => 1507663370741693 / 4000000000000
    | 19 => 1278062936292373 / 4000000000000
    | 20 => 799752443166919 / 4000000000000
    | 21 => 430109523791673 / 4000000000000
    | 22 => 1167831025314019 / 4000000000000
    | 23 => 1594573424120963 / 4000000000000
    | 24 => 674247556833081 / 4000000000000
    | 25 => 2740778885421401 / 4000000000000
    | _ => 1830713276630359 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-41110456797 / 1000000000000) (-41110455394 / 1000000000000), orderedInterval (6181678340 / 1000000000000) (6181679743 / 1000000000000))
    | 1 => (orderedInterval (43120552233 / 1000000000000) (43120576666 / 1000000000000), orderedInterval (-22124771333 / 1000000000000) (-22124746900 / 1000000000000))
    | 2 => (orderedInterval (-5866525568 / 1000000000000) (-5866525563 / 1000000000000), orderedInterval (37638181049 / 1000000000000) (37638181054 / 1000000000000))
    | 3 => (orderedInterval (-88979307778 / 1000000000000) (-88979307774 / 1000000000000), orderedInterval (-10403325352 / 1000000000000) (-10403325347 / 1000000000000))
    | 4 => (orderedInterval (-4911914258 / 1000000000000) (-4911914247 / 1000000000000), orderedInterval (54492442210 / 1000000000000) (54492442222 / 1000000000000))
    | 5 => (orderedInterval (12911499775 / 1000000000000) (12911499776 / 1000000000000), orderedInterval (30572251723 / 1000000000000) (30572251724 / 1000000000000))
    | 6 => (orderedInterval (-31782528336 / 1000000000000) (-31782445493 / 1000000000000), orderedInterval (22083088942 / 1000000000000) (22083171785 / 1000000000000))
    | 7 => (orderedInterval (25623850385 / 1000000000000) (25623850387 / 1000000000000), orderedInterval (14698409082 / 1000000000000) (14698409084 / 1000000000000))
    | 8 => (orderedInterval (-20414652873 / 1000000000000) (-20414652872 / 1000000000000), orderedInterval (-27704939876 / 1000000000000) (-27704939875 / 1000000000000))
    | 9 => (orderedInterval (27633147506 / 1000000000000) (27633158366 / 1000000000000), orderedInterval (-3019091608 / 1000000000000) (-3019080748 / 1000000000000))
    | 10 => (orderedInterval (-30890254514 / 1000000000000) (-30890159941 / 1000000000000), orderedInterval (19627982571 / 1000000000000) (19628077144 / 1000000000000))
    | 11 => (orderedInterval (2997161444 / 1000000000000) (2997161445 / 1000000000000), orderedInterval (-27298896054 / 1000000000000) (-27298896053 / 1000000000000))
    | 12 => (orderedInterval (-23919108616 / 1000000000000) (-23919108614 / 1000000000000), orderedInterval (-15314403411 / 1000000000000) (-15314403410 / 1000000000000))
    | 13 => (orderedInterval (-32684745886 / 1000000000000) (-32684745855 / 1000000000000), orderedInterval (-7888365897 / 1000000000000) (-7888365866 / 1000000000000))
    | 14 => (orderedInterval (-30453184319 / 1000000000000) (-30453184284 / 1000000000000), orderedInterval (-8344675847 / 1000000000000) (-8344675812 / 1000000000000))
    | 15 => (orderedInterval (-31852375632 / 1000000000000) (-31852333468 / 1000000000000), orderedInterval (13514033668 / 1000000000000) (13514075832 / 1000000000000))
    | 16 => (orderedInterval (-11358909721 / 1000000000000) (-11358909675 / 1000000000000), orderedInterval (35013261865 / 1000000000000) (35013261911 / 1000000000000))
    | 17 => (orderedInterval (-11452586785 / 1000000000000) (-11452586784 / 1000000000000), orderedInterval (-28332803829 / 1000000000000) (-28332803828 / 1000000000000))
    | 18 => (orderedInterval (26782357109 / 1000000000000) (26782357110 / 1000000000000), orderedInterval (31137043386 / 1000000000000) (31137043387 / 1000000000000))
    | 19 => (orderedInterval (-6304324364 / 1000000000000) (-6304324353 / 1000000000000), orderedInterval (44199342262 / 1000000000000) (44199342272 / 1000000000000))
    | 20 => (orderedInterval (-18767121265 / 1000000000000) (-18767120838 / 1000000000000), orderedInterval (53262409679 / 1000000000000) (53262410105 / 1000000000000))
    | 21 => (orderedInterval (76737822697 / 1000000000000) (76737822708 / 1000000000000), orderedInterval (5280522765 / 1000000000000) (5280522776 / 1000000000000))
    | 22 => (orderedInterval (-25379610721 / 1000000000000) (-25379610720 / 1000000000000), orderedInterval (-39153433746 / 1000000000000) (-39153433745 / 1000000000000))
    | 23 => (orderedInterval (-17244295051 / 1000000000000) (-17244295050 / 1000000000000), orderedInterval (-36028347623 / 1000000000000) (-36028347622 / 1000000000000))
    | 24 => (orderedInterval (-18129431426 / 1000000000000) (-18129431112 / 1000000000000), orderedInterval (58774378503 / 1000000000000) (58774378817 / 1000000000000))
    | 25 => (orderedInterval (27339046019 / 1000000000000) (27339046022 / 1000000000000), orderedInterval (13459079436 / 1000000000000) (13459079439 / 1000000000000))
    | _ => (orderedInterval (-7741231655 / 1000000000000) (-7741231645 / 1000000000000), orderedInterval (36492022668 / 1000000000000) (36492022679 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-16237200449 / 1000000000000) (-16237199639 / 1000000000000)
      | 1 => orderedInterval (-131854069 / 1000000000000) (-131854024 / 1000000000000)
      | 2 => orderedInterval (-1283723959 / 1000000000000) (-1283723938 / 1000000000000)
      | 3 => orderedInterval (-6772728177 / 1000000000000) (-6772719094 / 1000000000000)
      | 4 => orderedInterval (-2504838889 / 1000000000000) (-2504838842 / 1000000000000)
      | 5 => orderedInterval (-11019545 / 1000000000000) (-11019019 / 1000000000000)
      | 6 => orderedInterval (-4536440765 / 1000000000000) (-4536440657 / 1000000000000)
      | 7 => orderedInterval (480394116 / 1000000000000) (480394160 / 1000000000000)
      | _ => orderedInterval (-882276730 / 1000000000000) (-882276623 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (4928846432 / 1000000000000) (4928847185 / 1000000000000)
      | 1 => orderedInterval (-2234051290 / 1000000000000) (-2234051238 / 1000000000000)
      | 2 => orderedInterval (-1872868134 / 1000000000000) (-1872868098 / 1000000000000)
      | 3 => orderedInterval (-5813258324 / 1000000000000) (-5813244660 / 1000000000000)
      | 4 => orderedInterval (-474534909 / 1000000000000) (-474534832 / 1000000000000)
      | 5 => orderedInterval (-3672267969 / 1000000000000) (-3672267211 / 1000000000000)
      | 6 => orderedInterval (-6320608320 / 1000000000000) (-6320608226 / 1000000000000)
      | 7 => orderedInterval (3662347869 / 1000000000000) (3662347909 / 1000000000000)
      | _ => orderedInterval (-10378930297 / 1000000000000) (-10378930149 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (16551681750 / 1000000000000) (16551682465 / 1000000000000)
      | 1 => orderedInterval (2276853924 / 1000000000000) (2276853994 / 1000000000000)
      | 2 => orderedInterval (4147145734 / 1000000000000) (4147145798 / 1000000000000)
      | 3 => orderedInterval (26144604930 / 1000000000000) (26144626943 / 1000000000000)
      | 4 => orderedInterval (4772373028 / 1000000000000) (4772373154 / 1000000000000)
      | 5 => orderedInterval (721259546 / 1000000000000) (721260644 / 1000000000000)
      | 6 => orderedInterval (4408876498 / 1000000000000) (4408876584 / 1000000000000)
      | 7 => orderedInterval (-1797357258 / 1000000000000) (-1797357218 / 1000000000000)
      | _ => orderedInterval (5504827543 / 1000000000000) (5504827759 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-6144000631 / 1000000000000) (-6143999943 / 1000000000000)
      | 1 => orderedInterval (7982274104 / 1000000000000) (7982274209 / 1000000000000)
      | 2 => orderedInterval (5573215289 / 1000000000000) (5573215407 / 1000000000000)
      | 3 => orderedInterval (37459904778 / 1000000000000) (37459942910 / 1000000000000)
      | 4 => orderedInterval (-284888510 / 1000000000000) (-284888298 / 1000000000000)
      | 5 => orderedInterval (8274229876 / 1000000000000) (8274231467 / 1000000000000)
      | 6 => orderedInterval (6669343693 / 1000000000000) (6669343775 / 1000000000000)
      | 7 => orderedInterval (-3930141760 / 1000000000000) (-3930141719 / 1000000000000)
      | _ => orderedInterval (20112206724 / 1000000000000) (20112207056 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-16835662601 / 1000000000000) (-16835661928 / 1000000000000)
      | 1 => orderedInterval (-5604165617 / 1000000000000) (-5604165455 / 1000000000000)
      | 2 => orderedInterval (-14369093906 / 1000000000000) (-14369093689 / 1000000000000)
      | 3 => orderedInterval (-117577335805 / 1000000000000) (-117577264740 / 1000000000000)
      | 4 => orderedInterval (-6374997578 / 1000000000000) (-6374997212 / 1000000000000)
      | 5 => orderedInterval (-3348587300 / 1000000000000) (-3348584982 / 1000000000000)
      | 6 => orderedInterval (-4574529101 / 1000000000000) (-4574529021 / 1000000000000)
      | 7 => orderedInterval (2047938015 / 1000000000000) (2047938058 / 1000000000000)
      | _ => orderedInterval (-23260279169 / 1000000000000) (-23260278637 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-31879688467 / 1000000000000) (-31879677676 / 1000000000000)
    | 1 => orderedInterval (-22175324942 / 1000000000000) (-22175309320 / 1000000000000)
    | 2 => orderedInterval (62730265695 / 1000000000000) (62730290123 / 1000000000000)
    | 3 => orderedInterval (75712143563 / 1000000000000) (75712184864 / 1000000000000)
    | _ => orderedInterval (-189896713062 / 1000000000000) (-189896637606 / 1000000000000)

theorem compactCertificate497_stateChecks0 :
    compactCertificate497.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 117 12 (737 / 2)) (orderedInterval (-41110456797 / 1000000000000) (-41110455394 / 1000000000000), orderedInterval (6181678340 / 1000000000000) (6181679743 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 86 12 (1085741728603037 / 4000000000000)) (orderedInterval (43120552233 / 1000000000000) (43120576666 / 1000000000000), orderedInterval (-22124771333 / 1000000000000) (-22124746900 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 140 12 (351106567058621 / 800000000000)) (orderedInterval (-5866525568 / 1000000000000) (-5866525563 / 1000000000000), orderedInterval (37638181049 / 1000000000000) (37638181054 / 1000000000000))) = true
  rfl'

theorem compactCertificate497_stateChecks1 :
    compactCertificate497.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 25 12 (316816728527959 / 4000000000000)) (orderedInterval (-88979307778 / 1000000000000) (-88979307774 / 1000000000000), orderedInterval (-10403325352 / 1000000000000) (-10403325347 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (851014296785323 / 4000000000000)) (orderedInterval (-4911914258 / 1000000000000) (-4911914247 / 1000000000000), orderedInterval (54492442210 / 1000000000000) (54492442222 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 184 12 (2310669361628991 / 4000000000000)) (orderedInterval (12911499775 / 1000000000000) (12911499776 / 1000000000000), orderedInterval (30572251723 / 1000000000000) (30572251724 / 1000000000000))) = true
  rfl'

theorem compactCertificate497_stateChecks2 :
    compactCertificate497.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 136 12 (1702028593571383 / 4000000000000)) (orderedInterval (-31782528336 / 1000000000000) (-31782445493 / 1000000000000), orderedInterval (22083088942 / 1000000000000) (22083171785 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 232 12 (2916455005232659 / 4000000000000)) (orderedInterval (25623850385 / 1000000000000) (25623850387 / 1000000000000), orderedInterval (14698409082 / 1000000000000) (14698409084 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 171 12 (2148247556833081 / 4000000000000)) (orderedInterval (-20414652873 / 1000000000000) (-20414652872 / 1000000000000), orderedInterval (-27704939876 / 1000000000000) (-27704939875 / 1000000000000))) = true
  rfl'

theorem compactCertificate497_stateChecks3 :
    compactCertificate497.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 262 12 (3295964198834263 / 4000000000000)) (orderedInterval (27633147506 / 1000000000000) (27633158366 / 1000000000000), orderedInterval (-3019091608 / 1000000000000) (-3019080748 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 152 12 (1902925817436127 / 4000000000000)) (orderedInterval (-30890254514 / 1000000000000) (-30890159941 / 1000000000000), orderedInterval (19627982571 / 1000000000000) (19628077144 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 269 12 (3376775256198443 / 4000000000000)) (orderedInterval (2997161444 / 1000000000000) (2997161445 / 1000000000000), orderedInterval (-27298896054 / 1000000000000) (-27298896053 / 1000000000000))) = true
  rfl'

theorem compactCertificate497_stateChecks4 :
    compactCertificate497.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 251 12 (3155021468106167 / 4000000000000)) (orderedInterval (-23919108616 / 1000000000000) (-23919108614 / 1000000000000), orderedInterval (-15314403411 / 1000000000000) (-15314403410 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 179 12 (2251572191454311 / 4000000000000)) (orderedInterval (-32684745886 / 1000000000000) (-32684745855 / 1000000000000), orderedInterval (-7888365897 / 1000000000000) (-7888365866 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 203 12 (2553042890355969 / 4000000000000)) (orderedInterval (-30453184319 / 1000000000000) (-30453184284 / 1000000000000), orderedInterval (-8344675847 / 1000000000000) (-8344675812 / 1000000000000))) = true
  rfl'

theorem compactCertificate497_stateChecks5 :
    compactCertificate497.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 169 12 (2128460993877361 / 4000000000000)) (orderedInterval (-31852375632 / 1000000000000) (-31852333468 / 1000000000000), orderedInterval (13514033668 / 1000000000000) (13514075832 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 150 12 (1880559837836581 / 4000000000000)) (orderedInterval (-11358909721 / 1000000000000) (-11358909675 / 1000000000000), orderedInterval (35013261865 / 1000000000000) (35013261911 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 217 12 (545059539345519 / 800000000000)) (orderedInterval (-11452586785 / 1000000000000) (-11452586784 / 1000000000000), orderedInterval (-28332803829 / 1000000000000) (-28332803828 / 1000000000000))) = true
  rfl'

theorem compactCertificate497_stateChecks6 :
    compactCertificate497.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 120 12 (1507663370741693 / 4000000000000)) (orderedInterval (26782357109 / 1000000000000) (26782357110 / 1000000000000), orderedInterval (31137043386 / 1000000000000) (31137043387 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 102 12 (1278062936292373 / 4000000000000)) (orderedInterval (-6304324364 / 1000000000000) (-6304324353 / 1000000000000), orderedInterval (44199342262 / 1000000000000) (44199342272 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (799752443166919 / 4000000000000)) (orderedInterval (-18767121265 / 1000000000000) (-18767120838 / 1000000000000), orderedInterval (53262409679 / 1000000000000) (53262410105 / 1000000000000))) = true
  rfl'

theorem compactCertificate497_stateChecks7 :
    compactCertificate497.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (430109523791673 / 4000000000000)) (orderedInterval (76737822697 / 1000000000000) (76737822708 / 1000000000000), orderedInterval (5280522765 / 1000000000000) (5280522776 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 93 12 (1167831025314019 / 4000000000000)) (orderedInterval (-25379610721 / 1000000000000) (-25379610720 / 1000000000000), orderedInterval (-39153433746 / 1000000000000) (-39153433745 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 127 12 (1594573424120963 / 4000000000000)) (orderedInterval (-17244295051 / 1000000000000) (-17244295050 / 1000000000000), orderedInterval (-36028347623 / 1000000000000) (-36028347622 / 1000000000000))) = true
  rfl'

theorem compactCertificate497_stateChecks8 :
    compactCertificate497.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (674247556833081 / 4000000000000)) (orderedInterval (-18129431426 / 1000000000000) (-18129431112 / 1000000000000), orderedInterval (58774378503 / 1000000000000) (58774378817 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 218 12 (2740778885421401 / 4000000000000)) (orderedInterval (27339046019 / 1000000000000) (27339046022 / 1000000000000), orderedInterval (13459079436 / 1000000000000) (13459079439 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 146 12 (1830713276630359 / 4000000000000)) (orderedInterval (-7741231655 / 1000000000000) (-7741231645 / 1000000000000), orderedInterval (36492022668 / 1000000000000) (36492022679 / 1000000000000))) = true
  rfl'

theorem compactCertificate497_states : ∀ j,
    BesselStateValid (compactCertificate497.point j) (compactCertificate497.state j) :=
  compactCertificate497.statesValid_of_checks3 compactCertificate497_stateChecks0
    compactCertificate497_stateChecks1 compactCertificate497_stateChecks2
    compactCertificate497_stateChecks3 compactCertificate497_stateChecks4
    compactCertificate497_stateChecks5 compactCertificate497_stateChecks6
    compactCertificate497_stateChecks7 compactCertificate497_stateChecks8

theorem compactCertificate497_chunkChecks0_0 :
    compactCertificate497.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (737 / 2) 0 (IntervalRat.scale (737 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-41110456797 / 1000000000000) (-41110455394 / 1000000000000), orderedInterval (6181678340 / 1000000000000) (6181679743 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1085741728603037 / 4000000000000) 0 (IntervalRat.scale (737 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (43120552233 / 1000000000000) (43120576666 / 1000000000000), orderedInterval (-22124771333 / 1000000000000) (-22124746900 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (351106567058621 / 800000000000) 0 (IntervalRat.scale (737 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-5866525568 / 1000000000000) (-5866525563 / 1000000000000), orderedInterval (37638181049 / 1000000000000) (37638181054 / 1000000000000)))) (orderedInterval (-16237200449 / 1000000000000) (-16237199639 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (316816728527959 / 4000000000000) 0 (IntervalRat.scale (737 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-88979307778 / 1000000000000) (-88979307774 / 1000000000000), orderedInterval (-10403325352 / 1000000000000) (-10403325347 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (851014296785323 / 4000000000000) 0 (IntervalRat.scale (737 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-4911914258 / 1000000000000) (-4911914247 / 1000000000000), orderedInterval (54492442210 / 1000000000000) (54492442222 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2310669361628991 / 4000000000000) 0 (IntervalRat.scale (737 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (12911499775 / 1000000000000) (12911499776 / 1000000000000), orderedInterval (30572251723 / 1000000000000) (30572251724 / 1000000000000)))) (orderedInterval (-131854069 / 1000000000000) (-131854024 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1702028593571383 / 4000000000000) 0 (IntervalRat.scale (737 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-31782528336 / 1000000000000) (-31782445493 / 1000000000000), orderedInterval (22083088942 / 1000000000000) (22083171785 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2916455005232659 / 4000000000000) 0 (IntervalRat.scale (737 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (25623850385 / 1000000000000) (25623850387 / 1000000000000), orderedInterval (14698409082 / 1000000000000) (14698409084 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2148247556833081 / 4000000000000) 0 (IntervalRat.scale (737 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-20414652873 / 1000000000000) (-20414652872 / 1000000000000), orderedInterval (-27704939876 / 1000000000000) (-27704939875 / 1000000000000)))) (orderedInterval (-1283723959 / 1000000000000) (-1283723938 / 1000000000000))) = true
  rfl'

theorem compactCertificate497_chunkChecks0_1 :
    compactCertificate497.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3295964198834263 / 4000000000000) 0 (IntervalRat.scale (737 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (27633147506 / 1000000000000) (27633158366 / 1000000000000), orderedInterval (-3019091608 / 1000000000000) (-3019080748 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1902925817436127 / 4000000000000) 0 (IntervalRat.scale (737 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-30890254514 / 1000000000000) (-30890159941 / 1000000000000), orderedInterval (19627982571 / 1000000000000) (19628077144 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3376775256198443 / 4000000000000) 0 (IntervalRat.scale (737 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (2997161444 / 1000000000000) (2997161445 / 1000000000000), orderedInterval (-27298896054 / 1000000000000) (-27298896053 / 1000000000000)))) (orderedInterval (-6772728177 / 1000000000000) (-6772719094 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3155021468106167 / 4000000000000) 0 (IntervalRat.scale (737 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-23919108616 / 1000000000000) (-23919108614 / 1000000000000), orderedInterval (-15314403411 / 1000000000000) (-15314403410 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2251572191454311 / 4000000000000) 0 (IntervalRat.scale (737 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-32684745886 / 1000000000000) (-32684745855 / 1000000000000), orderedInterval (-7888365897 / 1000000000000) (-7888365866 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2553042890355969 / 4000000000000) 0 (IntervalRat.scale (737 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-30453184319 / 1000000000000) (-30453184284 / 1000000000000), orderedInterval (-8344675847 / 1000000000000) (-8344675812 / 1000000000000)))) (orderedInterval (-2504838889 / 1000000000000) (-2504838842 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2128460993877361 / 4000000000000) 0 (IntervalRat.scale (737 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-31852375632 / 1000000000000) (-31852333468 / 1000000000000), orderedInterval (13514033668 / 1000000000000) (13514075832 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1880559837836581 / 4000000000000) 0 (IntervalRat.scale (737 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-11358909721 / 1000000000000) (-11358909675 / 1000000000000), orderedInterval (35013261865 / 1000000000000) (35013261911 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (545059539345519 / 800000000000) 0 (IntervalRat.scale (737 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-11452586785 / 1000000000000) (-11452586784 / 1000000000000), orderedInterval (-28332803829 / 1000000000000) (-28332803828 / 1000000000000)))) (orderedInterval (-11019545 / 1000000000000) (-11019019 / 1000000000000))) = true
  rfl'

theorem compactCertificate497_chunkChecks0_2 :
    compactCertificate497.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1507663370741693 / 4000000000000) 0 (IntervalRat.scale (737 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (26782357109 / 1000000000000) (26782357110 / 1000000000000), orderedInterval (31137043386 / 1000000000000) (31137043387 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1278062936292373 / 4000000000000) 0 (IntervalRat.scale (737 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-6304324364 / 1000000000000) (-6304324353 / 1000000000000), orderedInterval (44199342262 / 1000000000000) (44199342272 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (799752443166919 / 4000000000000) 0 (IntervalRat.scale (737 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-18767121265 / 1000000000000) (-18767120838 / 1000000000000), orderedInterval (53262409679 / 1000000000000) (53262410105 / 1000000000000)))) (orderedInterval (-4536440765 / 1000000000000) (-4536440657 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (430109523791673 / 4000000000000) 0 (IntervalRat.scale (737 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (76737822697 / 1000000000000) (76737822708 / 1000000000000), orderedInterval (5280522765 / 1000000000000) (5280522776 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1167831025314019 / 4000000000000) 0 (IntervalRat.scale (737 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-25379610721 / 1000000000000) (-25379610720 / 1000000000000), orderedInterval (-39153433746 / 1000000000000) (-39153433745 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1594573424120963 / 4000000000000) 0 (IntervalRat.scale (737 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-17244295051 / 1000000000000) (-17244295050 / 1000000000000), orderedInterval (-36028347623 / 1000000000000) (-36028347622 / 1000000000000)))) (orderedInterval (480394116 / 1000000000000) (480394160 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (674247556833081 / 4000000000000) 0 (IntervalRat.scale (737 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-18129431426 / 1000000000000) (-18129431112 / 1000000000000), orderedInterval (58774378503 / 1000000000000) (58774378817 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2740778885421401 / 4000000000000) 0 (IntervalRat.scale (737 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27339046019 / 1000000000000) (27339046022 / 1000000000000), orderedInterval (13459079436 / 1000000000000) (13459079439 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1830713276630359 / 4000000000000) 0 (IntervalRat.scale (737 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-7741231655 / 1000000000000) (-7741231645 / 1000000000000), orderedInterval (36492022668 / 1000000000000) (36492022679 / 1000000000000)))) (orderedInterval (-882276730 / 1000000000000) (-882276623 / 1000000000000))) = true
  rfl'

theorem compactCertificate497_chunkChecks0 :
    compactCertificate497.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate497.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate497_chunkChecks0_0
    compactCertificate497_chunkChecks0_1 compactCertificate497_chunkChecks0_2

theorem compactCertificate497_chunkChecks1_0 :
    compactCertificate497.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (737 / 2) 1 (IntervalRat.scale (737 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-41110456797 / 1000000000000) (-41110455394 / 1000000000000), orderedInterval (6181678340 / 1000000000000) (6181679743 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1085741728603037 / 4000000000000) 1 (IntervalRat.scale (737 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (43120552233 / 1000000000000) (43120576666 / 1000000000000), orderedInterval (-22124771333 / 1000000000000) (-22124746900 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (351106567058621 / 800000000000) 1 (IntervalRat.scale (737 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-5866525568 / 1000000000000) (-5866525563 / 1000000000000), orderedInterval (37638181049 / 1000000000000) (37638181054 / 1000000000000)))) (orderedInterval (4928846432 / 1000000000000) (4928847185 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (316816728527959 / 4000000000000) 1 (IntervalRat.scale (737 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-88979307778 / 1000000000000) (-88979307774 / 1000000000000), orderedInterval (-10403325352 / 1000000000000) (-10403325347 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (851014296785323 / 4000000000000) 1 (IntervalRat.scale (737 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-4911914258 / 1000000000000) (-4911914247 / 1000000000000), orderedInterval (54492442210 / 1000000000000) (54492442222 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2310669361628991 / 4000000000000) 1 (IntervalRat.scale (737 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (12911499775 / 1000000000000) (12911499776 / 1000000000000), orderedInterval (30572251723 / 1000000000000) (30572251724 / 1000000000000)))) (orderedInterval (-2234051290 / 1000000000000) (-2234051238 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1702028593571383 / 4000000000000) 1 (IntervalRat.scale (737 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-31782528336 / 1000000000000) (-31782445493 / 1000000000000), orderedInterval (22083088942 / 1000000000000) (22083171785 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2916455005232659 / 4000000000000) 1 (IntervalRat.scale (737 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (25623850385 / 1000000000000) (25623850387 / 1000000000000), orderedInterval (14698409082 / 1000000000000) (14698409084 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2148247556833081 / 4000000000000) 1 (IntervalRat.scale (737 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-20414652873 / 1000000000000) (-20414652872 / 1000000000000), orderedInterval (-27704939876 / 1000000000000) (-27704939875 / 1000000000000)))) (orderedInterval (-1872868134 / 1000000000000) (-1872868098 / 1000000000000))) = true
  rfl'

theorem compactCertificate497_chunkChecks1_1 :
    compactCertificate497.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3295964198834263 / 4000000000000) 1 (IntervalRat.scale (737 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (27633147506 / 1000000000000) (27633158366 / 1000000000000), orderedInterval (-3019091608 / 1000000000000) (-3019080748 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1902925817436127 / 4000000000000) 1 (IntervalRat.scale (737 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-30890254514 / 1000000000000) (-30890159941 / 1000000000000), orderedInterval (19627982571 / 1000000000000) (19628077144 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3376775256198443 / 4000000000000) 1 (IntervalRat.scale (737 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (2997161444 / 1000000000000) (2997161445 / 1000000000000), orderedInterval (-27298896054 / 1000000000000) (-27298896053 / 1000000000000)))) (orderedInterval (-5813258324 / 1000000000000) (-5813244660 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3155021468106167 / 4000000000000) 1 (IntervalRat.scale (737 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-23919108616 / 1000000000000) (-23919108614 / 1000000000000), orderedInterval (-15314403411 / 1000000000000) (-15314403410 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2251572191454311 / 4000000000000) 1 (IntervalRat.scale (737 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-32684745886 / 1000000000000) (-32684745855 / 1000000000000), orderedInterval (-7888365897 / 1000000000000) (-7888365866 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2553042890355969 / 4000000000000) 1 (IntervalRat.scale (737 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-30453184319 / 1000000000000) (-30453184284 / 1000000000000), orderedInterval (-8344675847 / 1000000000000) (-8344675812 / 1000000000000)))) (orderedInterval (-474534909 / 1000000000000) (-474534832 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2128460993877361 / 4000000000000) 1 (IntervalRat.scale (737 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-31852375632 / 1000000000000) (-31852333468 / 1000000000000), orderedInterval (13514033668 / 1000000000000) (13514075832 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1880559837836581 / 4000000000000) 1 (IntervalRat.scale (737 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-11358909721 / 1000000000000) (-11358909675 / 1000000000000), orderedInterval (35013261865 / 1000000000000) (35013261911 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (545059539345519 / 800000000000) 1 (IntervalRat.scale (737 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-11452586785 / 1000000000000) (-11452586784 / 1000000000000), orderedInterval (-28332803829 / 1000000000000) (-28332803828 / 1000000000000)))) (orderedInterval (-3672267969 / 1000000000000) (-3672267211 / 1000000000000))) = true
  rfl'

theorem compactCertificate497_chunkChecks1_2 :
    compactCertificate497.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1507663370741693 / 4000000000000) 1 (IntervalRat.scale (737 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (26782357109 / 1000000000000) (26782357110 / 1000000000000), orderedInterval (31137043386 / 1000000000000) (31137043387 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1278062936292373 / 4000000000000) 1 (IntervalRat.scale (737 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-6304324364 / 1000000000000) (-6304324353 / 1000000000000), orderedInterval (44199342262 / 1000000000000) (44199342272 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (799752443166919 / 4000000000000) 1 (IntervalRat.scale (737 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-18767121265 / 1000000000000) (-18767120838 / 1000000000000), orderedInterval (53262409679 / 1000000000000) (53262410105 / 1000000000000)))) (orderedInterval (-6320608320 / 1000000000000) (-6320608226 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (430109523791673 / 4000000000000) 1 (IntervalRat.scale (737 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (76737822697 / 1000000000000) (76737822708 / 1000000000000), orderedInterval (5280522765 / 1000000000000) (5280522776 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1167831025314019 / 4000000000000) 1 (IntervalRat.scale (737 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-25379610721 / 1000000000000) (-25379610720 / 1000000000000), orderedInterval (-39153433746 / 1000000000000) (-39153433745 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1594573424120963 / 4000000000000) 1 (IntervalRat.scale (737 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-17244295051 / 1000000000000) (-17244295050 / 1000000000000), orderedInterval (-36028347623 / 1000000000000) (-36028347622 / 1000000000000)))) (orderedInterval (3662347869 / 1000000000000) (3662347909 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (674247556833081 / 4000000000000) 1 (IntervalRat.scale (737 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-18129431426 / 1000000000000) (-18129431112 / 1000000000000), orderedInterval (58774378503 / 1000000000000) (58774378817 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2740778885421401 / 4000000000000) 1 (IntervalRat.scale (737 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27339046019 / 1000000000000) (27339046022 / 1000000000000), orderedInterval (13459079436 / 1000000000000) (13459079439 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1830713276630359 / 4000000000000) 1 (IntervalRat.scale (737 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-7741231655 / 1000000000000) (-7741231645 / 1000000000000), orderedInterval (36492022668 / 1000000000000) (36492022679 / 1000000000000)))) (orderedInterval (-10378930297 / 1000000000000) (-10378930149 / 1000000000000))) = true
  rfl'

theorem compactCertificate497_chunkChecks1 :
    compactCertificate497.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate497.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate497_chunkChecks1_0
    compactCertificate497_chunkChecks1_1 compactCertificate497_chunkChecks1_2

theorem compactCertificate497_chunkChecks2_0 :
    compactCertificate497.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (737 / 2) 2 (IntervalRat.scale (737 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-41110456797 / 1000000000000) (-41110455394 / 1000000000000), orderedInterval (6181678340 / 1000000000000) (6181679743 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1085741728603037 / 4000000000000) 2 (IntervalRat.scale (737 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (43120552233 / 1000000000000) (43120576666 / 1000000000000), orderedInterval (-22124771333 / 1000000000000) (-22124746900 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (351106567058621 / 800000000000) 2 (IntervalRat.scale (737 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-5866525568 / 1000000000000) (-5866525563 / 1000000000000), orderedInterval (37638181049 / 1000000000000) (37638181054 / 1000000000000)))) (orderedInterval (16551681750 / 1000000000000) (16551682465 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (316816728527959 / 4000000000000) 2 (IntervalRat.scale (737 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-88979307778 / 1000000000000) (-88979307774 / 1000000000000), orderedInterval (-10403325352 / 1000000000000) (-10403325347 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (851014296785323 / 4000000000000) 2 (IntervalRat.scale (737 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-4911914258 / 1000000000000) (-4911914247 / 1000000000000), orderedInterval (54492442210 / 1000000000000) (54492442222 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2310669361628991 / 4000000000000) 2 (IntervalRat.scale (737 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (12911499775 / 1000000000000) (12911499776 / 1000000000000), orderedInterval (30572251723 / 1000000000000) (30572251724 / 1000000000000)))) (orderedInterval (2276853924 / 1000000000000) (2276853994 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1702028593571383 / 4000000000000) 2 (IntervalRat.scale (737 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-31782528336 / 1000000000000) (-31782445493 / 1000000000000), orderedInterval (22083088942 / 1000000000000) (22083171785 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2916455005232659 / 4000000000000) 2 (IntervalRat.scale (737 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (25623850385 / 1000000000000) (25623850387 / 1000000000000), orderedInterval (14698409082 / 1000000000000) (14698409084 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2148247556833081 / 4000000000000) 2 (IntervalRat.scale (737 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-20414652873 / 1000000000000) (-20414652872 / 1000000000000), orderedInterval (-27704939876 / 1000000000000) (-27704939875 / 1000000000000)))) (orderedInterval (4147145734 / 1000000000000) (4147145798 / 1000000000000))) = true
  rfl'

theorem compactCertificate497_chunkChecks2_1 :
    compactCertificate497.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3295964198834263 / 4000000000000) 2 (IntervalRat.scale (737 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (27633147506 / 1000000000000) (27633158366 / 1000000000000), orderedInterval (-3019091608 / 1000000000000) (-3019080748 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1902925817436127 / 4000000000000) 2 (IntervalRat.scale (737 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-30890254514 / 1000000000000) (-30890159941 / 1000000000000), orderedInterval (19627982571 / 1000000000000) (19628077144 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3376775256198443 / 4000000000000) 2 (IntervalRat.scale (737 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (2997161444 / 1000000000000) (2997161445 / 1000000000000), orderedInterval (-27298896054 / 1000000000000) (-27298896053 / 1000000000000)))) (orderedInterval (26144604930 / 1000000000000) (26144626943 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3155021468106167 / 4000000000000) 2 (IntervalRat.scale (737 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-23919108616 / 1000000000000) (-23919108614 / 1000000000000), orderedInterval (-15314403411 / 1000000000000) (-15314403410 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2251572191454311 / 4000000000000) 2 (IntervalRat.scale (737 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-32684745886 / 1000000000000) (-32684745855 / 1000000000000), orderedInterval (-7888365897 / 1000000000000) (-7888365866 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2553042890355969 / 4000000000000) 2 (IntervalRat.scale (737 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-30453184319 / 1000000000000) (-30453184284 / 1000000000000), orderedInterval (-8344675847 / 1000000000000) (-8344675812 / 1000000000000)))) (orderedInterval (4772373028 / 1000000000000) (4772373154 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2128460993877361 / 4000000000000) 2 (IntervalRat.scale (737 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-31852375632 / 1000000000000) (-31852333468 / 1000000000000), orderedInterval (13514033668 / 1000000000000) (13514075832 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1880559837836581 / 4000000000000) 2 (IntervalRat.scale (737 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-11358909721 / 1000000000000) (-11358909675 / 1000000000000), orderedInterval (35013261865 / 1000000000000) (35013261911 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (545059539345519 / 800000000000) 2 (IntervalRat.scale (737 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-11452586785 / 1000000000000) (-11452586784 / 1000000000000), orderedInterval (-28332803829 / 1000000000000) (-28332803828 / 1000000000000)))) (orderedInterval (721259546 / 1000000000000) (721260644 / 1000000000000))) = true
  rfl'

theorem compactCertificate497_chunkChecks2_2 :
    compactCertificate497.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1507663370741693 / 4000000000000) 2 (IntervalRat.scale (737 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (26782357109 / 1000000000000) (26782357110 / 1000000000000), orderedInterval (31137043386 / 1000000000000) (31137043387 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1278062936292373 / 4000000000000) 2 (IntervalRat.scale (737 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-6304324364 / 1000000000000) (-6304324353 / 1000000000000), orderedInterval (44199342262 / 1000000000000) (44199342272 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (799752443166919 / 4000000000000) 2 (IntervalRat.scale (737 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-18767121265 / 1000000000000) (-18767120838 / 1000000000000), orderedInterval (53262409679 / 1000000000000) (53262410105 / 1000000000000)))) (orderedInterval (4408876498 / 1000000000000) (4408876584 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (430109523791673 / 4000000000000) 2 (IntervalRat.scale (737 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (76737822697 / 1000000000000) (76737822708 / 1000000000000), orderedInterval (5280522765 / 1000000000000) (5280522776 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1167831025314019 / 4000000000000) 2 (IntervalRat.scale (737 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-25379610721 / 1000000000000) (-25379610720 / 1000000000000), orderedInterval (-39153433746 / 1000000000000) (-39153433745 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1594573424120963 / 4000000000000) 2 (IntervalRat.scale (737 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-17244295051 / 1000000000000) (-17244295050 / 1000000000000), orderedInterval (-36028347623 / 1000000000000) (-36028347622 / 1000000000000)))) (orderedInterval (-1797357258 / 1000000000000) (-1797357218 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (674247556833081 / 4000000000000) 2 (IntervalRat.scale (737 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-18129431426 / 1000000000000) (-18129431112 / 1000000000000), orderedInterval (58774378503 / 1000000000000) (58774378817 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2740778885421401 / 4000000000000) 2 (IntervalRat.scale (737 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27339046019 / 1000000000000) (27339046022 / 1000000000000), orderedInterval (13459079436 / 1000000000000) (13459079439 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1830713276630359 / 4000000000000) 2 (IntervalRat.scale (737 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-7741231655 / 1000000000000) (-7741231645 / 1000000000000), orderedInterval (36492022668 / 1000000000000) (36492022679 / 1000000000000)))) (orderedInterval (5504827543 / 1000000000000) (5504827759 / 1000000000000))) = true
  rfl'

theorem compactCertificate497_chunkChecks2 :
    compactCertificate497.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate497.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate497_chunkChecks2_0
    compactCertificate497_chunkChecks2_1 compactCertificate497_chunkChecks2_2

theorem compactCertificate497_chunkChecks3_0 :
    compactCertificate497.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (737 / 2) 3 (IntervalRat.scale (737 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-41110456797 / 1000000000000) (-41110455394 / 1000000000000), orderedInterval (6181678340 / 1000000000000) (6181679743 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1085741728603037 / 4000000000000) 3 (IntervalRat.scale (737 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (43120552233 / 1000000000000) (43120576666 / 1000000000000), orderedInterval (-22124771333 / 1000000000000) (-22124746900 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (351106567058621 / 800000000000) 3 (IntervalRat.scale (737 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-5866525568 / 1000000000000) (-5866525563 / 1000000000000), orderedInterval (37638181049 / 1000000000000) (37638181054 / 1000000000000)))) (orderedInterval (-6144000631 / 1000000000000) (-6143999943 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (316816728527959 / 4000000000000) 3 (IntervalRat.scale (737 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-88979307778 / 1000000000000) (-88979307774 / 1000000000000), orderedInterval (-10403325352 / 1000000000000) (-10403325347 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (851014296785323 / 4000000000000) 3 (IntervalRat.scale (737 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-4911914258 / 1000000000000) (-4911914247 / 1000000000000), orderedInterval (54492442210 / 1000000000000) (54492442222 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2310669361628991 / 4000000000000) 3 (IntervalRat.scale (737 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (12911499775 / 1000000000000) (12911499776 / 1000000000000), orderedInterval (30572251723 / 1000000000000) (30572251724 / 1000000000000)))) (orderedInterval (7982274104 / 1000000000000) (7982274209 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1702028593571383 / 4000000000000) 3 (IntervalRat.scale (737 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-31782528336 / 1000000000000) (-31782445493 / 1000000000000), orderedInterval (22083088942 / 1000000000000) (22083171785 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2916455005232659 / 4000000000000) 3 (IntervalRat.scale (737 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (25623850385 / 1000000000000) (25623850387 / 1000000000000), orderedInterval (14698409082 / 1000000000000) (14698409084 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2148247556833081 / 4000000000000) 3 (IntervalRat.scale (737 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-20414652873 / 1000000000000) (-20414652872 / 1000000000000), orderedInterval (-27704939876 / 1000000000000) (-27704939875 / 1000000000000)))) (orderedInterval (5573215289 / 1000000000000) (5573215407 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate497_chunkChecks3_1 :
    compactCertificate497.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3295964198834263 / 4000000000000) 3 (IntervalRat.scale (737 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (27633147506 / 1000000000000) (27633158366 / 1000000000000), orderedInterval (-3019091608 / 1000000000000) (-3019080748 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1902925817436127 / 4000000000000) 3 (IntervalRat.scale (737 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-30890254514 / 1000000000000) (-30890159941 / 1000000000000), orderedInterval (19627982571 / 1000000000000) (19628077144 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3376775256198443 / 4000000000000) 3 (IntervalRat.scale (737 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (2997161444 / 1000000000000) (2997161445 / 1000000000000), orderedInterval (-27298896054 / 1000000000000) (-27298896053 / 1000000000000)))) (orderedInterval (37459904778 / 1000000000000) (37459942910 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3155021468106167 / 4000000000000) 3 (IntervalRat.scale (737 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-23919108616 / 1000000000000) (-23919108614 / 1000000000000), orderedInterval (-15314403411 / 1000000000000) (-15314403410 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2251572191454311 / 4000000000000) 3 (IntervalRat.scale (737 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-32684745886 / 1000000000000) (-32684745855 / 1000000000000), orderedInterval (-7888365897 / 1000000000000) (-7888365866 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2553042890355969 / 4000000000000) 3 (IntervalRat.scale (737 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-30453184319 / 1000000000000) (-30453184284 / 1000000000000), orderedInterval (-8344675847 / 1000000000000) (-8344675812 / 1000000000000)))) (orderedInterval (-284888510 / 1000000000000) (-284888298 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2128460993877361 / 4000000000000) 3 (IntervalRat.scale (737 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-31852375632 / 1000000000000) (-31852333468 / 1000000000000), orderedInterval (13514033668 / 1000000000000) (13514075832 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1880559837836581 / 4000000000000) 3 (IntervalRat.scale (737 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-11358909721 / 1000000000000) (-11358909675 / 1000000000000), orderedInterval (35013261865 / 1000000000000) (35013261911 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (545059539345519 / 800000000000) 3 (IntervalRat.scale (737 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-11452586785 / 1000000000000) (-11452586784 / 1000000000000), orderedInterval (-28332803829 / 1000000000000) (-28332803828 / 1000000000000)))) (orderedInterval (8274229876 / 1000000000000) (8274231467 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate497_chunkChecks3_2 :
    compactCertificate497.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1507663370741693 / 4000000000000) 3 (IntervalRat.scale (737 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (26782357109 / 1000000000000) (26782357110 / 1000000000000), orderedInterval (31137043386 / 1000000000000) (31137043387 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1278062936292373 / 4000000000000) 3 (IntervalRat.scale (737 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-6304324364 / 1000000000000) (-6304324353 / 1000000000000), orderedInterval (44199342262 / 1000000000000) (44199342272 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (799752443166919 / 4000000000000) 3 (IntervalRat.scale (737 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-18767121265 / 1000000000000) (-18767120838 / 1000000000000), orderedInterval (53262409679 / 1000000000000) (53262410105 / 1000000000000)))) (orderedInterval (6669343693 / 1000000000000) (6669343775 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (430109523791673 / 4000000000000) 3 (IntervalRat.scale (737 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (76737822697 / 1000000000000) (76737822708 / 1000000000000), orderedInterval (5280522765 / 1000000000000) (5280522776 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1167831025314019 / 4000000000000) 3 (IntervalRat.scale (737 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-25379610721 / 1000000000000) (-25379610720 / 1000000000000), orderedInterval (-39153433746 / 1000000000000) (-39153433745 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1594573424120963 / 4000000000000) 3 (IntervalRat.scale (737 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-17244295051 / 1000000000000) (-17244295050 / 1000000000000), orderedInterval (-36028347623 / 1000000000000) (-36028347622 / 1000000000000)))) (orderedInterval (-3930141760 / 1000000000000) (-3930141719 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (674247556833081 / 4000000000000) 3 (IntervalRat.scale (737 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-18129431426 / 1000000000000) (-18129431112 / 1000000000000), orderedInterval (58774378503 / 1000000000000) (58774378817 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2740778885421401 / 4000000000000) 3 (IntervalRat.scale (737 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27339046019 / 1000000000000) (27339046022 / 1000000000000), orderedInterval (13459079436 / 1000000000000) (13459079439 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1830713276630359 / 4000000000000) 3 (IntervalRat.scale (737 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-7741231655 / 1000000000000) (-7741231645 / 1000000000000), orderedInterval (36492022668 / 1000000000000) (36492022679 / 1000000000000)))) (orderedInterval (20112206724 / 1000000000000) (20112207056 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate497_chunkChecks3 :
    compactCertificate497.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate497.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate497_chunkChecks3_0
    compactCertificate497_chunkChecks3_1 compactCertificate497_chunkChecks3_2

theorem compactCertificate497_chunkChecks4_0 :
    compactCertificate497.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (737 / 2) 4 (IntervalRat.scale (737 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-41110456797 / 1000000000000) (-41110455394 / 1000000000000), orderedInterval (6181678340 / 1000000000000) (6181679743 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1085741728603037 / 4000000000000) 4 (IntervalRat.scale (737 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (43120552233 / 1000000000000) (43120576666 / 1000000000000), orderedInterval (-22124771333 / 1000000000000) (-22124746900 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (351106567058621 / 800000000000) 4 (IntervalRat.scale (737 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-5866525568 / 1000000000000) (-5866525563 / 1000000000000), orderedInterval (37638181049 / 1000000000000) (37638181054 / 1000000000000)))) (orderedInterval (-16835662601 / 1000000000000) (-16835661928 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (316816728527959 / 4000000000000) 4 (IntervalRat.scale (737 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-88979307778 / 1000000000000) (-88979307774 / 1000000000000), orderedInterval (-10403325352 / 1000000000000) (-10403325347 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (851014296785323 / 4000000000000) 4 (IntervalRat.scale (737 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-4911914258 / 1000000000000) (-4911914247 / 1000000000000), orderedInterval (54492442210 / 1000000000000) (54492442222 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2310669361628991 / 4000000000000) 4 (IntervalRat.scale (737 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (12911499775 / 1000000000000) (12911499776 / 1000000000000), orderedInterval (30572251723 / 1000000000000) (30572251724 / 1000000000000)))) (orderedInterval (-5604165617 / 1000000000000) (-5604165455 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1702028593571383 / 4000000000000) 4 (IntervalRat.scale (737 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-31782528336 / 1000000000000) (-31782445493 / 1000000000000), orderedInterval (22083088942 / 1000000000000) (22083171785 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2916455005232659 / 4000000000000) 4 (IntervalRat.scale (737 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (25623850385 / 1000000000000) (25623850387 / 1000000000000), orderedInterval (14698409082 / 1000000000000) (14698409084 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2148247556833081 / 4000000000000) 4 (IntervalRat.scale (737 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-20414652873 / 1000000000000) (-20414652872 / 1000000000000), orderedInterval (-27704939876 / 1000000000000) (-27704939875 / 1000000000000)))) (orderedInterval (-14369093906 / 1000000000000) (-14369093689 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate497_chunkChecks4_1 :
    compactCertificate497.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3295964198834263 / 4000000000000) 4 (IntervalRat.scale (737 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (27633147506 / 1000000000000) (27633158366 / 1000000000000), orderedInterval (-3019091608 / 1000000000000) (-3019080748 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1902925817436127 / 4000000000000) 4 (IntervalRat.scale (737 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-30890254514 / 1000000000000) (-30890159941 / 1000000000000), orderedInterval (19627982571 / 1000000000000) (19628077144 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3376775256198443 / 4000000000000) 4 (IntervalRat.scale (737 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (2997161444 / 1000000000000) (2997161445 / 1000000000000), orderedInterval (-27298896054 / 1000000000000) (-27298896053 / 1000000000000)))) (orderedInterval (-117577335805 / 1000000000000) (-117577264740 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3155021468106167 / 4000000000000) 4 (IntervalRat.scale (737 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-23919108616 / 1000000000000) (-23919108614 / 1000000000000), orderedInterval (-15314403411 / 1000000000000) (-15314403410 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2251572191454311 / 4000000000000) 4 (IntervalRat.scale (737 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-32684745886 / 1000000000000) (-32684745855 / 1000000000000), orderedInterval (-7888365897 / 1000000000000) (-7888365866 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2553042890355969 / 4000000000000) 4 (IntervalRat.scale (737 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-30453184319 / 1000000000000) (-30453184284 / 1000000000000), orderedInterval (-8344675847 / 1000000000000) (-8344675812 / 1000000000000)))) (orderedInterval (-6374997578 / 1000000000000) (-6374997212 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2128460993877361 / 4000000000000) 4 (IntervalRat.scale (737 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-31852375632 / 1000000000000) (-31852333468 / 1000000000000), orderedInterval (13514033668 / 1000000000000) (13514075832 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1880559837836581 / 4000000000000) 4 (IntervalRat.scale (737 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-11358909721 / 1000000000000) (-11358909675 / 1000000000000), orderedInterval (35013261865 / 1000000000000) (35013261911 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (545059539345519 / 800000000000) 4 (IntervalRat.scale (737 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-11452586785 / 1000000000000) (-11452586784 / 1000000000000), orderedInterval (-28332803829 / 1000000000000) (-28332803828 / 1000000000000)))) (orderedInterval (-3348587300 / 1000000000000) (-3348584982 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate497_chunkChecks4_2 :
    compactCertificate497.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1507663370741693 / 4000000000000) 4 (IntervalRat.scale (737 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (26782357109 / 1000000000000) (26782357110 / 1000000000000), orderedInterval (31137043386 / 1000000000000) (31137043387 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1278062936292373 / 4000000000000) 4 (IntervalRat.scale (737 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-6304324364 / 1000000000000) (-6304324353 / 1000000000000), orderedInterval (44199342262 / 1000000000000) (44199342272 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (799752443166919 / 4000000000000) 4 (IntervalRat.scale (737 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-18767121265 / 1000000000000) (-18767120838 / 1000000000000), orderedInterval (53262409679 / 1000000000000) (53262410105 / 1000000000000)))) (orderedInterval (-4574529101 / 1000000000000) (-4574529021 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (430109523791673 / 4000000000000) 4 (IntervalRat.scale (737 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (76737822697 / 1000000000000) (76737822708 / 1000000000000), orderedInterval (5280522765 / 1000000000000) (5280522776 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1167831025314019 / 4000000000000) 4 (IntervalRat.scale (737 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-25379610721 / 1000000000000) (-25379610720 / 1000000000000), orderedInterval (-39153433746 / 1000000000000) (-39153433745 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1594573424120963 / 4000000000000) 4 (IntervalRat.scale (737 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-17244295051 / 1000000000000) (-17244295050 / 1000000000000), orderedInterval (-36028347623 / 1000000000000) (-36028347622 / 1000000000000)))) (orderedInterval (2047938015 / 1000000000000) (2047938058 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (674247556833081 / 4000000000000) 4 (IntervalRat.scale (737 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-18129431426 / 1000000000000) (-18129431112 / 1000000000000), orderedInterval (58774378503 / 1000000000000) (58774378817 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2740778885421401 / 4000000000000) 4 (IntervalRat.scale (737 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27339046019 / 1000000000000) (27339046022 / 1000000000000), orderedInterval (13459079436 / 1000000000000) (13459079439 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1830713276630359 / 4000000000000) 4 (IntervalRat.scale (737 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-7741231655 / 1000000000000) (-7741231645 / 1000000000000), orderedInterval (36492022668 / 1000000000000) (36492022679 / 1000000000000)))) (orderedInterval (-23260279169 / 1000000000000) (-23260278637 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate497_chunkChecks4 :
    compactCertificate497.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate497.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate497_chunkChecks4_0
    compactCertificate497_chunkChecks4_1 compactCertificate497_chunkChecks4_2

theorem compactCertificate497_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate497.chunkCheck r b = true :=
  compactCertificate497.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate497_chunkChecks0
    · exact compactCertificate497_chunkChecks1
    · exact compactCertificate497_chunkChecks2
    · exact compactCertificate497_chunkChecks3
    · exact compactCertificate497_chunkChecks4)

theorem compactCertificate497_coefficient0 :
    compactCertificate497.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate497_coefficient1 :
    compactCertificate497.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate497_coefficient2 :
    compactCertificate497.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate497_coefficient3 :
    compactCertificate497.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate497_coefficient4 :
    compactCertificate497.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate497_coefficients : ∀ r : Fin 5,
    compactCertificate497.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate497_coefficient0
  · exact compactCertificate497_coefficient1
  · exact compactCertificate497_coefficient2
  · exact compactCertificate497_coefficient3
  · exact compactCertificate497_coefficient4

theorem compactCertificate497_lower : (1 : ℚ) ≤ compactCertificate497.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate497, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate497_proves {t : ℝ} (ht : t ∈ compactCertificate497.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate497.proves compactCertificate497_states compactCertificate497_chunks
    compactCertificate497_coefficients compactCertificate497_lower ht

end Erdos232
