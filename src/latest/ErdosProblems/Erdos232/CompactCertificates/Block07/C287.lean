/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate287 : CompactCertificate where
  left := 161
  right := 162
  center := 323 / 2
  grid := fun i =>
    match i.val with
    | 0 => 51
    | 1 => 38
    | 2 => 61
    | 3 => 11
    | 4 => 30
    | 5 => 81
    | 6 => 59
    | 7 => 102
    | 8 => 75
    | 9 => 115
    | 10 => 66
    | 11 => 118
    | 12 => 110
    | 13 => 79
    | 14 => 89
    | 15 => 74
    | 16 => 66
    | 17 => 95
    | 18 => 53
    | 19 => 45
    | 20 => 28
    | 21 => 15
    | 22 => 41
    | 23 => 56
    | 24 => 24
    | 25 => 96
    | _ => 64
  point := fun i =>
    match i.val with
    | 0 => 323 / 2
    | 1 => 475840676172023 / 4000000000000
    | 2 => 153877097910359 / 800000000000
    | 3 => 138849122543461 / 4000000000000
    | 4 => 372968273896417 / 4000000000000
    | 5 => 1012681416290589 / 4000000000000
    | 6 => 745936547793157 / 4000000000000
    | 7 => 1278174988724761 / 4000000000000
    | 8 => 941497911610699 / 4000000000000
    | 9 => 1444499913464677 / 4000000000000
    | 10 => 833982413883133 / 4000000000000
    | 11 => 1479916428428897 / 4000000000000
    | 12 => 1382729897148293 / 4000000000000
    | 13 => 986781299646869 / 4000000000000
    | 14 => 1118904821689251 / 4000000000000
    | 15 => 932826188632819 / 4000000000000
    | 16 => 824180227437199 / 4000000000000
    | 17 => 238879553878701 / 800000000000
    | 18 => 660753417570647 / 4000000000000
    | 19 => 560127989718367 / 4000000000000
    | 20 => 350502088389301 / 4000000000000
    | 21 => 188501188853067 / 4000000000000
    | 22 => 511817396440201 / 4000000000000
    | 23 => 698842898223977 / 4000000000000
    | 24 => 295497911610699 / 4000000000000
    | 25 => 1201182605143979 / 4000000000000
    | _ => 802334312553061 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-55319789228 / 1000000000000) (-55319771738 / 1000000000000), orderedInterval (29863504362 / 1000000000000) (29863521851 / 1000000000000))
    | 1 => (orderedInterval (26043579264 / 1000000000000) (26043579265 / 1000000000000), orderedInterval (68252110175 / 1000000000000) (68252110176 / 1000000000000))
    | 2 => (orderedInterval (-57360689220 / 1000000000000) (-57360689199 / 1000000000000), orderedInterval (-4266477750 / 1000000000000) (-4266477730 / 1000000000000))
    | 3 => (orderedInterval (-109082419635 / 1000000000000) (-109082419634 / 1000000000000), orderedInterval (-78680945693 / 1000000000000) (-78680945692 / 1000000000000))
    | 4 => (orderedInterval (-18165340793 / 1000000000000) (-18165340609 / 1000000000000), orderedInterval (80705790095 / 1000000000000) (80705790279 / 1000000000000))
    | 5 => (orderedInterval (24643749419 / 1000000000000) (24643751883 / 1000000000000), orderedInterval (-43721072274 / 1000000000000) (-43721069810 / 1000000000000))
    | 6 => (orderedInterval (-55002542100 / 1000000000000) (-55002537647 / 1000000000000), orderedInterval (19858185188 / 1000000000000) (19858189641 / 1000000000000))
    | 7 => (orderedInterval (-5063906232 / 1000000000000) (-5063906225 / 1000000000000), orderedInterval (44354700148 / 1000000000000) (44354700155 / 1000000000000))
    | 8 => (orderedInterval (-26733912586 / 1000000000000) (-26733912585 / 1000000000000), orderedInterval (-44552750381 / 1000000000000) (-44552750380 / 1000000000000))
    | 9 => (orderedInterval (-24630074271 / 1000000000000) (-24630074270 / 1000000000000), orderedInterval (-33969417612 / 1000000000000) (-33969417611 / 1000000000000))
    | 10 => (orderedInterval (51627351167 / 1000000000000) (51627357360 / 1000000000000), orderedInterval (-19821688470 / 1000000000000) (-19821682277 / 1000000000000))
    | 11 => (orderedInterval (2331436393 / 1000000000000) (2331436394 / 1000000000000), orderedInterval (41412511828 / 1000000000000) (41412511829 / 1000000000000))
    | 12 => (orderedInterval (33409969455 / 1000000000000) (33409969456 / 1000000000000), orderedInterval (26885021773 / 1000000000000) (26885021774 / 1000000000000))
    | 13 => (orderedInterval (32943097134 / 1000000000000) (32943115421 / 1000000000000), orderedInterval (-38736451800 / 1000000000000) (-38736433512 / 1000000000000))
    | 14 => (orderedInterval (-37646811849 / 1000000000000) (-37646811848 / 1000000000000), orderedInterval (-29234314380 / 1000000000000) (-29234314379 / 1000000000000))
    | 15 => (orderedInterval (52162362752 / 1000000000000) (52162362790 / 1000000000000), orderedInterval (2877385340 / 1000000000000) (2877385377 / 1000000000000))
    | 16 => (orderedInterval (-27390500146 / 1000000000000) (-27390496893 / 1000000000000), orderedInterval (48434602636 / 1000000000000) (48434605890 / 1000000000000))
    | 17 => (orderedInterval (-37099747947 / 1000000000000) (-37099747946 / 1000000000000), orderedInterval (-27426549931 / 1000000000000) (-27426549930 / 1000000000000))
    | 18 => (orderedInterval (31459085324 / 1000000000000) (31459090145 / 1000000000000), orderedInterval (-53613786811 / 1000000000000) (-53613781990 / 1000000000000))
    | 19 => (orderedInterval (35539019950 / 1000000000000) (35539026986 / 1000000000000), orderedInterval (-57426424055 / 1000000000000) (-57426417019 / 1000000000000))
    | 20 => (orderedInterval (36682622533 / 1000000000000) (36682622534 / 1000000000000), orderedInterval (76730226407 / 1000000000000) (76730226408 / 1000000000000))
    | 21 => (orderedInterval (-82081381681 / 1000000000000) (-82081381680 / 1000000000000), orderedInterval (-81419774105 / 1000000000000) (-81419774104 / 1000000000000))
    | 22 => (orderedInterval (4689187141 / 1000000000000) (4689187156 / 1000000000000), orderedInterval (-70398829186 / 1000000000000) (-70398829171 / 1000000000000))
    | 23 => (orderedInterval (-25371367550 / 1000000000000) (-25371365989 / 1000000000000), orderedInterval (54846269435 / 1000000000000) (54846270996 / 1000000000000))
    | 24 => (orderedInterval (-62596813268 / 1000000000000) (-62596758164 / 1000000000000), orderedInterval (68974678866 / 1000000000000) (68974733970 / 1000000000000))
    | 25 => (orderedInterval (-22568050394 / 1000000000000) (-22568048539 / 1000000000000), orderedInterval (40170620692 / 1000000000000) (40170622547 / 1000000000000))
    | _ => (orderedInterval (16994004134 / 1000000000000) (16994004135 / 1000000000000), orderedInterval (53670298808 / 1000000000000) (53670298809 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-25050142877 / 1000000000000) (-25050135931 / 1000000000000)
      | 1 => orderedInterval (-1231696880 / 1000000000000) (-1231696678 / 1000000000000)
      | 2 => orderedInterval (-489914797 / 1000000000000) (-489914787 / 1000000000000)
      | 3 => orderedInterval (8533056082 / 1000000000000) (8533056606 / 1000000000000)
      | 4 => orderedInterval (2702555171 / 1000000000000) (2702556920 / 1000000000000)
      | 5 => orderedInterval (1219920770 / 1000000000000) (1219920973 / 1000000000000)
      | 6 => orderedInterval (-5847365413 / 1000000000000) (-5847364203 / 1000000000000)
      | 7 => orderedInterval (3353692184 / 1000000000000) (3353692324 / 1000000000000)
      | _ => orderedInterval (-1728800866 / 1000000000000) (-1728800337 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (12007124980 / 1000000000000) (12007131927 / 1000000000000)
      | 1 => orderedInterval (6757098540 / 1000000000000) (6757098841 / 1000000000000)
      | 2 => orderedInterval (-4276162371 / 1000000000000) (-4276162354 / 1000000000000)
      | 3 => orderedInterval (25087378581 / 1000000000000) (25087379308 / 1000000000000)
      | 4 => orderedInterval (-6378009833 / 1000000000000) (-6378007160 / 1000000000000)
      | 5 => orderedInterval (-4786636679 / 1000000000000) (-4786636418 / 1000000000000)
      | 6 => orderedInterval (12941819215 / 1000000000000) (12941820387 / 1000000000000)
      | 7 => orderedInterval (-2843111413 / 1000000000000) (-2843111265 / 1000000000000)
      | _ => orderedInterval (-18396957306 / 1000000000000) (-18396956809 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (26495391567 / 1000000000000) (26495398560 / 1000000000000)
      | 1 => orderedInterval (4429773716 / 1000000000000) (4429774181 / 1000000000000)
      | 2 => orderedInterval (787401837 / 1000000000000) (787401866 / 1000000000000)
      | 3 => orderedInterval (-30152337849 / 1000000000000) (-30152336794 / 1000000000000)
      | 4 => orderedInterval (-5037482365 / 1000000000000) (-5037478261 / 1000000000000)
      | 5 => orderedInterval (-530538968 / 1000000000000) (-530538629 / 1000000000000)
      | 6 => orderedInterval (6343030247 / 1000000000000) (6343031397 / 1000000000000)
      | 7 => orderedInterval (-2320221075 / 1000000000000) (-2320220916 / 1000000000000)
      | _ => orderedInterval (-1240164060 / 1000000000000) (-1240163372 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-11831662006 / 1000000000000) (-11831655012 / 1000000000000)
      | 1 => orderedInterval (-12576157177 / 1000000000000) (-12576156452 / 1000000000000)
      | 2 => orderedInterval (13925294460 / 1000000000000) (13925294513 / 1000000000000)
      | 3 => orderedInterval (-134916378029 / 1000000000000) (-134916376410 / 1000000000000)
      | 4 => orderedInterval (17077738767 / 1000000000000) (17077745044 / 1000000000000)
      | 5 => orderedInterval (10097500654 / 1000000000000) (10097501096 / 1000000000000)
      | 6 => orderedInterval (-11729870127 / 1000000000000) (-11729869000 / 1000000000000)
      | 7 => orderedInterval (4504138930 / 1000000000000) (4504139101 / 1000000000000)
      | _ => orderedInterval (40281945074 / 1000000000000) (40281946224 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-28480505257 / 1000000000000) (-28480498216 / 1000000000000)
      | 1 => orderedInterval (-10494984816 / 1000000000000) (-10494983678 / 1000000000000)
      | 2 => orderedInterval (-693704157 / 1000000000000) (-693704058 / 1000000000000)
      | 3 => orderedInterval (130835410417 / 1000000000000) (130835413096 / 1000000000000)
      | 4 => orderedInterval (5803065328 / 1000000000000) (5803074972 / 1000000000000)
      | 5 => orderedInterval (-4453710075 / 1000000000000) (-4453709493 / 1000000000000)
      | 6 => orderedInterval (-6393515219 / 1000000000000) (-6393514102 / 1000000000000)
      | 7 => orderedInterval (2576263740 / 1000000000000) (2576263925 / 1000000000000)
      | _ => orderedInterval (13857473293 / 1000000000000) (13857475356 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-18538696626 / 1000000000000) (-18538685113 / 1000000000000)
    | 1 => orderedInterval (20112543714 / 1000000000000) (20112556457 / 1000000000000)
    | 2 => orderedInterval (-1225146950 / 1000000000000) (-1225131968 / 1000000000000)
    | 3 => orderedInterval (-85167449454 / 1000000000000) (-85167430896 / 1000000000000)
    | _ => orderedInterval (102555793254 / 1000000000000) (102555817802 / 1000000000000)

theorem compactCertificate287_stateChecks0 :
    compactCertificate287.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (323 / 2)) (orderedInterval (-55319789228 / 1000000000000) (-55319771738 / 1000000000000), orderedInterval (29863504362 / 1000000000000) (29863521851 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (475840676172023 / 4000000000000)) (orderedInterval (26043579264 / 1000000000000) (26043579265 / 1000000000000), orderedInterval (68252110175 / 1000000000000) (68252110176 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 61 12 (153877097910359 / 800000000000)) (orderedInterval (-57360689220 / 1000000000000) (-57360689199 / 1000000000000), orderedInterval (-4266477750 / 1000000000000) (-4266477730 / 1000000000000))) = true
  rfl'

theorem compactCertificate287_stateChecks1 :
    compactCertificate287.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 11 12 (138849122543461 / 4000000000000)) (orderedInterval (-109082419635 / 1000000000000) (-109082419634 / 1000000000000), orderedInterval (-78680945693 / 1000000000000) (-78680945692 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (372968273896417 / 4000000000000)) (orderedInterval (-18165340793 / 1000000000000) (-18165340609 / 1000000000000), orderedInterval (80705790095 / 1000000000000) (80705790279 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 81 12 (1012681416290589 / 4000000000000)) (orderedInterval (24643749419 / 1000000000000) (24643751883 / 1000000000000), orderedInterval (-43721072274 / 1000000000000) (-43721069810 / 1000000000000))) = true
  rfl'

theorem compactCertificate287_stateChecks2 :
    compactCertificate287.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 59 12 (745936547793157 / 4000000000000)) (orderedInterval (-55002542100 / 1000000000000) (-55002537647 / 1000000000000), orderedInterval (19858185188 / 1000000000000) (19858189641 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 102 12 (1278174988724761 / 4000000000000)) (orderedInterval (-5063906232 / 1000000000000) (-5063906225 / 1000000000000), orderedInterval (44354700148 / 1000000000000) (44354700155 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 75 12 (941497911610699 / 4000000000000)) (orderedInterval (-26733912586 / 1000000000000) (-26733912585 / 1000000000000), orderedInterval (-44552750381 / 1000000000000) (-44552750380 / 1000000000000))) = true
  rfl'

theorem compactCertificate287_stateChecks3 :
    compactCertificate287.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 115 12 (1444499913464677 / 4000000000000)) (orderedInterval (-24630074271 / 1000000000000) (-24630074270 / 1000000000000), orderedInterval (-33969417612 / 1000000000000) (-33969417611 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (833982413883133 / 4000000000000)) (orderedInterval (51627351167 / 1000000000000) (51627357360 / 1000000000000), orderedInterval (-19821688470 / 1000000000000) (-19821682277 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 118 12 (1479916428428897 / 4000000000000)) (orderedInterval (2331436393 / 1000000000000) (2331436394 / 1000000000000), orderedInterval (41412511828 / 1000000000000) (41412511829 / 1000000000000))) = true
  rfl'

theorem compactCertificate287_stateChecks4 :
    compactCertificate287.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 110 12 (1382729897148293 / 4000000000000)) (orderedInterval (33409969455 / 1000000000000) (33409969456 / 1000000000000), orderedInterval (26885021773 / 1000000000000) (26885021774 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 79 12 (986781299646869 / 4000000000000)) (orderedInterval (32943097134 / 1000000000000) (32943115421 / 1000000000000), orderedInterval (-38736451800 / 1000000000000) (-38736433512 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 89 12 (1118904821689251 / 4000000000000)) (orderedInterval (-37646811849 / 1000000000000) (-37646811848 / 1000000000000), orderedInterval (-29234314380 / 1000000000000) (-29234314379 / 1000000000000))) = true
  rfl'

theorem compactCertificate287_stateChecks5 :
    compactCertificate287.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 74 12 (932826188632819 / 4000000000000)) (orderedInterval (52162362752 / 1000000000000) (52162362790 / 1000000000000), orderedInterval (2877385340 / 1000000000000) (2877385377 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (824180227437199 / 4000000000000)) (orderedInterval (-27390500146 / 1000000000000) (-27390496893 / 1000000000000), orderedInterval (48434602636 / 1000000000000) (48434605890 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 95 12 (238879553878701 / 800000000000)) (orderedInterval (-37099747947 / 1000000000000) (-37099747946 / 1000000000000), orderedInterval (-27426549931 / 1000000000000) (-27426549930 / 1000000000000))) = true
  rfl'

theorem compactCertificate287_stateChecks6 :
    compactCertificate287.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 53 12 (660753417570647 / 4000000000000)) (orderedInterval (31459085324 / 1000000000000) (31459090145 / 1000000000000), orderedInterval (-53613786811 / 1000000000000) (-53613781990 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (560127989718367 / 4000000000000)) (orderedInterval (35539019950 / 1000000000000) (35539026986 / 1000000000000), orderedInterval (-57426424055 / 1000000000000) (-57426417019 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 28 12 (350502088389301 / 4000000000000)) (orderedInterval (36682622533 / 1000000000000) (36682622534 / 1000000000000), orderedInterval (76730226407 / 1000000000000) (76730226408 / 1000000000000))) = true
  rfl'

theorem compactCertificate287_stateChecks7 :
    compactCertificate287.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 15 12 (188501188853067 / 4000000000000)) (orderedInterval (-82081381681 / 1000000000000) (-82081381680 / 1000000000000), orderedInterval (-81419774105 / 1000000000000) (-81419774104 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 41 12 (511817396440201 / 4000000000000)) (orderedInterval (4689187141 / 1000000000000) (4689187156 / 1000000000000), orderedInterval (-70398829186 / 1000000000000) (-70398829171 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 56 12 (698842898223977 / 4000000000000)) (orderedInterval (-25371367550 / 1000000000000) (-25371365989 / 1000000000000), orderedInterval (54846269435 / 1000000000000) (54846270996 / 1000000000000))) = true
  rfl'

theorem compactCertificate287_stateChecks8 :
    compactCertificate287.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 24 12 (295497911610699 / 4000000000000)) (orderedInterval (-62596813268 / 1000000000000) (-62596758164 / 1000000000000), orderedInterval (68974678866 / 1000000000000) (68974733970 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 96 12 (1201182605143979 / 4000000000000)) (orderedInterval (-22568050394 / 1000000000000) (-22568048539 / 1000000000000), orderedInterval (40170620692 / 1000000000000) (40170622547 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (802334312553061 / 4000000000000)) (orderedInterval (16994004134 / 1000000000000) (16994004135 / 1000000000000), orderedInterval (53670298808 / 1000000000000) (53670298809 / 1000000000000))) = true
  rfl'

theorem compactCertificate287_states : ∀ j,
    BesselStateValid (compactCertificate287.point j) (compactCertificate287.state j) :=
  compactCertificate287.statesValid_of_checks3 compactCertificate287_stateChecks0
    compactCertificate287_stateChecks1 compactCertificate287_stateChecks2
    compactCertificate287_stateChecks3 compactCertificate287_stateChecks4
    compactCertificate287_stateChecks5 compactCertificate287_stateChecks6
    compactCertificate287_stateChecks7 compactCertificate287_stateChecks8

theorem compactCertificate287_chunkChecks0_0 :
    compactCertificate287.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (323 / 2) 0 (IntervalRat.scale (323 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-55319789228 / 1000000000000) (-55319771738 / 1000000000000), orderedInterval (29863504362 / 1000000000000) (29863521851 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (475840676172023 / 4000000000000) 0 (IntervalRat.scale (323 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (26043579264 / 1000000000000) (26043579265 / 1000000000000), orderedInterval (68252110175 / 1000000000000) (68252110176 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (153877097910359 / 800000000000) 0 (IntervalRat.scale (323 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-57360689220 / 1000000000000) (-57360689199 / 1000000000000), orderedInterval (-4266477750 / 1000000000000) (-4266477730 / 1000000000000)))) (orderedInterval (-25050142877 / 1000000000000) (-25050135931 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (138849122543461 / 4000000000000) 0 (IntervalRat.scale (323 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-109082419635 / 1000000000000) (-109082419634 / 1000000000000), orderedInterval (-78680945693 / 1000000000000) (-78680945692 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (372968273896417 / 4000000000000) 0 (IntervalRat.scale (323 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-18165340793 / 1000000000000) (-18165340609 / 1000000000000), orderedInterval (80705790095 / 1000000000000) (80705790279 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1012681416290589 / 4000000000000) 0 (IntervalRat.scale (323 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (24643749419 / 1000000000000) (24643751883 / 1000000000000), orderedInterval (-43721072274 / 1000000000000) (-43721069810 / 1000000000000)))) (orderedInterval (-1231696880 / 1000000000000) (-1231696678 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (745936547793157 / 4000000000000) 0 (IntervalRat.scale (323 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-55002542100 / 1000000000000) (-55002537647 / 1000000000000), orderedInterval (19858185188 / 1000000000000) (19858189641 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1278174988724761 / 4000000000000) 0 (IntervalRat.scale (323 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-5063906232 / 1000000000000) (-5063906225 / 1000000000000), orderedInterval (44354700148 / 1000000000000) (44354700155 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (941497911610699 / 4000000000000) 0 (IntervalRat.scale (323 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-26733912586 / 1000000000000) (-26733912585 / 1000000000000), orderedInterval (-44552750381 / 1000000000000) (-44552750380 / 1000000000000)))) (orderedInterval (-489914797 / 1000000000000) (-489914787 / 1000000000000))) = true
  rfl'

theorem compactCertificate287_chunkChecks0_1 :
    compactCertificate287.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1444499913464677 / 4000000000000) 0 (IntervalRat.scale (323 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-24630074271 / 1000000000000) (-24630074270 / 1000000000000), orderedInterval (-33969417612 / 1000000000000) (-33969417611 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (833982413883133 / 4000000000000) 0 (IntervalRat.scale (323 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (51627351167 / 1000000000000) (51627357360 / 1000000000000), orderedInterval (-19821688470 / 1000000000000) (-19821682277 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1479916428428897 / 4000000000000) 0 (IntervalRat.scale (323 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (2331436393 / 1000000000000) (2331436394 / 1000000000000), orderedInterval (41412511828 / 1000000000000) (41412511829 / 1000000000000)))) (orderedInterval (8533056082 / 1000000000000) (8533056606 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1382729897148293 / 4000000000000) 0 (IntervalRat.scale (323 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (33409969455 / 1000000000000) (33409969456 / 1000000000000), orderedInterval (26885021773 / 1000000000000) (26885021774 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (986781299646869 / 4000000000000) 0 (IntervalRat.scale (323 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (32943097134 / 1000000000000) (32943115421 / 1000000000000), orderedInterval (-38736451800 / 1000000000000) (-38736433512 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1118904821689251 / 4000000000000) 0 (IntervalRat.scale (323 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-37646811849 / 1000000000000) (-37646811848 / 1000000000000), orderedInterval (-29234314380 / 1000000000000) (-29234314379 / 1000000000000)))) (orderedInterval (2702555171 / 1000000000000) (2702556920 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (932826188632819 / 4000000000000) 0 (IntervalRat.scale (323 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (52162362752 / 1000000000000) (52162362790 / 1000000000000), orderedInterval (2877385340 / 1000000000000) (2877385377 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (824180227437199 / 4000000000000) 0 (IntervalRat.scale (323 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-27390500146 / 1000000000000) (-27390496893 / 1000000000000), orderedInterval (48434602636 / 1000000000000) (48434605890 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (238879553878701 / 800000000000) 0 (IntervalRat.scale (323 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-37099747947 / 1000000000000) (-37099747946 / 1000000000000), orderedInterval (-27426549931 / 1000000000000) (-27426549930 / 1000000000000)))) (orderedInterval (1219920770 / 1000000000000) (1219920973 / 1000000000000))) = true
  rfl'

theorem compactCertificate287_chunkChecks0_2 :
    compactCertificate287.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (660753417570647 / 4000000000000) 0 (IntervalRat.scale (323 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (31459085324 / 1000000000000) (31459090145 / 1000000000000), orderedInterval (-53613786811 / 1000000000000) (-53613781990 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (560127989718367 / 4000000000000) 0 (IntervalRat.scale (323 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (35539019950 / 1000000000000) (35539026986 / 1000000000000), orderedInterval (-57426424055 / 1000000000000) (-57426417019 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (350502088389301 / 4000000000000) 0 (IntervalRat.scale (323 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (36682622533 / 1000000000000) (36682622534 / 1000000000000), orderedInterval (76730226407 / 1000000000000) (76730226408 / 1000000000000)))) (orderedInterval (-5847365413 / 1000000000000) (-5847364203 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (188501188853067 / 4000000000000) 0 (IntervalRat.scale (323 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-82081381681 / 1000000000000) (-82081381680 / 1000000000000), orderedInterval (-81419774105 / 1000000000000) (-81419774104 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (511817396440201 / 4000000000000) 0 (IntervalRat.scale (323 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (4689187141 / 1000000000000) (4689187156 / 1000000000000), orderedInterval (-70398829186 / 1000000000000) (-70398829171 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (698842898223977 / 4000000000000) 0 (IntervalRat.scale (323 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-25371367550 / 1000000000000) (-25371365989 / 1000000000000), orderedInterval (54846269435 / 1000000000000) (54846270996 / 1000000000000)))) (orderedInterval (3353692184 / 1000000000000) (3353692324 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (295497911610699 / 4000000000000) 0 (IntervalRat.scale (323 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-62596813268 / 1000000000000) (-62596758164 / 1000000000000), orderedInterval (68974678866 / 1000000000000) (68974733970 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1201182605143979 / 4000000000000) 0 (IntervalRat.scale (323 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-22568050394 / 1000000000000) (-22568048539 / 1000000000000), orderedInterval (40170620692 / 1000000000000) (40170622547 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (802334312553061 / 4000000000000) 0 (IntervalRat.scale (323 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (16994004134 / 1000000000000) (16994004135 / 1000000000000), orderedInterval (53670298808 / 1000000000000) (53670298809 / 1000000000000)))) (orderedInterval (-1728800866 / 1000000000000) (-1728800337 / 1000000000000))) = true
  rfl'

theorem compactCertificate287_chunkChecks0 :
    compactCertificate287.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate287.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate287_chunkChecks0_0
    compactCertificate287_chunkChecks0_1 compactCertificate287_chunkChecks0_2

theorem compactCertificate287_chunkChecks1_0 :
    compactCertificate287.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (323 / 2) 1 (IntervalRat.scale (323 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-55319789228 / 1000000000000) (-55319771738 / 1000000000000), orderedInterval (29863504362 / 1000000000000) (29863521851 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (475840676172023 / 4000000000000) 1 (IntervalRat.scale (323 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (26043579264 / 1000000000000) (26043579265 / 1000000000000), orderedInterval (68252110175 / 1000000000000) (68252110176 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (153877097910359 / 800000000000) 1 (IntervalRat.scale (323 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-57360689220 / 1000000000000) (-57360689199 / 1000000000000), orderedInterval (-4266477750 / 1000000000000) (-4266477730 / 1000000000000)))) (orderedInterval (12007124980 / 1000000000000) (12007131927 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (138849122543461 / 4000000000000) 1 (IntervalRat.scale (323 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-109082419635 / 1000000000000) (-109082419634 / 1000000000000), orderedInterval (-78680945693 / 1000000000000) (-78680945692 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (372968273896417 / 4000000000000) 1 (IntervalRat.scale (323 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-18165340793 / 1000000000000) (-18165340609 / 1000000000000), orderedInterval (80705790095 / 1000000000000) (80705790279 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1012681416290589 / 4000000000000) 1 (IntervalRat.scale (323 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (24643749419 / 1000000000000) (24643751883 / 1000000000000), orderedInterval (-43721072274 / 1000000000000) (-43721069810 / 1000000000000)))) (orderedInterval (6757098540 / 1000000000000) (6757098841 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (745936547793157 / 4000000000000) 1 (IntervalRat.scale (323 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-55002542100 / 1000000000000) (-55002537647 / 1000000000000), orderedInterval (19858185188 / 1000000000000) (19858189641 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1278174988724761 / 4000000000000) 1 (IntervalRat.scale (323 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-5063906232 / 1000000000000) (-5063906225 / 1000000000000), orderedInterval (44354700148 / 1000000000000) (44354700155 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (941497911610699 / 4000000000000) 1 (IntervalRat.scale (323 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-26733912586 / 1000000000000) (-26733912585 / 1000000000000), orderedInterval (-44552750381 / 1000000000000) (-44552750380 / 1000000000000)))) (orderedInterval (-4276162371 / 1000000000000) (-4276162354 / 1000000000000))) = true
  rfl'

theorem compactCertificate287_chunkChecks1_1 :
    compactCertificate287.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1444499913464677 / 4000000000000) 1 (IntervalRat.scale (323 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-24630074271 / 1000000000000) (-24630074270 / 1000000000000), orderedInterval (-33969417612 / 1000000000000) (-33969417611 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (833982413883133 / 4000000000000) 1 (IntervalRat.scale (323 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (51627351167 / 1000000000000) (51627357360 / 1000000000000), orderedInterval (-19821688470 / 1000000000000) (-19821682277 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1479916428428897 / 4000000000000) 1 (IntervalRat.scale (323 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (2331436393 / 1000000000000) (2331436394 / 1000000000000), orderedInterval (41412511828 / 1000000000000) (41412511829 / 1000000000000)))) (orderedInterval (25087378581 / 1000000000000) (25087379308 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1382729897148293 / 4000000000000) 1 (IntervalRat.scale (323 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (33409969455 / 1000000000000) (33409969456 / 1000000000000), orderedInterval (26885021773 / 1000000000000) (26885021774 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (986781299646869 / 4000000000000) 1 (IntervalRat.scale (323 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (32943097134 / 1000000000000) (32943115421 / 1000000000000), orderedInterval (-38736451800 / 1000000000000) (-38736433512 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1118904821689251 / 4000000000000) 1 (IntervalRat.scale (323 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-37646811849 / 1000000000000) (-37646811848 / 1000000000000), orderedInterval (-29234314380 / 1000000000000) (-29234314379 / 1000000000000)))) (orderedInterval (-6378009833 / 1000000000000) (-6378007160 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (932826188632819 / 4000000000000) 1 (IntervalRat.scale (323 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (52162362752 / 1000000000000) (52162362790 / 1000000000000), orderedInterval (2877385340 / 1000000000000) (2877385377 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (824180227437199 / 4000000000000) 1 (IntervalRat.scale (323 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-27390500146 / 1000000000000) (-27390496893 / 1000000000000), orderedInterval (48434602636 / 1000000000000) (48434605890 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (238879553878701 / 800000000000) 1 (IntervalRat.scale (323 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-37099747947 / 1000000000000) (-37099747946 / 1000000000000), orderedInterval (-27426549931 / 1000000000000) (-27426549930 / 1000000000000)))) (orderedInterval (-4786636679 / 1000000000000) (-4786636418 / 1000000000000))) = true
  rfl'

theorem compactCertificate287_chunkChecks1_2 :
    compactCertificate287.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (660753417570647 / 4000000000000) 1 (IntervalRat.scale (323 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (31459085324 / 1000000000000) (31459090145 / 1000000000000), orderedInterval (-53613786811 / 1000000000000) (-53613781990 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (560127989718367 / 4000000000000) 1 (IntervalRat.scale (323 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (35539019950 / 1000000000000) (35539026986 / 1000000000000), orderedInterval (-57426424055 / 1000000000000) (-57426417019 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (350502088389301 / 4000000000000) 1 (IntervalRat.scale (323 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (36682622533 / 1000000000000) (36682622534 / 1000000000000), orderedInterval (76730226407 / 1000000000000) (76730226408 / 1000000000000)))) (orderedInterval (12941819215 / 1000000000000) (12941820387 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (188501188853067 / 4000000000000) 1 (IntervalRat.scale (323 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-82081381681 / 1000000000000) (-82081381680 / 1000000000000), orderedInterval (-81419774105 / 1000000000000) (-81419774104 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (511817396440201 / 4000000000000) 1 (IntervalRat.scale (323 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (4689187141 / 1000000000000) (4689187156 / 1000000000000), orderedInterval (-70398829186 / 1000000000000) (-70398829171 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (698842898223977 / 4000000000000) 1 (IntervalRat.scale (323 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-25371367550 / 1000000000000) (-25371365989 / 1000000000000), orderedInterval (54846269435 / 1000000000000) (54846270996 / 1000000000000)))) (orderedInterval (-2843111413 / 1000000000000) (-2843111265 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (295497911610699 / 4000000000000) 1 (IntervalRat.scale (323 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-62596813268 / 1000000000000) (-62596758164 / 1000000000000), orderedInterval (68974678866 / 1000000000000) (68974733970 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1201182605143979 / 4000000000000) 1 (IntervalRat.scale (323 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-22568050394 / 1000000000000) (-22568048539 / 1000000000000), orderedInterval (40170620692 / 1000000000000) (40170622547 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (802334312553061 / 4000000000000) 1 (IntervalRat.scale (323 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (16994004134 / 1000000000000) (16994004135 / 1000000000000), orderedInterval (53670298808 / 1000000000000) (53670298809 / 1000000000000)))) (orderedInterval (-18396957306 / 1000000000000) (-18396956809 / 1000000000000))) = true
  rfl'

theorem compactCertificate287_chunkChecks1 :
    compactCertificate287.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate287.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate287_chunkChecks1_0
    compactCertificate287_chunkChecks1_1 compactCertificate287_chunkChecks1_2

theorem compactCertificate287_chunkChecks2_0 :
    compactCertificate287.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (323 / 2) 2 (IntervalRat.scale (323 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-55319789228 / 1000000000000) (-55319771738 / 1000000000000), orderedInterval (29863504362 / 1000000000000) (29863521851 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (475840676172023 / 4000000000000) 2 (IntervalRat.scale (323 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (26043579264 / 1000000000000) (26043579265 / 1000000000000), orderedInterval (68252110175 / 1000000000000) (68252110176 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (153877097910359 / 800000000000) 2 (IntervalRat.scale (323 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-57360689220 / 1000000000000) (-57360689199 / 1000000000000), orderedInterval (-4266477750 / 1000000000000) (-4266477730 / 1000000000000)))) (orderedInterval (26495391567 / 1000000000000) (26495398560 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (138849122543461 / 4000000000000) 2 (IntervalRat.scale (323 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-109082419635 / 1000000000000) (-109082419634 / 1000000000000), orderedInterval (-78680945693 / 1000000000000) (-78680945692 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (372968273896417 / 4000000000000) 2 (IntervalRat.scale (323 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-18165340793 / 1000000000000) (-18165340609 / 1000000000000), orderedInterval (80705790095 / 1000000000000) (80705790279 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1012681416290589 / 4000000000000) 2 (IntervalRat.scale (323 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (24643749419 / 1000000000000) (24643751883 / 1000000000000), orderedInterval (-43721072274 / 1000000000000) (-43721069810 / 1000000000000)))) (orderedInterval (4429773716 / 1000000000000) (4429774181 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (745936547793157 / 4000000000000) 2 (IntervalRat.scale (323 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-55002542100 / 1000000000000) (-55002537647 / 1000000000000), orderedInterval (19858185188 / 1000000000000) (19858189641 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1278174988724761 / 4000000000000) 2 (IntervalRat.scale (323 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-5063906232 / 1000000000000) (-5063906225 / 1000000000000), orderedInterval (44354700148 / 1000000000000) (44354700155 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (941497911610699 / 4000000000000) 2 (IntervalRat.scale (323 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-26733912586 / 1000000000000) (-26733912585 / 1000000000000), orderedInterval (-44552750381 / 1000000000000) (-44552750380 / 1000000000000)))) (orderedInterval (787401837 / 1000000000000) (787401866 / 1000000000000))) = true
  rfl'

theorem compactCertificate287_chunkChecks2_1 :
    compactCertificate287.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1444499913464677 / 4000000000000) 2 (IntervalRat.scale (323 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-24630074271 / 1000000000000) (-24630074270 / 1000000000000), orderedInterval (-33969417612 / 1000000000000) (-33969417611 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (833982413883133 / 4000000000000) 2 (IntervalRat.scale (323 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (51627351167 / 1000000000000) (51627357360 / 1000000000000), orderedInterval (-19821688470 / 1000000000000) (-19821682277 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1479916428428897 / 4000000000000) 2 (IntervalRat.scale (323 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (2331436393 / 1000000000000) (2331436394 / 1000000000000), orderedInterval (41412511828 / 1000000000000) (41412511829 / 1000000000000)))) (orderedInterval (-30152337849 / 1000000000000) (-30152336794 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1382729897148293 / 4000000000000) 2 (IntervalRat.scale (323 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (33409969455 / 1000000000000) (33409969456 / 1000000000000), orderedInterval (26885021773 / 1000000000000) (26885021774 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (986781299646869 / 4000000000000) 2 (IntervalRat.scale (323 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (32943097134 / 1000000000000) (32943115421 / 1000000000000), orderedInterval (-38736451800 / 1000000000000) (-38736433512 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1118904821689251 / 4000000000000) 2 (IntervalRat.scale (323 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-37646811849 / 1000000000000) (-37646811848 / 1000000000000), orderedInterval (-29234314380 / 1000000000000) (-29234314379 / 1000000000000)))) (orderedInterval (-5037482365 / 1000000000000) (-5037478261 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (932826188632819 / 4000000000000) 2 (IntervalRat.scale (323 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (52162362752 / 1000000000000) (52162362790 / 1000000000000), orderedInterval (2877385340 / 1000000000000) (2877385377 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (824180227437199 / 4000000000000) 2 (IntervalRat.scale (323 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-27390500146 / 1000000000000) (-27390496893 / 1000000000000), orderedInterval (48434602636 / 1000000000000) (48434605890 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (238879553878701 / 800000000000) 2 (IntervalRat.scale (323 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-37099747947 / 1000000000000) (-37099747946 / 1000000000000), orderedInterval (-27426549931 / 1000000000000) (-27426549930 / 1000000000000)))) (orderedInterval (-530538968 / 1000000000000) (-530538629 / 1000000000000))) = true
  rfl'

theorem compactCertificate287_chunkChecks2_2 :
    compactCertificate287.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (660753417570647 / 4000000000000) 2 (IntervalRat.scale (323 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (31459085324 / 1000000000000) (31459090145 / 1000000000000), orderedInterval (-53613786811 / 1000000000000) (-53613781990 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (560127989718367 / 4000000000000) 2 (IntervalRat.scale (323 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (35539019950 / 1000000000000) (35539026986 / 1000000000000), orderedInterval (-57426424055 / 1000000000000) (-57426417019 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (350502088389301 / 4000000000000) 2 (IntervalRat.scale (323 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (36682622533 / 1000000000000) (36682622534 / 1000000000000), orderedInterval (76730226407 / 1000000000000) (76730226408 / 1000000000000)))) (orderedInterval (6343030247 / 1000000000000) (6343031397 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (188501188853067 / 4000000000000) 2 (IntervalRat.scale (323 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-82081381681 / 1000000000000) (-82081381680 / 1000000000000), orderedInterval (-81419774105 / 1000000000000) (-81419774104 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (511817396440201 / 4000000000000) 2 (IntervalRat.scale (323 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (4689187141 / 1000000000000) (4689187156 / 1000000000000), orderedInterval (-70398829186 / 1000000000000) (-70398829171 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (698842898223977 / 4000000000000) 2 (IntervalRat.scale (323 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-25371367550 / 1000000000000) (-25371365989 / 1000000000000), orderedInterval (54846269435 / 1000000000000) (54846270996 / 1000000000000)))) (orderedInterval (-2320221075 / 1000000000000) (-2320220916 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (295497911610699 / 4000000000000) 2 (IntervalRat.scale (323 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-62596813268 / 1000000000000) (-62596758164 / 1000000000000), orderedInterval (68974678866 / 1000000000000) (68974733970 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1201182605143979 / 4000000000000) 2 (IntervalRat.scale (323 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-22568050394 / 1000000000000) (-22568048539 / 1000000000000), orderedInterval (40170620692 / 1000000000000) (40170622547 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (802334312553061 / 4000000000000) 2 (IntervalRat.scale (323 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (16994004134 / 1000000000000) (16994004135 / 1000000000000), orderedInterval (53670298808 / 1000000000000) (53670298809 / 1000000000000)))) (orderedInterval (-1240164060 / 1000000000000) (-1240163372 / 1000000000000))) = true
  rfl'

theorem compactCertificate287_chunkChecks2 :
    compactCertificate287.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate287.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate287_chunkChecks2_0
    compactCertificate287_chunkChecks2_1 compactCertificate287_chunkChecks2_2

theorem compactCertificate287_chunkChecks3_0 :
    compactCertificate287.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (323 / 2) 3 (IntervalRat.scale (323 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-55319789228 / 1000000000000) (-55319771738 / 1000000000000), orderedInterval (29863504362 / 1000000000000) (29863521851 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (475840676172023 / 4000000000000) 3 (IntervalRat.scale (323 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (26043579264 / 1000000000000) (26043579265 / 1000000000000), orderedInterval (68252110175 / 1000000000000) (68252110176 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (153877097910359 / 800000000000) 3 (IntervalRat.scale (323 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-57360689220 / 1000000000000) (-57360689199 / 1000000000000), orderedInterval (-4266477750 / 1000000000000) (-4266477730 / 1000000000000)))) (orderedInterval (-11831662006 / 1000000000000) (-11831655012 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (138849122543461 / 4000000000000) 3 (IntervalRat.scale (323 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-109082419635 / 1000000000000) (-109082419634 / 1000000000000), orderedInterval (-78680945693 / 1000000000000) (-78680945692 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (372968273896417 / 4000000000000) 3 (IntervalRat.scale (323 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-18165340793 / 1000000000000) (-18165340609 / 1000000000000), orderedInterval (80705790095 / 1000000000000) (80705790279 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1012681416290589 / 4000000000000) 3 (IntervalRat.scale (323 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (24643749419 / 1000000000000) (24643751883 / 1000000000000), orderedInterval (-43721072274 / 1000000000000) (-43721069810 / 1000000000000)))) (orderedInterval (-12576157177 / 1000000000000) (-12576156452 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (745936547793157 / 4000000000000) 3 (IntervalRat.scale (323 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-55002542100 / 1000000000000) (-55002537647 / 1000000000000), orderedInterval (19858185188 / 1000000000000) (19858189641 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1278174988724761 / 4000000000000) 3 (IntervalRat.scale (323 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-5063906232 / 1000000000000) (-5063906225 / 1000000000000), orderedInterval (44354700148 / 1000000000000) (44354700155 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (941497911610699 / 4000000000000) 3 (IntervalRat.scale (323 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-26733912586 / 1000000000000) (-26733912585 / 1000000000000), orderedInterval (-44552750381 / 1000000000000) (-44552750380 / 1000000000000)))) (orderedInterval (13925294460 / 1000000000000) (13925294513 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate287_chunkChecks3_1 :
    compactCertificate287.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1444499913464677 / 4000000000000) 3 (IntervalRat.scale (323 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-24630074271 / 1000000000000) (-24630074270 / 1000000000000), orderedInterval (-33969417612 / 1000000000000) (-33969417611 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (833982413883133 / 4000000000000) 3 (IntervalRat.scale (323 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (51627351167 / 1000000000000) (51627357360 / 1000000000000), orderedInterval (-19821688470 / 1000000000000) (-19821682277 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1479916428428897 / 4000000000000) 3 (IntervalRat.scale (323 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (2331436393 / 1000000000000) (2331436394 / 1000000000000), orderedInterval (41412511828 / 1000000000000) (41412511829 / 1000000000000)))) (orderedInterval (-134916378029 / 1000000000000) (-134916376410 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1382729897148293 / 4000000000000) 3 (IntervalRat.scale (323 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (33409969455 / 1000000000000) (33409969456 / 1000000000000), orderedInterval (26885021773 / 1000000000000) (26885021774 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (986781299646869 / 4000000000000) 3 (IntervalRat.scale (323 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (32943097134 / 1000000000000) (32943115421 / 1000000000000), orderedInterval (-38736451800 / 1000000000000) (-38736433512 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1118904821689251 / 4000000000000) 3 (IntervalRat.scale (323 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-37646811849 / 1000000000000) (-37646811848 / 1000000000000), orderedInterval (-29234314380 / 1000000000000) (-29234314379 / 1000000000000)))) (orderedInterval (17077738767 / 1000000000000) (17077745044 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (932826188632819 / 4000000000000) 3 (IntervalRat.scale (323 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (52162362752 / 1000000000000) (52162362790 / 1000000000000), orderedInterval (2877385340 / 1000000000000) (2877385377 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (824180227437199 / 4000000000000) 3 (IntervalRat.scale (323 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-27390500146 / 1000000000000) (-27390496893 / 1000000000000), orderedInterval (48434602636 / 1000000000000) (48434605890 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (238879553878701 / 800000000000) 3 (IntervalRat.scale (323 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-37099747947 / 1000000000000) (-37099747946 / 1000000000000), orderedInterval (-27426549931 / 1000000000000) (-27426549930 / 1000000000000)))) (orderedInterval (10097500654 / 1000000000000) (10097501096 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate287_chunkChecks3_2 :
    compactCertificate287.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (660753417570647 / 4000000000000) 3 (IntervalRat.scale (323 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (31459085324 / 1000000000000) (31459090145 / 1000000000000), orderedInterval (-53613786811 / 1000000000000) (-53613781990 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (560127989718367 / 4000000000000) 3 (IntervalRat.scale (323 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (35539019950 / 1000000000000) (35539026986 / 1000000000000), orderedInterval (-57426424055 / 1000000000000) (-57426417019 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (350502088389301 / 4000000000000) 3 (IntervalRat.scale (323 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (36682622533 / 1000000000000) (36682622534 / 1000000000000), orderedInterval (76730226407 / 1000000000000) (76730226408 / 1000000000000)))) (orderedInterval (-11729870127 / 1000000000000) (-11729869000 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (188501188853067 / 4000000000000) 3 (IntervalRat.scale (323 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-82081381681 / 1000000000000) (-82081381680 / 1000000000000), orderedInterval (-81419774105 / 1000000000000) (-81419774104 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (511817396440201 / 4000000000000) 3 (IntervalRat.scale (323 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (4689187141 / 1000000000000) (4689187156 / 1000000000000), orderedInterval (-70398829186 / 1000000000000) (-70398829171 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (698842898223977 / 4000000000000) 3 (IntervalRat.scale (323 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-25371367550 / 1000000000000) (-25371365989 / 1000000000000), orderedInterval (54846269435 / 1000000000000) (54846270996 / 1000000000000)))) (orderedInterval (4504138930 / 1000000000000) (4504139101 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (295497911610699 / 4000000000000) 3 (IntervalRat.scale (323 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-62596813268 / 1000000000000) (-62596758164 / 1000000000000), orderedInterval (68974678866 / 1000000000000) (68974733970 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1201182605143979 / 4000000000000) 3 (IntervalRat.scale (323 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-22568050394 / 1000000000000) (-22568048539 / 1000000000000), orderedInterval (40170620692 / 1000000000000) (40170622547 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (802334312553061 / 4000000000000) 3 (IntervalRat.scale (323 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (16994004134 / 1000000000000) (16994004135 / 1000000000000), orderedInterval (53670298808 / 1000000000000) (53670298809 / 1000000000000)))) (orderedInterval (40281945074 / 1000000000000) (40281946224 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate287_chunkChecks3 :
    compactCertificate287.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate287.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate287_chunkChecks3_0
    compactCertificate287_chunkChecks3_1 compactCertificate287_chunkChecks3_2

theorem compactCertificate287_chunkChecks4_0 :
    compactCertificate287.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (323 / 2) 4 (IntervalRat.scale (323 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-55319789228 / 1000000000000) (-55319771738 / 1000000000000), orderedInterval (29863504362 / 1000000000000) (29863521851 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (475840676172023 / 4000000000000) 4 (IntervalRat.scale (323 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (26043579264 / 1000000000000) (26043579265 / 1000000000000), orderedInterval (68252110175 / 1000000000000) (68252110176 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (153877097910359 / 800000000000) 4 (IntervalRat.scale (323 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-57360689220 / 1000000000000) (-57360689199 / 1000000000000), orderedInterval (-4266477750 / 1000000000000) (-4266477730 / 1000000000000)))) (orderedInterval (-28480505257 / 1000000000000) (-28480498216 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (138849122543461 / 4000000000000) 4 (IntervalRat.scale (323 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-109082419635 / 1000000000000) (-109082419634 / 1000000000000), orderedInterval (-78680945693 / 1000000000000) (-78680945692 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (372968273896417 / 4000000000000) 4 (IntervalRat.scale (323 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-18165340793 / 1000000000000) (-18165340609 / 1000000000000), orderedInterval (80705790095 / 1000000000000) (80705790279 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1012681416290589 / 4000000000000) 4 (IntervalRat.scale (323 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (24643749419 / 1000000000000) (24643751883 / 1000000000000), orderedInterval (-43721072274 / 1000000000000) (-43721069810 / 1000000000000)))) (orderedInterval (-10494984816 / 1000000000000) (-10494983678 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (745936547793157 / 4000000000000) 4 (IntervalRat.scale (323 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-55002542100 / 1000000000000) (-55002537647 / 1000000000000), orderedInterval (19858185188 / 1000000000000) (19858189641 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1278174988724761 / 4000000000000) 4 (IntervalRat.scale (323 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-5063906232 / 1000000000000) (-5063906225 / 1000000000000), orderedInterval (44354700148 / 1000000000000) (44354700155 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (941497911610699 / 4000000000000) 4 (IntervalRat.scale (323 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-26733912586 / 1000000000000) (-26733912585 / 1000000000000), orderedInterval (-44552750381 / 1000000000000) (-44552750380 / 1000000000000)))) (orderedInterval (-693704157 / 1000000000000) (-693704058 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate287_chunkChecks4_1 :
    compactCertificate287.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1444499913464677 / 4000000000000) 4 (IntervalRat.scale (323 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-24630074271 / 1000000000000) (-24630074270 / 1000000000000), orderedInterval (-33969417612 / 1000000000000) (-33969417611 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (833982413883133 / 4000000000000) 4 (IntervalRat.scale (323 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (51627351167 / 1000000000000) (51627357360 / 1000000000000), orderedInterval (-19821688470 / 1000000000000) (-19821682277 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1479916428428897 / 4000000000000) 4 (IntervalRat.scale (323 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (2331436393 / 1000000000000) (2331436394 / 1000000000000), orderedInterval (41412511828 / 1000000000000) (41412511829 / 1000000000000)))) (orderedInterval (130835410417 / 1000000000000) (130835413096 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1382729897148293 / 4000000000000) 4 (IntervalRat.scale (323 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (33409969455 / 1000000000000) (33409969456 / 1000000000000), orderedInterval (26885021773 / 1000000000000) (26885021774 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (986781299646869 / 4000000000000) 4 (IntervalRat.scale (323 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (32943097134 / 1000000000000) (32943115421 / 1000000000000), orderedInterval (-38736451800 / 1000000000000) (-38736433512 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1118904821689251 / 4000000000000) 4 (IntervalRat.scale (323 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-37646811849 / 1000000000000) (-37646811848 / 1000000000000), orderedInterval (-29234314380 / 1000000000000) (-29234314379 / 1000000000000)))) (orderedInterval (5803065328 / 1000000000000) (5803074972 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (932826188632819 / 4000000000000) 4 (IntervalRat.scale (323 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (52162362752 / 1000000000000) (52162362790 / 1000000000000), orderedInterval (2877385340 / 1000000000000) (2877385377 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (824180227437199 / 4000000000000) 4 (IntervalRat.scale (323 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-27390500146 / 1000000000000) (-27390496893 / 1000000000000), orderedInterval (48434602636 / 1000000000000) (48434605890 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (238879553878701 / 800000000000) 4 (IntervalRat.scale (323 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-37099747947 / 1000000000000) (-37099747946 / 1000000000000), orderedInterval (-27426549931 / 1000000000000) (-27426549930 / 1000000000000)))) (orderedInterval (-4453710075 / 1000000000000) (-4453709493 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate287_chunkChecks4_2 :
    compactCertificate287.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (660753417570647 / 4000000000000) 4 (IntervalRat.scale (323 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (31459085324 / 1000000000000) (31459090145 / 1000000000000), orderedInterval (-53613786811 / 1000000000000) (-53613781990 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (560127989718367 / 4000000000000) 4 (IntervalRat.scale (323 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (35539019950 / 1000000000000) (35539026986 / 1000000000000), orderedInterval (-57426424055 / 1000000000000) (-57426417019 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (350502088389301 / 4000000000000) 4 (IntervalRat.scale (323 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (36682622533 / 1000000000000) (36682622534 / 1000000000000), orderedInterval (76730226407 / 1000000000000) (76730226408 / 1000000000000)))) (orderedInterval (-6393515219 / 1000000000000) (-6393514102 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (188501188853067 / 4000000000000) 4 (IntervalRat.scale (323 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-82081381681 / 1000000000000) (-82081381680 / 1000000000000), orderedInterval (-81419774105 / 1000000000000) (-81419774104 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (511817396440201 / 4000000000000) 4 (IntervalRat.scale (323 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (4689187141 / 1000000000000) (4689187156 / 1000000000000), orderedInterval (-70398829186 / 1000000000000) (-70398829171 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (698842898223977 / 4000000000000) 4 (IntervalRat.scale (323 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-25371367550 / 1000000000000) (-25371365989 / 1000000000000), orderedInterval (54846269435 / 1000000000000) (54846270996 / 1000000000000)))) (orderedInterval (2576263740 / 1000000000000) (2576263925 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (295497911610699 / 4000000000000) 4 (IntervalRat.scale (323 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-62596813268 / 1000000000000) (-62596758164 / 1000000000000), orderedInterval (68974678866 / 1000000000000) (68974733970 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1201182605143979 / 4000000000000) 4 (IntervalRat.scale (323 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-22568050394 / 1000000000000) (-22568048539 / 1000000000000), orderedInterval (40170620692 / 1000000000000) (40170622547 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (802334312553061 / 4000000000000) 4 (IntervalRat.scale (323 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (16994004134 / 1000000000000) (16994004135 / 1000000000000), orderedInterval (53670298808 / 1000000000000) (53670298809 / 1000000000000)))) (orderedInterval (13857473293 / 1000000000000) (13857475356 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate287_chunkChecks4 :
    compactCertificate287.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate287.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate287_chunkChecks4_0
    compactCertificate287_chunkChecks4_1 compactCertificate287_chunkChecks4_2

theorem compactCertificate287_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate287.chunkCheck r b = true :=
  compactCertificate287.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate287_chunkChecks0
    · exact compactCertificate287_chunkChecks1
    · exact compactCertificate287_chunkChecks2
    · exact compactCertificate287_chunkChecks3
    · exact compactCertificate287_chunkChecks4)

theorem compactCertificate287_coefficient0 :
    compactCertificate287.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate287_coefficient1 :
    compactCertificate287.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate287_coefficient2 :
    compactCertificate287.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate287_coefficient3 :
    compactCertificate287.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate287_coefficient4 :
    compactCertificate287.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate287_coefficients : ∀ r : Fin 5,
    compactCertificate287.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate287_coefficient0
  · exact compactCertificate287_coefficient1
  · exact compactCertificate287_coefficient2
  · exact compactCertificate287_coefficient3
  · exact compactCertificate287_coefficient4

theorem compactCertificate287_lower : (1 : ℚ) ≤ compactCertificate287.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate287, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate287_proves {t : ℝ} (ht : t ∈ compactCertificate287.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate287.proves compactCertificate287_states compactCertificate287_chunks
    compactCertificate287_coefficients compactCertificate287_lower ht

end Erdos232
