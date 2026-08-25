/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate407 : CompactCertificate where
  left := 278
  right := 279
  center := 557 / 2
  grid := fun i =>
    match i.val with
    | 0 => 89
    | 1 => 65
    | 2 => 106
    | 3 => 19
    | 4 => 51
    | 5 => 139
    | 6 => 102
    | 7 => 175
    | 8 => 129
    | 9 => 198
    | 10 => 115
    | 11 => 203
    | 12 => 190
    | 13 => 135
    | 14 => 154
    | 15 => 128
    | 16 => 113
    | 17 => 164
    | 18 => 91
    | 19 => 77
    | 20 => 48
    | 21 => 26
    | 22 => 70
    | 23 => 96
    | 24 => 41
    | 25 => 165
    | _ => 110
  point := fun i =>
    match i.val with
    | 0 => 557 / 2
    | 1 => 820567357980857 / 4000000000000
    | 2 => 265354623950681 / 800000000000
    | 3 => 239439508534699 / 4000000000000
    | 4 => 643168199877103 / 4000000000000
    | 5 => 1746326776699251 / 4000000000000
    | 6 => 1286336399754763 / 4000000000000
    | 7 => 2204159345881399 / 4000000000000
    | 8 => 1623573798040741 / 4000000000000
    | 9 => 2490979726934443 / 4000000000000
    | 10 => 1438167815891347 / 4000000000000
    | 11 => 2552054026733423 / 4000000000000
    | 12 => 2384459915515787 / 4000000000000
    | 13 => 1701663108059771 / 4000000000000
    | 14 => 1929504599631309 / 4000000000000
    | 15 => 1608619774205821 / 4000000000000
    | 16 => 1421264355054241 / 4000000000000
    | 17 => 411937806533859 / 800000000000
    | 18 => 1139441651971673 / 4000000000000
    | 19 => 965917307347153 / 4000000000000
    | 20 => 604426201959259 / 4000000000000
    | 21 => 325062421644453 / 4000000000000
    | 22 => 882607708412359 / 4000000000000
    | 23 => 1205125369383143 / 4000000000000
    | 24 => 509573798040741 / 4000000000000
    | 25 => 2071389198344261 / 4000000000000
    | _ => 1383591987901099 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (14894268231 / 1000000000000) (14894268421 / 1000000000000), orderedInterval (-45458574949 / 1000000000000) (-45458574759 / 1000000000000))
    | 1 => (orderedInterval (-55062417488 / 1000000000000) (-55062416940 / 1000000000000), orderedInterval (8586218414 / 1000000000000) (8586218962 / 1000000000000))
    | 2 => (orderedInterval (-22166979968 / 1000000000000) (-22166978063 / 1000000000000), orderedInterval (37821357631 / 1000000000000) (37821359536 / 1000000000000))
    | 3 => (orderedInterval (-84058811450 / 1000000000000) (-84058811449 / 1000000000000), orderedInterval (-59040374617 / 1000000000000) (-59040374616 / 1000000000000))
    | 4 => (orderedInterval (-61469189626 / 1000000000000) (-61469189624 / 1000000000000), orderedInterval (-13254869970 / 1000000000000) (-13254869968 / 1000000000000))
    | 5 => (orderedInterval (-24172048225 / 1000000000000) (-24172048224 / 1000000000000), orderedInterval (-29534182452 / 1000000000000) (-29534182451 / 1000000000000))
    | 6 => (orderedInterval (41705426286 / 1000000000000) (41705436421 / 1000000000000), orderedInterval (-15566207705 / 1000000000000) (-15566197570 / 1000000000000))
    | 7 => (orderedInterval (-30219184226 / 1000000000000) (-30219096339 / 1000000000000), orderedInterval (15587242590 / 1000000000000) (15587330477 / 1000000000000))
    | 8 => (orderedInterval (-39112036375 / 1000000000000) (-39112036344 / 1000000000000), orderedInterval (-6171795590 / 1000000000000) (-6171795559 / 1000000000000))
    | 9 => (orderedInterval (31880786012 / 1000000000000) (31880786455 / 1000000000000), orderedInterval (2402422010 / 1000000000000) (2402422453 / 1000000000000))
    | 10 => (orderedInterval (34377530427 / 1000000000000) (34377632826 / 1000000000000), orderedInterval (-24313518698 / 1000000000000) (-24313416298 / 1000000000000))
    | 11 => (orderedInterval (-27484827450 / 1000000000000) (-27484827449 / 1000000000000), orderedInterval (-15547648548 / 1000000000000) (-15547648547 / 1000000000000))
    | 12 => (orderedInterval (-79634244 / 1000000000000) (-79634243 / 1000000000000), orderedInterval (32679448498 / 1000000000000) (32679448499 / 1000000000000))
    | 13 => (orderedInterval (-33665110208 / 1000000000000) (-33665038591 / 1000000000000), orderedInterval (19095423266 / 1000000000000) (19095494883 / 1000000000000))
    | 14 => (orderedInterval (-21810986692 / 1000000000000) (-21810983809 / 1000000000000), orderedInterval (29074957335 / 1000000000000) (29074960217 / 1000000000000))
    | 15 => (orderedInterval (28986092906 / 1000000000000) (28986092907 / 1000000000000), orderedInterval (27218823006 / 1000000000000) (27218823007 / 1000000000000))
    | 16 => (orderedInterval (-37745777701 / 1000000000000) (-37745777700 / 1000000000000), orderedInterval (-19102954878 / 1000000000000) (-19102954877 / 1000000000000))
    | 17 => (orderedInterval (16430538368 / 1000000000000) (16430538369 / 1000000000000), orderedInterval (31070686922 / 1000000000000) (31070686923 / 1000000000000))
    | 18 => (orderedInterval (11216942723 / 1000000000000) (11216942785 / 1000000000000), orderedInterval (-45943880549 / 1000000000000) (-45943880487 / 1000000000000))
    | 19 => (orderedInterval (-18163149206 / 1000000000000) (-18163149205 / 1000000000000), orderedInterval (-47987767080 / 1000000000000) (-47987767079 / 1000000000000))
    | 20 => (orderedInterval (57688728602 / 1000000000000) (57688728603 / 1000000000000), orderedInterval (29558893257 / 1000000000000) (29558893258 / 1000000000000))
    | 21 => (orderedInterval (31845429502 / 1000000000000) (31845429503 / 1000000000000), orderedInterval (82386118071 / 1000000000000) (82386118072 / 1000000000000))
    | 22 => (orderedInterval (53658122934 / 1000000000000) (53658122975 / 1000000000000), orderedInterval (2322800991 / 1000000000000) (2322801032 / 1000000000000))
    | 23 => (orderedInterval (20958668673 / 1000000000000) (20958668674 / 1000000000000), orderedInterval (40877033925 / 1000000000000) (40877033926 / 1000000000000))
    | 24 => (orderedInterval (41500487707 / 1000000000000) (41500503077 / 1000000000000), orderedInterval (-57390444566 / 1000000000000) (-57390429196 / 1000000000000))
    | 25 => (orderedInterval (-9340987945 / 1000000000000) (-9340987944 / 1000000000000), orderedInterval (-33786018103 / 1000000000000) (-33786018102 / 1000000000000))
    | _ => (orderedInterval (38384968597 / 1000000000000) (38384968598 / 1000000000000), orderedInterval (19103771837 / 1000000000000) (19103771838 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (4089707948 / 1000000000000) (4089708161 / 1000000000000)
      | 1 => orderedInterval (386013282 / 1000000000000) (386013316 / 1000000000000)
      | 2 => orderedInterval (-13182922 / 1000000000000) (-13180194 / 1000000000000)
      | 3 => orderedInterval (-7024868930 / 1000000000000) (-7024861154 / 1000000000000)
      | 4 => orderedInterval (-3071655537 / 1000000000000) (-3071648717 / 1000000000000)
      | 5 => orderedInterval (2915473933 / 1000000000000) (2915473961 / 1000000000000)
      | 6 => orderedInterval (1112601230 / 1000000000000) (1112601311 / 1000000000000)
      | 7 => orderedInterval (-3411612714 / 1000000000000) (-3411612679 / 1000000000000)
      | _ => orderedInterval (-6191486816 / 1000000000000) (-6191486646 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-15315950932 / 1000000000000) (-15315950697 / 1000000000000)
      | 1 => orderedInterval (3149594621 / 1000000000000) (3149594659 / 1000000000000)
      | 2 => orderedInterval (-1168652240 / 1000000000000) (-1168646847 / 1000000000000)
      | 3 => orderedInterval (-8343481269 / 1000000000000) (-8343471069 / 1000000000000)
      | 4 => orderedInterval (1240642973 / 1000000000000) (1240653398 / 1000000000000)
      | 5 => orderedInterval (3319465977 / 1000000000000) (3319466016 / 1000000000000)
      | 6 => orderedInterval (10391023289 / 1000000000000) (10391023364 / 1000000000000)
      | 7 => orderedInterval (-3874684532 / 1000000000000) (-3874684500 / 1000000000000)
      | _ => orderedInterval (503782077 / 1000000000000) (503782229 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-3725057346 / 1000000000000) (-3725057083 / 1000000000000)
      | 1 => orderedInterval (-3528123821 / 1000000000000) (-3528123768 / 1000000000000)
      | 2 => orderedInterval (-1636940795 / 1000000000000) (-1636930113 / 1000000000000)
      | 3 => orderedInterval (44614297793 / 1000000000000) (44614311358 / 1000000000000)
      | 4 => orderedInterval (7085909367 / 1000000000000) (7085925340 / 1000000000000)
      | 5 => orderedInterval (-5663950423 / 1000000000000) (-5663950365 / 1000000000000)
      | 6 => orderedInterval (513284330 / 1000000000000) (513284403 / 1000000000000)
      | 7 => orderedInterval (2707903766 / 1000000000000) (2707903797 / 1000000000000)
      | _ => orderedInterval (8426578577 / 1000000000000) (8426578758 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (14249918457 / 1000000000000) (14249918754 / 1000000000000)
      | 1 => orderedInterval (-7988720348 / 1000000000000) (-7988720269 / 1000000000000)
      | 2 => orderedInterval (4191651226 / 1000000000000) (4191672352 / 1000000000000)
      | 3 => orderedInterval (35061607604 / 1000000000000) (35061625932 / 1000000000000)
      | 4 => orderedInterval (88600841 / 1000000000000) (88625263 / 1000000000000)
      | 5 => orderedInterval (-8224365169 / 1000000000000) (-8224365080 / 1000000000000)
      | 6 => orderedInterval (-9786946741 / 1000000000000) (-9786946670 / 1000000000000)
      | 7 => orderedInterval (4020385383 / 1000000000000) (4020385415 / 1000000000000)
      | _ => orderedInterval (-10810642744 / 1000000000000) (-10810642487 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (3032859418 / 1000000000000) (3032859756 / 1000000000000)
      | 1 => orderedInterval (10187119288 / 1000000000000) (10187119410 / 1000000000000)
      | 2 => orderedInterval (9990176665 / 1000000000000) (9990218528 / 1000000000000)
      | 3 => orderedInterval (-242412661771 / 1000000000000) (-242412636215 / 1000000000000)
      | 4 => orderedInterval (-16309205157 / 1000000000000) (-16309167718 / 1000000000000)
      | 5 => orderedInterval (12153472025 / 1000000000000) (12153472166 / 1000000000000)
      | 6 => orderedInterval (-1148928697 / 1000000000000) (-1148928627 / 1000000000000)
      | 7 => orderedInterval (-2712656773 / 1000000000000) (-2712656740 / 1000000000000)
      | _ => orderedInterval (-7959429463 / 1000000000000) (-7959429061 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-11209010526 / 1000000000000) (-11208992641 / 1000000000000)
    | 1 => orderedInterval (-10098260036 / 1000000000000) (-10098233447 / 1000000000000)
    | 2 => orderedInterval (48793901448 / 1000000000000) (48793942327 / 1000000000000)
    | 3 => orderedInterval (20801488509 / 1000000000000) (20801553210 / 1000000000000)
    | _ => orderedInterval (-235179254465 / 1000000000000) (-235179148501 / 1000000000000)

theorem compactCertificate407_stateChecks0 :
    compactCertificate407.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 89 12 (557 / 2)) (orderedInterval (14894268231 / 1000000000000) (14894268421 / 1000000000000), orderedInterval (-45458574949 / 1000000000000) (-45458574759 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 65 12 (820567357980857 / 4000000000000)) (orderedInterval (-55062417488 / 1000000000000) (-55062416940 / 1000000000000), orderedInterval (8586218414 / 1000000000000) (8586218962 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 106 12 (265354623950681 / 800000000000)) (orderedInterval (-22166979968 / 1000000000000) (-22166978063 / 1000000000000), orderedInterval (37821357631 / 1000000000000) (37821359536 / 1000000000000))) = true
  rfl'

theorem compactCertificate407_stateChecks1 :
    compactCertificate407.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 19 12 (239439508534699 / 4000000000000)) (orderedInterval (-84058811450 / 1000000000000) (-84058811449 / 1000000000000), orderedInterval (-59040374617 / 1000000000000) (-59040374616 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (643168199877103 / 4000000000000)) (orderedInterval (-61469189626 / 1000000000000) (-61469189624 / 1000000000000), orderedInterval (-13254869970 / 1000000000000) (-13254869968 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 139 12 (1746326776699251 / 4000000000000)) (orderedInterval (-24172048225 / 1000000000000) (-24172048224 / 1000000000000), orderedInterval (-29534182452 / 1000000000000) (-29534182451 / 1000000000000))) = true
  rfl'

theorem compactCertificate407_stateChecks2 :
    compactCertificate407.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 102 12 (1286336399754763 / 4000000000000)) (orderedInterval (41705426286 / 1000000000000) (41705436421 / 1000000000000), orderedInterval (-15566207705 / 1000000000000) (-15566197570 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 175 12 (2204159345881399 / 4000000000000)) (orderedInterval (-30219184226 / 1000000000000) (-30219096339 / 1000000000000), orderedInterval (15587242590 / 1000000000000) (15587330477 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 129 12 (1623573798040741 / 4000000000000)) (orderedInterval (-39112036375 / 1000000000000) (-39112036344 / 1000000000000), orderedInterval (-6171795590 / 1000000000000) (-6171795559 / 1000000000000))) = true
  rfl'

theorem compactCertificate407_stateChecks3 :
    compactCertificate407.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 198 12 (2490979726934443 / 4000000000000)) (orderedInterval (31880786012 / 1000000000000) (31880786455 / 1000000000000), orderedInterval (2402422010 / 1000000000000) (2402422453 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 115 12 (1438167815891347 / 4000000000000)) (orderedInterval (34377530427 / 1000000000000) (34377632826 / 1000000000000), orderedInterval (-24313518698 / 1000000000000) (-24313416298 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 203 12 (2552054026733423 / 4000000000000)) (orderedInterval (-27484827450 / 1000000000000) (-27484827449 / 1000000000000), orderedInterval (-15547648548 / 1000000000000) (-15547648547 / 1000000000000))) = true
  rfl'

theorem compactCertificate407_stateChecks4 :
    compactCertificate407.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 190 12 (2384459915515787 / 4000000000000)) (orderedInterval (-79634244 / 1000000000000) (-79634243 / 1000000000000), orderedInterval (32679448498 / 1000000000000) (32679448499 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 135 12 (1701663108059771 / 4000000000000)) (orderedInterval (-33665110208 / 1000000000000) (-33665038591 / 1000000000000), orderedInterval (19095423266 / 1000000000000) (19095494883 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 154 12 (1929504599631309 / 4000000000000)) (orderedInterval (-21810986692 / 1000000000000) (-21810983809 / 1000000000000), orderedInterval (29074957335 / 1000000000000) (29074960217 / 1000000000000))) = true
  rfl'

theorem compactCertificate407_stateChecks5 :
    compactCertificate407.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 128 12 (1608619774205821 / 4000000000000)) (orderedInterval (28986092906 / 1000000000000) (28986092907 / 1000000000000), orderedInterval (27218823006 / 1000000000000) (27218823007 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 113 12 (1421264355054241 / 4000000000000)) (orderedInterval (-37745777701 / 1000000000000) (-37745777700 / 1000000000000), orderedInterval (-19102954878 / 1000000000000) (-19102954877 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 164 12 (411937806533859 / 800000000000)) (orderedInterval (16430538368 / 1000000000000) (16430538369 / 1000000000000), orderedInterval (31070686922 / 1000000000000) (31070686923 / 1000000000000))) = true
  rfl'

theorem compactCertificate407_stateChecks6 :
    compactCertificate407.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 91 12 (1139441651971673 / 4000000000000)) (orderedInterval (11216942723 / 1000000000000) (11216942785 / 1000000000000), orderedInterval (-45943880549 / 1000000000000) (-45943880487 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 77 12 (965917307347153 / 4000000000000)) (orderedInterval (-18163149206 / 1000000000000) (-18163149205 / 1000000000000), orderedInterval (-47987767080 / 1000000000000) (-47987767079 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 48 12 (604426201959259 / 4000000000000)) (orderedInterval (57688728602 / 1000000000000) (57688728603 / 1000000000000), orderedInterval (29558893257 / 1000000000000) (29558893258 / 1000000000000))) = true
  rfl'

theorem compactCertificate407_stateChecks7 :
    compactCertificate407.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 26 12 (325062421644453 / 4000000000000)) (orderedInterval (31845429502 / 1000000000000) (31845429503 / 1000000000000), orderedInterval (82386118071 / 1000000000000) (82386118072 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (882607708412359 / 4000000000000)) (orderedInterval (53658122934 / 1000000000000) (53658122975 / 1000000000000), orderedInterval (2322800991 / 1000000000000) (2322801032 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 96 12 (1205125369383143 / 4000000000000)) (orderedInterval (20958668673 / 1000000000000) (20958668674 / 1000000000000), orderedInterval (40877033925 / 1000000000000) (40877033926 / 1000000000000))) = true
  rfl'

theorem compactCertificate407_stateChecks8 :
    compactCertificate407.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 41 12 (509573798040741 / 4000000000000)) (orderedInterval (41500487707 / 1000000000000) (41500503077 / 1000000000000), orderedInterval (-57390444566 / 1000000000000) (-57390429196 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 165 12 (2071389198344261 / 4000000000000)) (orderedInterval (-9340987945 / 1000000000000) (-9340987944 / 1000000000000), orderedInterval (-33786018103 / 1000000000000) (-33786018102 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 110 12 (1383591987901099 / 4000000000000)) (orderedInterval (38384968597 / 1000000000000) (38384968598 / 1000000000000), orderedInterval (19103771837 / 1000000000000) (19103771838 / 1000000000000))) = true
  rfl'

theorem compactCertificate407_states : ∀ j,
    BesselStateValid (compactCertificate407.point j) (compactCertificate407.state j) :=
  compactCertificate407.statesValid_of_checks3 compactCertificate407_stateChecks0
    compactCertificate407_stateChecks1 compactCertificate407_stateChecks2
    compactCertificate407_stateChecks3 compactCertificate407_stateChecks4
    compactCertificate407_stateChecks5 compactCertificate407_stateChecks6
    compactCertificate407_stateChecks7 compactCertificate407_stateChecks8

theorem compactCertificate407_chunkChecks0_0 :
    compactCertificate407.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (557 / 2) 0 (IntervalRat.scale (557 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (14894268231 / 1000000000000) (14894268421 / 1000000000000), orderedInterval (-45458574949 / 1000000000000) (-45458574759 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (820567357980857 / 4000000000000) 0 (IntervalRat.scale (557 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-55062417488 / 1000000000000) (-55062416940 / 1000000000000), orderedInterval (8586218414 / 1000000000000) (8586218962 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (265354623950681 / 800000000000) 0 (IntervalRat.scale (557 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-22166979968 / 1000000000000) (-22166978063 / 1000000000000), orderedInterval (37821357631 / 1000000000000) (37821359536 / 1000000000000)))) (orderedInterval (4089707948 / 1000000000000) (4089708161 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (239439508534699 / 4000000000000) 0 (IntervalRat.scale (557 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-84058811450 / 1000000000000) (-84058811449 / 1000000000000), orderedInterval (-59040374617 / 1000000000000) (-59040374616 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (643168199877103 / 4000000000000) 0 (IntervalRat.scale (557 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-61469189626 / 1000000000000) (-61469189624 / 1000000000000), orderedInterval (-13254869970 / 1000000000000) (-13254869968 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1746326776699251 / 4000000000000) 0 (IntervalRat.scale (557 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-24172048225 / 1000000000000) (-24172048224 / 1000000000000), orderedInterval (-29534182452 / 1000000000000) (-29534182451 / 1000000000000)))) (orderedInterval (386013282 / 1000000000000) (386013316 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1286336399754763 / 4000000000000) 0 (IntervalRat.scale (557 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (41705426286 / 1000000000000) (41705436421 / 1000000000000), orderedInterval (-15566207705 / 1000000000000) (-15566197570 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2204159345881399 / 4000000000000) 0 (IntervalRat.scale (557 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-30219184226 / 1000000000000) (-30219096339 / 1000000000000), orderedInterval (15587242590 / 1000000000000) (15587330477 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1623573798040741 / 4000000000000) 0 (IntervalRat.scale (557 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-39112036375 / 1000000000000) (-39112036344 / 1000000000000), orderedInterval (-6171795590 / 1000000000000) (-6171795559 / 1000000000000)))) (orderedInterval (-13182922 / 1000000000000) (-13180194 / 1000000000000))) = true
  rfl'

theorem compactCertificate407_chunkChecks0_1 :
    compactCertificate407.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2490979726934443 / 4000000000000) 0 (IntervalRat.scale (557 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (31880786012 / 1000000000000) (31880786455 / 1000000000000), orderedInterval (2402422010 / 1000000000000) (2402422453 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1438167815891347 / 4000000000000) 0 (IntervalRat.scale (557 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (34377530427 / 1000000000000) (34377632826 / 1000000000000), orderedInterval (-24313518698 / 1000000000000) (-24313416298 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2552054026733423 / 4000000000000) 0 (IntervalRat.scale (557 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-27484827450 / 1000000000000) (-27484827449 / 1000000000000), orderedInterval (-15547648548 / 1000000000000) (-15547648547 / 1000000000000)))) (orderedInterval (-7024868930 / 1000000000000) (-7024861154 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2384459915515787 / 4000000000000) 0 (IntervalRat.scale (557 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-79634244 / 1000000000000) (-79634243 / 1000000000000), orderedInterval (32679448498 / 1000000000000) (32679448499 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1701663108059771 / 4000000000000) 0 (IntervalRat.scale (557 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-33665110208 / 1000000000000) (-33665038591 / 1000000000000), orderedInterval (19095423266 / 1000000000000) (19095494883 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1929504599631309 / 4000000000000) 0 (IntervalRat.scale (557 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-21810986692 / 1000000000000) (-21810983809 / 1000000000000), orderedInterval (29074957335 / 1000000000000) (29074960217 / 1000000000000)))) (orderedInterval (-3071655537 / 1000000000000) (-3071648717 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1608619774205821 / 4000000000000) 0 (IntervalRat.scale (557 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (28986092906 / 1000000000000) (28986092907 / 1000000000000), orderedInterval (27218823006 / 1000000000000) (27218823007 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1421264355054241 / 4000000000000) 0 (IntervalRat.scale (557 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-37745777701 / 1000000000000) (-37745777700 / 1000000000000), orderedInterval (-19102954878 / 1000000000000) (-19102954877 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (411937806533859 / 800000000000) 0 (IntervalRat.scale (557 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16430538368 / 1000000000000) (16430538369 / 1000000000000), orderedInterval (31070686922 / 1000000000000) (31070686923 / 1000000000000)))) (orderedInterval (2915473933 / 1000000000000) (2915473961 / 1000000000000))) = true
  rfl'

theorem compactCertificate407_chunkChecks0_2 :
    compactCertificate407.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1139441651971673 / 4000000000000) 0 (IntervalRat.scale (557 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (11216942723 / 1000000000000) (11216942785 / 1000000000000), orderedInterval (-45943880549 / 1000000000000) (-45943880487 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (965917307347153 / 4000000000000) 0 (IntervalRat.scale (557 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-18163149206 / 1000000000000) (-18163149205 / 1000000000000), orderedInterval (-47987767080 / 1000000000000) (-47987767079 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (604426201959259 / 4000000000000) 0 (IntervalRat.scale (557 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (57688728602 / 1000000000000) (57688728603 / 1000000000000), orderedInterval (29558893257 / 1000000000000) (29558893258 / 1000000000000)))) (orderedInterval (1112601230 / 1000000000000) (1112601311 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (325062421644453 / 4000000000000) 0 (IntervalRat.scale (557 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (31845429502 / 1000000000000) (31845429503 / 1000000000000), orderedInterval (82386118071 / 1000000000000) (82386118072 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (882607708412359 / 4000000000000) 0 (IntervalRat.scale (557 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (53658122934 / 1000000000000) (53658122975 / 1000000000000), orderedInterval (2322800991 / 1000000000000) (2322801032 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1205125369383143 / 4000000000000) 0 (IntervalRat.scale (557 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (20958668673 / 1000000000000) (20958668674 / 1000000000000), orderedInterval (40877033925 / 1000000000000) (40877033926 / 1000000000000)))) (orderedInterval (-3411612714 / 1000000000000) (-3411612679 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (509573798040741 / 4000000000000) 0 (IntervalRat.scale (557 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (41500487707 / 1000000000000) (41500503077 / 1000000000000), orderedInterval (-57390444566 / 1000000000000) (-57390429196 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2071389198344261 / 4000000000000) 0 (IntervalRat.scale (557 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-9340987945 / 1000000000000) (-9340987944 / 1000000000000), orderedInterval (-33786018103 / 1000000000000) (-33786018102 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1383591987901099 / 4000000000000) 0 (IntervalRat.scale (557 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (38384968597 / 1000000000000) (38384968598 / 1000000000000), orderedInterval (19103771837 / 1000000000000) (19103771838 / 1000000000000)))) (orderedInterval (-6191486816 / 1000000000000) (-6191486646 / 1000000000000))) = true
  rfl'

theorem compactCertificate407_chunkChecks0 :
    compactCertificate407.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate407.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate407_chunkChecks0_0
    compactCertificate407_chunkChecks0_1 compactCertificate407_chunkChecks0_2

theorem compactCertificate407_chunkChecks1_0 :
    compactCertificate407.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (557 / 2) 1 (IntervalRat.scale (557 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (14894268231 / 1000000000000) (14894268421 / 1000000000000), orderedInterval (-45458574949 / 1000000000000) (-45458574759 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (820567357980857 / 4000000000000) 1 (IntervalRat.scale (557 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-55062417488 / 1000000000000) (-55062416940 / 1000000000000), orderedInterval (8586218414 / 1000000000000) (8586218962 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (265354623950681 / 800000000000) 1 (IntervalRat.scale (557 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-22166979968 / 1000000000000) (-22166978063 / 1000000000000), orderedInterval (37821357631 / 1000000000000) (37821359536 / 1000000000000)))) (orderedInterval (-15315950932 / 1000000000000) (-15315950697 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (239439508534699 / 4000000000000) 1 (IntervalRat.scale (557 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-84058811450 / 1000000000000) (-84058811449 / 1000000000000), orderedInterval (-59040374617 / 1000000000000) (-59040374616 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (643168199877103 / 4000000000000) 1 (IntervalRat.scale (557 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-61469189626 / 1000000000000) (-61469189624 / 1000000000000), orderedInterval (-13254869970 / 1000000000000) (-13254869968 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1746326776699251 / 4000000000000) 1 (IntervalRat.scale (557 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-24172048225 / 1000000000000) (-24172048224 / 1000000000000), orderedInterval (-29534182452 / 1000000000000) (-29534182451 / 1000000000000)))) (orderedInterval (3149594621 / 1000000000000) (3149594659 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1286336399754763 / 4000000000000) 1 (IntervalRat.scale (557 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (41705426286 / 1000000000000) (41705436421 / 1000000000000), orderedInterval (-15566207705 / 1000000000000) (-15566197570 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2204159345881399 / 4000000000000) 1 (IntervalRat.scale (557 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-30219184226 / 1000000000000) (-30219096339 / 1000000000000), orderedInterval (15587242590 / 1000000000000) (15587330477 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1623573798040741 / 4000000000000) 1 (IntervalRat.scale (557 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-39112036375 / 1000000000000) (-39112036344 / 1000000000000), orderedInterval (-6171795590 / 1000000000000) (-6171795559 / 1000000000000)))) (orderedInterval (-1168652240 / 1000000000000) (-1168646847 / 1000000000000))) = true
  rfl'

theorem compactCertificate407_chunkChecks1_1 :
    compactCertificate407.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2490979726934443 / 4000000000000) 1 (IntervalRat.scale (557 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (31880786012 / 1000000000000) (31880786455 / 1000000000000), orderedInterval (2402422010 / 1000000000000) (2402422453 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1438167815891347 / 4000000000000) 1 (IntervalRat.scale (557 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (34377530427 / 1000000000000) (34377632826 / 1000000000000), orderedInterval (-24313518698 / 1000000000000) (-24313416298 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2552054026733423 / 4000000000000) 1 (IntervalRat.scale (557 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-27484827450 / 1000000000000) (-27484827449 / 1000000000000), orderedInterval (-15547648548 / 1000000000000) (-15547648547 / 1000000000000)))) (orderedInterval (-8343481269 / 1000000000000) (-8343471069 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2384459915515787 / 4000000000000) 1 (IntervalRat.scale (557 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-79634244 / 1000000000000) (-79634243 / 1000000000000), orderedInterval (32679448498 / 1000000000000) (32679448499 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1701663108059771 / 4000000000000) 1 (IntervalRat.scale (557 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-33665110208 / 1000000000000) (-33665038591 / 1000000000000), orderedInterval (19095423266 / 1000000000000) (19095494883 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1929504599631309 / 4000000000000) 1 (IntervalRat.scale (557 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-21810986692 / 1000000000000) (-21810983809 / 1000000000000), orderedInterval (29074957335 / 1000000000000) (29074960217 / 1000000000000)))) (orderedInterval (1240642973 / 1000000000000) (1240653398 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1608619774205821 / 4000000000000) 1 (IntervalRat.scale (557 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (28986092906 / 1000000000000) (28986092907 / 1000000000000), orderedInterval (27218823006 / 1000000000000) (27218823007 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1421264355054241 / 4000000000000) 1 (IntervalRat.scale (557 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-37745777701 / 1000000000000) (-37745777700 / 1000000000000), orderedInterval (-19102954878 / 1000000000000) (-19102954877 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (411937806533859 / 800000000000) 1 (IntervalRat.scale (557 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16430538368 / 1000000000000) (16430538369 / 1000000000000), orderedInterval (31070686922 / 1000000000000) (31070686923 / 1000000000000)))) (orderedInterval (3319465977 / 1000000000000) (3319466016 / 1000000000000))) = true
  rfl'

theorem compactCertificate407_chunkChecks1_2 :
    compactCertificate407.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1139441651971673 / 4000000000000) 1 (IntervalRat.scale (557 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (11216942723 / 1000000000000) (11216942785 / 1000000000000), orderedInterval (-45943880549 / 1000000000000) (-45943880487 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (965917307347153 / 4000000000000) 1 (IntervalRat.scale (557 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-18163149206 / 1000000000000) (-18163149205 / 1000000000000), orderedInterval (-47987767080 / 1000000000000) (-47987767079 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (604426201959259 / 4000000000000) 1 (IntervalRat.scale (557 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (57688728602 / 1000000000000) (57688728603 / 1000000000000), orderedInterval (29558893257 / 1000000000000) (29558893258 / 1000000000000)))) (orderedInterval (10391023289 / 1000000000000) (10391023364 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (325062421644453 / 4000000000000) 1 (IntervalRat.scale (557 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (31845429502 / 1000000000000) (31845429503 / 1000000000000), orderedInterval (82386118071 / 1000000000000) (82386118072 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (882607708412359 / 4000000000000) 1 (IntervalRat.scale (557 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (53658122934 / 1000000000000) (53658122975 / 1000000000000), orderedInterval (2322800991 / 1000000000000) (2322801032 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1205125369383143 / 4000000000000) 1 (IntervalRat.scale (557 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (20958668673 / 1000000000000) (20958668674 / 1000000000000), orderedInterval (40877033925 / 1000000000000) (40877033926 / 1000000000000)))) (orderedInterval (-3874684532 / 1000000000000) (-3874684500 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (509573798040741 / 4000000000000) 1 (IntervalRat.scale (557 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (41500487707 / 1000000000000) (41500503077 / 1000000000000), orderedInterval (-57390444566 / 1000000000000) (-57390429196 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2071389198344261 / 4000000000000) 1 (IntervalRat.scale (557 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-9340987945 / 1000000000000) (-9340987944 / 1000000000000), orderedInterval (-33786018103 / 1000000000000) (-33786018102 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1383591987901099 / 4000000000000) 1 (IntervalRat.scale (557 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (38384968597 / 1000000000000) (38384968598 / 1000000000000), orderedInterval (19103771837 / 1000000000000) (19103771838 / 1000000000000)))) (orderedInterval (503782077 / 1000000000000) (503782229 / 1000000000000))) = true
  rfl'

theorem compactCertificate407_chunkChecks1 :
    compactCertificate407.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate407.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate407_chunkChecks1_0
    compactCertificate407_chunkChecks1_1 compactCertificate407_chunkChecks1_2

theorem compactCertificate407_chunkChecks2_0 :
    compactCertificate407.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (557 / 2) 2 (IntervalRat.scale (557 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (14894268231 / 1000000000000) (14894268421 / 1000000000000), orderedInterval (-45458574949 / 1000000000000) (-45458574759 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (820567357980857 / 4000000000000) 2 (IntervalRat.scale (557 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-55062417488 / 1000000000000) (-55062416940 / 1000000000000), orderedInterval (8586218414 / 1000000000000) (8586218962 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (265354623950681 / 800000000000) 2 (IntervalRat.scale (557 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-22166979968 / 1000000000000) (-22166978063 / 1000000000000), orderedInterval (37821357631 / 1000000000000) (37821359536 / 1000000000000)))) (orderedInterval (-3725057346 / 1000000000000) (-3725057083 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (239439508534699 / 4000000000000) 2 (IntervalRat.scale (557 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-84058811450 / 1000000000000) (-84058811449 / 1000000000000), orderedInterval (-59040374617 / 1000000000000) (-59040374616 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (643168199877103 / 4000000000000) 2 (IntervalRat.scale (557 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-61469189626 / 1000000000000) (-61469189624 / 1000000000000), orderedInterval (-13254869970 / 1000000000000) (-13254869968 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1746326776699251 / 4000000000000) 2 (IntervalRat.scale (557 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-24172048225 / 1000000000000) (-24172048224 / 1000000000000), orderedInterval (-29534182452 / 1000000000000) (-29534182451 / 1000000000000)))) (orderedInterval (-3528123821 / 1000000000000) (-3528123768 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1286336399754763 / 4000000000000) 2 (IntervalRat.scale (557 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (41705426286 / 1000000000000) (41705436421 / 1000000000000), orderedInterval (-15566207705 / 1000000000000) (-15566197570 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2204159345881399 / 4000000000000) 2 (IntervalRat.scale (557 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-30219184226 / 1000000000000) (-30219096339 / 1000000000000), orderedInterval (15587242590 / 1000000000000) (15587330477 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1623573798040741 / 4000000000000) 2 (IntervalRat.scale (557 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-39112036375 / 1000000000000) (-39112036344 / 1000000000000), orderedInterval (-6171795590 / 1000000000000) (-6171795559 / 1000000000000)))) (orderedInterval (-1636940795 / 1000000000000) (-1636930113 / 1000000000000))) = true
  rfl'

theorem compactCertificate407_chunkChecks2_1 :
    compactCertificate407.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2490979726934443 / 4000000000000) 2 (IntervalRat.scale (557 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (31880786012 / 1000000000000) (31880786455 / 1000000000000), orderedInterval (2402422010 / 1000000000000) (2402422453 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1438167815891347 / 4000000000000) 2 (IntervalRat.scale (557 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (34377530427 / 1000000000000) (34377632826 / 1000000000000), orderedInterval (-24313518698 / 1000000000000) (-24313416298 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2552054026733423 / 4000000000000) 2 (IntervalRat.scale (557 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-27484827450 / 1000000000000) (-27484827449 / 1000000000000), orderedInterval (-15547648548 / 1000000000000) (-15547648547 / 1000000000000)))) (orderedInterval (44614297793 / 1000000000000) (44614311358 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2384459915515787 / 4000000000000) 2 (IntervalRat.scale (557 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-79634244 / 1000000000000) (-79634243 / 1000000000000), orderedInterval (32679448498 / 1000000000000) (32679448499 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1701663108059771 / 4000000000000) 2 (IntervalRat.scale (557 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-33665110208 / 1000000000000) (-33665038591 / 1000000000000), orderedInterval (19095423266 / 1000000000000) (19095494883 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1929504599631309 / 4000000000000) 2 (IntervalRat.scale (557 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-21810986692 / 1000000000000) (-21810983809 / 1000000000000), orderedInterval (29074957335 / 1000000000000) (29074960217 / 1000000000000)))) (orderedInterval (7085909367 / 1000000000000) (7085925340 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1608619774205821 / 4000000000000) 2 (IntervalRat.scale (557 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (28986092906 / 1000000000000) (28986092907 / 1000000000000), orderedInterval (27218823006 / 1000000000000) (27218823007 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1421264355054241 / 4000000000000) 2 (IntervalRat.scale (557 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-37745777701 / 1000000000000) (-37745777700 / 1000000000000), orderedInterval (-19102954878 / 1000000000000) (-19102954877 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (411937806533859 / 800000000000) 2 (IntervalRat.scale (557 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16430538368 / 1000000000000) (16430538369 / 1000000000000), orderedInterval (31070686922 / 1000000000000) (31070686923 / 1000000000000)))) (orderedInterval (-5663950423 / 1000000000000) (-5663950365 / 1000000000000))) = true
  rfl'

theorem compactCertificate407_chunkChecks2_2 :
    compactCertificate407.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1139441651971673 / 4000000000000) 2 (IntervalRat.scale (557 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (11216942723 / 1000000000000) (11216942785 / 1000000000000), orderedInterval (-45943880549 / 1000000000000) (-45943880487 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (965917307347153 / 4000000000000) 2 (IntervalRat.scale (557 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-18163149206 / 1000000000000) (-18163149205 / 1000000000000), orderedInterval (-47987767080 / 1000000000000) (-47987767079 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (604426201959259 / 4000000000000) 2 (IntervalRat.scale (557 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (57688728602 / 1000000000000) (57688728603 / 1000000000000), orderedInterval (29558893257 / 1000000000000) (29558893258 / 1000000000000)))) (orderedInterval (513284330 / 1000000000000) (513284403 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (325062421644453 / 4000000000000) 2 (IntervalRat.scale (557 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (31845429502 / 1000000000000) (31845429503 / 1000000000000), orderedInterval (82386118071 / 1000000000000) (82386118072 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (882607708412359 / 4000000000000) 2 (IntervalRat.scale (557 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (53658122934 / 1000000000000) (53658122975 / 1000000000000), orderedInterval (2322800991 / 1000000000000) (2322801032 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1205125369383143 / 4000000000000) 2 (IntervalRat.scale (557 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (20958668673 / 1000000000000) (20958668674 / 1000000000000), orderedInterval (40877033925 / 1000000000000) (40877033926 / 1000000000000)))) (orderedInterval (2707903766 / 1000000000000) (2707903797 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (509573798040741 / 4000000000000) 2 (IntervalRat.scale (557 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (41500487707 / 1000000000000) (41500503077 / 1000000000000), orderedInterval (-57390444566 / 1000000000000) (-57390429196 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2071389198344261 / 4000000000000) 2 (IntervalRat.scale (557 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-9340987945 / 1000000000000) (-9340987944 / 1000000000000), orderedInterval (-33786018103 / 1000000000000) (-33786018102 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1383591987901099 / 4000000000000) 2 (IntervalRat.scale (557 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (38384968597 / 1000000000000) (38384968598 / 1000000000000), orderedInterval (19103771837 / 1000000000000) (19103771838 / 1000000000000)))) (orderedInterval (8426578577 / 1000000000000) (8426578758 / 1000000000000))) = true
  rfl'

theorem compactCertificate407_chunkChecks2 :
    compactCertificate407.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate407.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate407_chunkChecks2_0
    compactCertificate407_chunkChecks2_1 compactCertificate407_chunkChecks2_2

theorem compactCertificate407_chunkChecks3_0 :
    compactCertificate407.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (557 / 2) 3 (IntervalRat.scale (557 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (14894268231 / 1000000000000) (14894268421 / 1000000000000), orderedInterval (-45458574949 / 1000000000000) (-45458574759 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (820567357980857 / 4000000000000) 3 (IntervalRat.scale (557 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-55062417488 / 1000000000000) (-55062416940 / 1000000000000), orderedInterval (8586218414 / 1000000000000) (8586218962 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (265354623950681 / 800000000000) 3 (IntervalRat.scale (557 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-22166979968 / 1000000000000) (-22166978063 / 1000000000000), orderedInterval (37821357631 / 1000000000000) (37821359536 / 1000000000000)))) (orderedInterval (14249918457 / 1000000000000) (14249918754 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (239439508534699 / 4000000000000) 3 (IntervalRat.scale (557 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-84058811450 / 1000000000000) (-84058811449 / 1000000000000), orderedInterval (-59040374617 / 1000000000000) (-59040374616 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (643168199877103 / 4000000000000) 3 (IntervalRat.scale (557 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-61469189626 / 1000000000000) (-61469189624 / 1000000000000), orderedInterval (-13254869970 / 1000000000000) (-13254869968 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1746326776699251 / 4000000000000) 3 (IntervalRat.scale (557 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-24172048225 / 1000000000000) (-24172048224 / 1000000000000), orderedInterval (-29534182452 / 1000000000000) (-29534182451 / 1000000000000)))) (orderedInterval (-7988720348 / 1000000000000) (-7988720269 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1286336399754763 / 4000000000000) 3 (IntervalRat.scale (557 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (41705426286 / 1000000000000) (41705436421 / 1000000000000), orderedInterval (-15566207705 / 1000000000000) (-15566197570 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2204159345881399 / 4000000000000) 3 (IntervalRat.scale (557 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-30219184226 / 1000000000000) (-30219096339 / 1000000000000), orderedInterval (15587242590 / 1000000000000) (15587330477 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1623573798040741 / 4000000000000) 3 (IntervalRat.scale (557 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-39112036375 / 1000000000000) (-39112036344 / 1000000000000), orderedInterval (-6171795590 / 1000000000000) (-6171795559 / 1000000000000)))) (orderedInterval (4191651226 / 1000000000000) (4191672352 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate407_chunkChecks3_1 :
    compactCertificate407.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2490979726934443 / 4000000000000) 3 (IntervalRat.scale (557 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (31880786012 / 1000000000000) (31880786455 / 1000000000000), orderedInterval (2402422010 / 1000000000000) (2402422453 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1438167815891347 / 4000000000000) 3 (IntervalRat.scale (557 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (34377530427 / 1000000000000) (34377632826 / 1000000000000), orderedInterval (-24313518698 / 1000000000000) (-24313416298 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2552054026733423 / 4000000000000) 3 (IntervalRat.scale (557 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-27484827450 / 1000000000000) (-27484827449 / 1000000000000), orderedInterval (-15547648548 / 1000000000000) (-15547648547 / 1000000000000)))) (orderedInterval (35061607604 / 1000000000000) (35061625932 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2384459915515787 / 4000000000000) 3 (IntervalRat.scale (557 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-79634244 / 1000000000000) (-79634243 / 1000000000000), orderedInterval (32679448498 / 1000000000000) (32679448499 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1701663108059771 / 4000000000000) 3 (IntervalRat.scale (557 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-33665110208 / 1000000000000) (-33665038591 / 1000000000000), orderedInterval (19095423266 / 1000000000000) (19095494883 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1929504599631309 / 4000000000000) 3 (IntervalRat.scale (557 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-21810986692 / 1000000000000) (-21810983809 / 1000000000000), orderedInterval (29074957335 / 1000000000000) (29074960217 / 1000000000000)))) (orderedInterval (88600841 / 1000000000000) (88625263 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1608619774205821 / 4000000000000) 3 (IntervalRat.scale (557 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (28986092906 / 1000000000000) (28986092907 / 1000000000000), orderedInterval (27218823006 / 1000000000000) (27218823007 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1421264355054241 / 4000000000000) 3 (IntervalRat.scale (557 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-37745777701 / 1000000000000) (-37745777700 / 1000000000000), orderedInterval (-19102954878 / 1000000000000) (-19102954877 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (411937806533859 / 800000000000) 3 (IntervalRat.scale (557 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16430538368 / 1000000000000) (16430538369 / 1000000000000), orderedInterval (31070686922 / 1000000000000) (31070686923 / 1000000000000)))) (orderedInterval (-8224365169 / 1000000000000) (-8224365080 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate407_chunkChecks3_2 :
    compactCertificate407.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1139441651971673 / 4000000000000) 3 (IntervalRat.scale (557 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (11216942723 / 1000000000000) (11216942785 / 1000000000000), orderedInterval (-45943880549 / 1000000000000) (-45943880487 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (965917307347153 / 4000000000000) 3 (IntervalRat.scale (557 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-18163149206 / 1000000000000) (-18163149205 / 1000000000000), orderedInterval (-47987767080 / 1000000000000) (-47987767079 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (604426201959259 / 4000000000000) 3 (IntervalRat.scale (557 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (57688728602 / 1000000000000) (57688728603 / 1000000000000), orderedInterval (29558893257 / 1000000000000) (29558893258 / 1000000000000)))) (orderedInterval (-9786946741 / 1000000000000) (-9786946670 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (325062421644453 / 4000000000000) 3 (IntervalRat.scale (557 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (31845429502 / 1000000000000) (31845429503 / 1000000000000), orderedInterval (82386118071 / 1000000000000) (82386118072 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (882607708412359 / 4000000000000) 3 (IntervalRat.scale (557 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (53658122934 / 1000000000000) (53658122975 / 1000000000000), orderedInterval (2322800991 / 1000000000000) (2322801032 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1205125369383143 / 4000000000000) 3 (IntervalRat.scale (557 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (20958668673 / 1000000000000) (20958668674 / 1000000000000), orderedInterval (40877033925 / 1000000000000) (40877033926 / 1000000000000)))) (orderedInterval (4020385383 / 1000000000000) (4020385415 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (509573798040741 / 4000000000000) 3 (IntervalRat.scale (557 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (41500487707 / 1000000000000) (41500503077 / 1000000000000), orderedInterval (-57390444566 / 1000000000000) (-57390429196 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2071389198344261 / 4000000000000) 3 (IntervalRat.scale (557 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-9340987945 / 1000000000000) (-9340987944 / 1000000000000), orderedInterval (-33786018103 / 1000000000000) (-33786018102 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1383591987901099 / 4000000000000) 3 (IntervalRat.scale (557 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (38384968597 / 1000000000000) (38384968598 / 1000000000000), orderedInterval (19103771837 / 1000000000000) (19103771838 / 1000000000000)))) (orderedInterval (-10810642744 / 1000000000000) (-10810642487 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate407_chunkChecks3 :
    compactCertificate407.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate407.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate407_chunkChecks3_0
    compactCertificate407_chunkChecks3_1 compactCertificate407_chunkChecks3_2

theorem compactCertificate407_chunkChecks4_0 :
    compactCertificate407.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (557 / 2) 4 (IntervalRat.scale (557 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (14894268231 / 1000000000000) (14894268421 / 1000000000000), orderedInterval (-45458574949 / 1000000000000) (-45458574759 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (820567357980857 / 4000000000000) 4 (IntervalRat.scale (557 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-55062417488 / 1000000000000) (-55062416940 / 1000000000000), orderedInterval (8586218414 / 1000000000000) (8586218962 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (265354623950681 / 800000000000) 4 (IntervalRat.scale (557 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-22166979968 / 1000000000000) (-22166978063 / 1000000000000), orderedInterval (37821357631 / 1000000000000) (37821359536 / 1000000000000)))) (orderedInterval (3032859418 / 1000000000000) (3032859756 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (239439508534699 / 4000000000000) 4 (IntervalRat.scale (557 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-84058811450 / 1000000000000) (-84058811449 / 1000000000000), orderedInterval (-59040374617 / 1000000000000) (-59040374616 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (643168199877103 / 4000000000000) 4 (IntervalRat.scale (557 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-61469189626 / 1000000000000) (-61469189624 / 1000000000000), orderedInterval (-13254869970 / 1000000000000) (-13254869968 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1746326776699251 / 4000000000000) 4 (IntervalRat.scale (557 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-24172048225 / 1000000000000) (-24172048224 / 1000000000000), orderedInterval (-29534182452 / 1000000000000) (-29534182451 / 1000000000000)))) (orderedInterval (10187119288 / 1000000000000) (10187119410 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1286336399754763 / 4000000000000) 4 (IntervalRat.scale (557 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (41705426286 / 1000000000000) (41705436421 / 1000000000000), orderedInterval (-15566207705 / 1000000000000) (-15566197570 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2204159345881399 / 4000000000000) 4 (IntervalRat.scale (557 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-30219184226 / 1000000000000) (-30219096339 / 1000000000000), orderedInterval (15587242590 / 1000000000000) (15587330477 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1623573798040741 / 4000000000000) 4 (IntervalRat.scale (557 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-39112036375 / 1000000000000) (-39112036344 / 1000000000000), orderedInterval (-6171795590 / 1000000000000) (-6171795559 / 1000000000000)))) (orderedInterval (9990176665 / 1000000000000) (9990218528 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate407_chunkChecks4_1 :
    compactCertificate407.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2490979726934443 / 4000000000000) 4 (IntervalRat.scale (557 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (31880786012 / 1000000000000) (31880786455 / 1000000000000), orderedInterval (2402422010 / 1000000000000) (2402422453 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1438167815891347 / 4000000000000) 4 (IntervalRat.scale (557 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (34377530427 / 1000000000000) (34377632826 / 1000000000000), orderedInterval (-24313518698 / 1000000000000) (-24313416298 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2552054026733423 / 4000000000000) 4 (IntervalRat.scale (557 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-27484827450 / 1000000000000) (-27484827449 / 1000000000000), orderedInterval (-15547648548 / 1000000000000) (-15547648547 / 1000000000000)))) (orderedInterval (-242412661771 / 1000000000000) (-242412636215 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2384459915515787 / 4000000000000) 4 (IntervalRat.scale (557 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-79634244 / 1000000000000) (-79634243 / 1000000000000), orderedInterval (32679448498 / 1000000000000) (32679448499 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1701663108059771 / 4000000000000) 4 (IntervalRat.scale (557 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-33665110208 / 1000000000000) (-33665038591 / 1000000000000), orderedInterval (19095423266 / 1000000000000) (19095494883 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1929504599631309 / 4000000000000) 4 (IntervalRat.scale (557 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-21810986692 / 1000000000000) (-21810983809 / 1000000000000), orderedInterval (29074957335 / 1000000000000) (29074960217 / 1000000000000)))) (orderedInterval (-16309205157 / 1000000000000) (-16309167718 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1608619774205821 / 4000000000000) 4 (IntervalRat.scale (557 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (28986092906 / 1000000000000) (28986092907 / 1000000000000), orderedInterval (27218823006 / 1000000000000) (27218823007 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1421264355054241 / 4000000000000) 4 (IntervalRat.scale (557 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-37745777701 / 1000000000000) (-37745777700 / 1000000000000), orderedInterval (-19102954878 / 1000000000000) (-19102954877 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (411937806533859 / 800000000000) 4 (IntervalRat.scale (557 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16430538368 / 1000000000000) (16430538369 / 1000000000000), orderedInterval (31070686922 / 1000000000000) (31070686923 / 1000000000000)))) (orderedInterval (12153472025 / 1000000000000) (12153472166 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate407_chunkChecks4_2 :
    compactCertificate407.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1139441651971673 / 4000000000000) 4 (IntervalRat.scale (557 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (11216942723 / 1000000000000) (11216942785 / 1000000000000), orderedInterval (-45943880549 / 1000000000000) (-45943880487 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (965917307347153 / 4000000000000) 4 (IntervalRat.scale (557 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-18163149206 / 1000000000000) (-18163149205 / 1000000000000), orderedInterval (-47987767080 / 1000000000000) (-47987767079 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (604426201959259 / 4000000000000) 4 (IntervalRat.scale (557 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (57688728602 / 1000000000000) (57688728603 / 1000000000000), orderedInterval (29558893257 / 1000000000000) (29558893258 / 1000000000000)))) (orderedInterval (-1148928697 / 1000000000000) (-1148928627 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (325062421644453 / 4000000000000) 4 (IntervalRat.scale (557 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (31845429502 / 1000000000000) (31845429503 / 1000000000000), orderedInterval (82386118071 / 1000000000000) (82386118072 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (882607708412359 / 4000000000000) 4 (IntervalRat.scale (557 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (53658122934 / 1000000000000) (53658122975 / 1000000000000), orderedInterval (2322800991 / 1000000000000) (2322801032 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1205125369383143 / 4000000000000) 4 (IntervalRat.scale (557 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (20958668673 / 1000000000000) (20958668674 / 1000000000000), orderedInterval (40877033925 / 1000000000000) (40877033926 / 1000000000000)))) (orderedInterval (-2712656773 / 1000000000000) (-2712656740 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (509573798040741 / 4000000000000) 4 (IntervalRat.scale (557 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (41500487707 / 1000000000000) (41500503077 / 1000000000000), orderedInterval (-57390444566 / 1000000000000) (-57390429196 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2071389198344261 / 4000000000000) 4 (IntervalRat.scale (557 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-9340987945 / 1000000000000) (-9340987944 / 1000000000000), orderedInterval (-33786018103 / 1000000000000) (-33786018102 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1383591987901099 / 4000000000000) 4 (IntervalRat.scale (557 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (38384968597 / 1000000000000) (38384968598 / 1000000000000), orderedInterval (19103771837 / 1000000000000) (19103771838 / 1000000000000)))) (orderedInterval (-7959429463 / 1000000000000) (-7959429061 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate407_chunkChecks4 :
    compactCertificate407.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate407.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate407_chunkChecks4_0
    compactCertificate407_chunkChecks4_1 compactCertificate407_chunkChecks4_2

theorem compactCertificate407_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate407.chunkCheck r b = true :=
  compactCertificate407.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate407_chunkChecks0
    · exact compactCertificate407_chunkChecks1
    · exact compactCertificate407_chunkChecks2
    · exact compactCertificate407_chunkChecks3
    · exact compactCertificate407_chunkChecks4)

theorem compactCertificate407_coefficient0 :
    compactCertificate407.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate407_coefficient1 :
    compactCertificate407.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate407_coefficient2 :
    compactCertificate407.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate407_coefficient3 :
    compactCertificate407.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate407_coefficient4 :
    compactCertificate407.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate407_coefficients : ∀ r : Fin 5,
    compactCertificate407.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate407_coefficient0
  · exact compactCertificate407_coefficient1
  · exact compactCertificate407_coefficient2
  · exact compactCertificate407_coefficient3
  · exact compactCertificate407_coefficient4

theorem compactCertificate407_lower : (1 : ℚ) ≤ compactCertificate407.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate407, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate407_proves {t : ℝ} (ht : t ∈ compactCertificate407.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate407.proves compactCertificate407_states compactCertificate407_chunks
    compactCertificate407_coefficients compactCertificate407_lower ht

end Erdos232
