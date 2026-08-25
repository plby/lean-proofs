/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate584 : CompactCertificate where
  left := 455
  right := 456
  center := 911 / 2
  grid := fun i =>
    match i.val with
    | 0 => 145
    | 1 => 107
    | 2 => 173
    | 3 => 31
    | 4 => 84
    | 5 => 227
    | 6 => 168
    | 7 => 287
    | 8 => 211
    | 9 => 324
    | 10 => 187
    | 11 => 332
    | 12 => 311
    | 13 => 222
    | 14 => 251
    | 15 => 209
    | 16 => 185
    | 17 => 268
    | 18 => 148
    | 19 => 126
    | 20 => 79
    | 21 => 42
    | 22 => 115
    | 23 => 157
    | 24 => 66
    | 25 => 270
    | _ => 180
  point := fun i =>
    match i.val with
    | 0 => 911 / 2
    | 1 => 1342076953537811 / 4000000000000
    | 2 => 434000112062963 / 800000000000
    | 3 => 391614707854777 / 4000000000000
    | 4 => 1051932190463269 / 4000000000000
    | 5 => 2856200527061073 / 4000000000000
    | 6 => 2103864380927449 / 4000000000000
    | 7 => 3605007475938877 / 4000000000000
    | 8 => 2655432190332343 / 4000000000000
    | 9 => 4074115855004089 / 4000000000000
    | 10 => 2352191885596081 / 4000000000000
    | 11 => 4174005778014629 / 4000000000000
    | 12 => 3899897635610201 / 4000000000000
    | 13 => 2783150972069033 / 4000000000000
    | 14 => 3155796571389807 / 4000000000000
    | 15 => 2630974172893183 / 4000000000000
    | 16 => 2324545471192843 / 4000000000000
    | 17 => 673743881063457 / 800000000000
    | 18 => 1863611032219379 / 4000000000000
    | 19 => 1579803710939419 / 4000000000000
    | 20 => 988567809667657 / 4000000000000
    | 21 => 531655055867319 / 4000000000000
    | 22 => 1443546898318957 / 4000000000000
    | 23 => 1971039877034189 / 4000000000000
    | 24 => 833432190332343 / 4000000000000
    | 25 => 3387855582929303 / 4000000000000
    | _ => 2262930522401977 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-25597330043 / 1000000000000) (-25597330042 / 1000000000000), orderedInterval (-27219016074 / 1000000000000) (-27219016073 / 1000000000000))
    | 1 => (orderedInterval (-6675197792 / 1000000000000) (-6675197791 / 1000000000000), orderedInterval (-43034916750 / 1000000000000) (-43034916749 / 1000000000000))
    | 2 => (orderedInterval (7148470389 / 1000000000000) (7148470394 / 1000000000000), orderedInterval (-33508710634 / 1000000000000) (-33508710629 / 1000000000000))
    | 3 => (orderedInterval (-77664999259 / 1000000000000) (-77664999257 / 1000000000000), orderedInterval (-21296381920 / 1000000000000) (-21296381919 / 1000000000000))
    | 4 => (orderedInterval (-6173806721 / 1000000000000) (-6173806708 / 1000000000000), orderedInterval (48824153253 / 1000000000000) (48824153266 / 1000000000000))
    | 5 => (orderedInterval (-29633350934 / 1000000000000) (-29633343742 / 1000000000000), orderedInterval (3684929963 / 1000000000000) (3684937155 / 1000000000000))
    | 6 => (orderedInterval (-29938361024 / 1000000000000) (-29938262107 / 1000000000000), orderedInterval (17750681772 / 1000000000000) (17750780689 / 1000000000000))
    | 7 => (orderedInterval (-10350735615 / 1000000000000) (-10350735614 / 1000000000000), orderedInterval (-24473536787 / 1000000000000) (-24473536786 / 1000000000000))
    | 8 => (orderedInterval (-30371838302 / 1000000000000) (-30371826664 / 1000000000000), orderedInterval (6066151592 / 1000000000000) (6066163230 / 1000000000000))
    | 9 => (orderedInterval (24781373331 / 1000000000000) (24781375776 / 1000000000000), orderedInterval (3292657050 / 1000000000000) (3292659495 / 1000000000000))
    | 10 => (orderedInterval (-32142042699 / 1000000000000) (-32142042647 / 1000000000000), orderedInterval (-7007377581 / 1000000000000) (-7007377529 / 1000000000000))
    | 11 => (orderedInterval (23648321213 / 1000000000000) (23648321638 / 1000000000000), orderedInterval (7118691637 / 1000000000000) (7118692061 / 1000000000000))
    | 12 => (orderedInterval (24448006991 / 1000000000000) (24448116027 / 1000000000000), orderedInterval (-7445804370 / 1000000000000) (-7445695334 / 1000000000000))
    | 13 => (orderedInterval (-22935473935 / 1000000000000) (-22935464933 / 1000000000000), orderedInterval (19737704622 / 1000000000000) (19737713624 / 1000000000000))
    | 14 => (orderedInterval (-26420140766 / 1000000000000) (-26420140744 / 1000000000000), orderedInterval (-10418639358 / 1000000000000) (-10418639337 / 1000000000000))
    | 15 => (orderedInterval (-29060394692 / 1000000000000) (-29060340534 / 1000000000000), orderedInterval (11129685681 / 1000000000000) (11129739839 / 1000000000000))
    | 16 => (orderedInterval (-21995693246 / 1000000000000) (-21995693245 / 1000000000000), orderedInterval (-24712907216 / 1000000000000) (-24712907215 / 1000000000000))
    | 17 => (orderedInterval (23402910148 / 1000000000000) (23402910150 / 1000000000000), orderedInterval (14416031677 / 1000000000000) (14416031679 / 1000000000000))
    | 18 => (orderedInterval (36484833142 / 1000000000000) (36484835990 / 1000000000000), orderedInterval (-5978692033 / 1000000000000) (-5978689184 / 1000000000000))
    | 19 => (orderedInterval (-4194462920 / 1000000000000) (-4194462917 / 1000000000000), orderedInterval (39934041884 / 1000000000000) (39934041887 / 1000000000000))
    | 20 => (orderedInterval (12997460220 / 1000000000000) (12997460327 / 1000000000000), orderedInterval (-49087463326 / 1000000000000) (-49087463219 / 1000000000000))
    | 21 => (orderedInterval (68082797426 / 1000000000000) (68082797922 / 1000000000000), orderedInterval (-12682753760 / 1000000000000) (-12682753264 / 1000000000000))
    | 22 => (orderedInterval (-15914524881 / 1000000000000) (-15914524880 / 1000000000000), orderedInterval (-38846605369 / 1000000000000) (-38846605368 / 1000000000000))
    | 23 => (orderedInterval (-11138230773 / 1000000000000) (-11138230772 / 1000000000000), orderedInterval (-34163065272 / 1000000000000) (-34163065271 / 1000000000000))
    | 24 => (orderedInterval (53858475531 / 1000000000000) (53858476902 / 1000000000000), orderedInterval (-12565847313 / 1000000000000) (-12565845942 / 1000000000000))
    | 25 => (orderedInterval (-12681395219 / 1000000000000) (-12681395187 / 1000000000000), orderedInterval (24314512822 / 1000000000000) (24314512854 / 1000000000000))
    | _ => (orderedInterval (28778028814 / 1000000000000) (28778028815 / 1000000000000), orderedInterval (17211918777 / 1000000000000) (17211918778 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-9788605061 / 1000000000000) (-9788605028 / 1000000000000)
      | 1 => orderedInterval (2723817455 / 1000000000000) (2723818022 / 1000000000000)
      | 2 => orderedInterval (-414769322 / 1000000000000) (-414769014 / 1000000000000)
      | 3 => orderedInterval (-3423064026 / 1000000000000) (-3423063347 / 1000000000000)
      | 4 => orderedInterval (-2476506987 / 1000000000000) (-2476504112 / 1000000000000)
      | 5 => orderedInterval (1522367504 / 1000000000000) (1522368174 / 1000000000000)
      | 6 => orderedInterval (-5173107323 / 1000000000000) (-5173106750 / 1000000000000)
      | 7 => orderedInterval (-42484807 / 1000000000000) (-42484743 / 1000000000000)
      | _ => orderedInterval (-4042557004 / 1000000000000) (-4042556867 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-13425938035 / 1000000000000) (-13425937998 / 1000000000000)
      | 1 => orderedInterval (668222994 / 1000000000000) (668223858 / 1000000000000)
      | 2 => orderedInterval (1707237700 / 1000000000000) (1707238155 / 1000000000000)
      | 3 => orderedInterval (339783142 / 1000000000000) (339784630 / 1000000000000)
      | 4 => orderedInterval (3230090969 / 1000000000000) (3230096571 / 1000000000000)
      | 5 => orderedInterval (2672347124 / 1000000000000) (2672348091 / 1000000000000)
      | 6 => orderedInterval (-1849093180 / 1000000000000) (-1849092606 / 1000000000000)
      | 7 => orderedInterval (3598973537 / 1000000000000) (3598973589 / 1000000000000)
      | _ => orderedInterval (-7725831201 / 1000000000000) (-7725831015 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (9614084488 / 1000000000000) (9614084530 / 1000000000000)
      | 1 => orderedInterval (-5142130576 / 1000000000000) (-5142129232 / 1000000000000)
      | 2 => orderedInterval (305545440 / 1000000000000) (305546118 / 1000000000000)
      | 3 => orderedInterval (8342023888 / 1000000000000) (8342027188 / 1000000000000)
      | 4 => orderedInterval (6674548670 / 1000000000000) (6674559833 / 1000000000000)
      | 5 => orderedInterval (-3403387019 / 1000000000000) (-3403385618 / 1000000000000)
      | 6 => orderedInterval (5804160126 / 1000000000000) (5804160706 / 1000000000000)
      | 7 => orderedInterval (-1126483745 / 1000000000000) (-1126483695 / 1000000000000)
      | _ => orderedInterval (4709120670 / 1000000000000) (4709120943 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (14249688396 / 1000000000000) (14249688445 / 1000000000000)
      | 1 => orderedInterval (675077624 / 1000000000000) (675079726 / 1000000000000)
      | 2 => orderedInterval (-6301620501 / 1000000000000) (-6301619484 / 1000000000000)
      | 3 => orderedInterval (-4526842566 / 1000000000000) (-4526835213 / 1000000000000)
      | 4 => orderedInterval (-8259255836 / 1000000000000) (-8259233226 / 1000000000000)
      | 5 => orderedInterval (-5649338565 / 1000000000000) (-5649336534 / 1000000000000)
      | 6 => orderedInterval (692957996 / 1000000000000) (692958583 / 1000000000000)
      | 7 => orderedInterval (-3756353184 / 1000000000000) (-3756353133 / 1000000000000)
      | _ => orderedInterval (18908201431 / 1000000000000) (18908201852 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-9382687699 / 1000000000000) (-9382687642 / 1000000000000)
      | 1 => orderedInterval (12695554410 / 1000000000000) (12695557705 / 1000000000000)
      | 2 => orderedInterval (1608880603 / 1000000000000) (1608882143 / 1000000000000)
      | 3 => orderedInterval (-24084816953 / 1000000000000) (-24084800491 / 1000000000000)
      | 4 => orderedInterval (-19832921272 / 1000000000000) (-19832874791 / 1000000000000)
      | 5 => orderedInterval (8903067941 / 1000000000000) (8903070898 / 1000000000000)
      | 6 => orderedInterval (-6217260647 / 1000000000000) (-6217260050 / 1000000000000)
      | 7 => orderedInterval (1318743565 / 1000000000000) (1318743618 / 1000000000000)
      | _ => orderedInterval (-577346481 / 1000000000000) (-577345801 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-21114909571 / 1000000000000) (-21114903665 / 1000000000000)
    | 1 => orderedInterval (-10784206950 / 1000000000000) (-10784196725 / 1000000000000)
    | 2 => orderedInterval (25777481942 / 1000000000000) (25777500773 / 1000000000000)
    | 3 => orderedInterval (6032514795 / 1000000000000) (6032551016 / 1000000000000)
    | _ => orderedInterval (-35568786533 / 1000000000000) (-35568714411 / 1000000000000)

theorem compactCertificate584_stateChecks0 :
    compactCertificate584.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 145 12 (911 / 2)) (orderedInterval (-25597330043 / 1000000000000) (-25597330042 / 1000000000000), orderedInterval (-27219016074 / 1000000000000) (-27219016073 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 107 12 (1342076953537811 / 4000000000000)) (orderedInterval (-6675197792 / 1000000000000) (-6675197791 / 1000000000000), orderedInterval (-43034916750 / 1000000000000) (-43034916749 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 173 12 (434000112062963 / 800000000000)) (orderedInterval (7148470389 / 1000000000000) (7148470394 / 1000000000000), orderedInterval (-33508710634 / 1000000000000) (-33508710629 / 1000000000000))) = true
  rfl'

theorem compactCertificate584_stateChecks1 :
    compactCertificate584.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 31 12 (391614707854777 / 4000000000000)) (orderedInterval (-77664999259 / 1000000000000) (-77664999257 / 1000000000000), orderedInterval (-21296381920 / 1000000000000) (-21296381919 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 84 12 (1051932190463269 / 4000000000000)) (orderedInterval (-6173806721 / 1000000000000) (-6173806708 / 1000000000000), orderedInterval (48824153253 / 1000000000000) (48824153266 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 227 12 (2856200527061073 / 4000000000000)) (orderedInterval (-29633350934 / 1000000000000) (-29633343742 / 1000000000000), orderedInterval (3684929963 / 1000000000000) (3684937155 / 1000000000000))) = true
  rfl'

theorem compactCertificate584_stateChecks2 :
    compactCertificate584.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 168 12 (2103864380927449 / 4000000000000)) (orderedInterval (-29938361024 / 1000000000000) (-29938262107 / 1000000000000), orderedInterval (17750681772 / 1000000000000) (17750780689 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 287 12 (3605007475938877 / 4000000000000)) (orderedInterval (-10350735615 / 1000000000000) (-10350735614 / 1000000000000), orderedInterval (-24473536787 / 1000000000000) (-24473536786 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 211 12 (2655432190332343 / 4000000000000)) (orderedInterval (-30371838302 / 1000000000000) (-30371826664 / 1000000000000), orderedInterval (6066151592 / 1000000000000) (6066163230 / 1000000000000))) = true
  rfl'

theorem compactCertificate584_stateChecks3 :
    compactCertificate584.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 324 12 (4074115855004089 / 4000000000000)) (orderedInterval (24781373331 / 1000000000000) (24781375776 / 1000000000000), orderedInterval (3292657050 / 1000000000000) (3292659495 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 187 12 (2352191885596081 / 4000000000000)) (orderedInterval (-32142042699 / 1000000000000) (-32142042647 / 1000000000000), orderedInterval (-7007377581 / 1000000000000) (-7007377529 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 332 12 (4174005778014629 / 4000000000000)) (orderedInterval (23648321213 / 1000000000000) (23648321638 / 1000000000000), orderedInterval (7118691637 / 1000000000000) (7118692061 / 1000000000000))) = true
  rfl'

theorem compactCertificate584_stateChecks4 :
    compactCertificate584.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 311 12 (3899897635610201 / 4000000000000)) (orderedInterval (24448006991 / 1000000000000) (24448116027 / 1000000000000), orderedInterval (-7445804370 / 1000000000000) (-7445695334 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 222 12 (2783150972069033 / 4000000000000)) (orderedInterval (-22935473935 / 1000000000000) (-22935464933 / 1000000000000), orderedInterval (19737704622 / 1000000000000) (19737713624 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 251 12 (3155796571389807 / 4000000000000)) (orderedInterval (-26420140766 / 1000000000000) (-26420140744 / 1000000000000), orderedInterval (-10418639358 / 1000000000000) (-10418639337 / 1000000000000))) = true
  rfl'

theorem compactCertificate584_stateChecks5 :
    compactCertificate584.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 209 12 (2630974172893183 / 4000000000000)) (orderedInterval (-29060394692 / 1000000000000) (-29060340534 / 1000000000000), orderedInterval (11129685681 / 1000000000000) (11129739839 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 185 12 (2324545471192843 / 4000000000000)) (orderedInterval (-21995693246 / 1000000000000) (-21995693245 / 1000000000000), orderedInterval (-24712907216 / 1000000000000) (-24712907215 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 268 12 (673743881063457 / 800000000000)) (orderedInterval (23402910148 / 1000000000000) (23402910150 / 1000000000000), orderedInterval (14416031677 / 1000000000000) (14416031679 / 1000000000000))) = true
  rfl'

theorem compactCertificate584_stateChecks6 :
    compactCertificate584.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 148 12 (1863611032219379 / 4000000000000)) (orderedInterval (36484833142 / 1000000000000) (36484835990 / 1000000000000), orderedInterval (-5978692033 / 1000000000000) (-5978689184 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 126 12 (1579803710939419 / 4000000000000)) (orderedInterval (-4194462920 / 1000000000000) (-4194462917 / 1000000000000), orderedInterval (39934041884 / 1000000000000) (39934041887 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 79 12 (988567809667657 / 4000000000000)) (orderedInterval (12997460220 / 1000000000000) (12997460327 / 1000000000000), orderedInterval (-49087463326 / 1000000000000) (-49087463219 / 1000000000000))) = true
  rfl'

theorem compactCertificate584_stateChecks7 :
    compactCertificate584.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 42 12 (531655055867319 / 4000000000000)) (orderedInterval (68082797426 / 1000000000000) (68082797922 / 1000000000000), orderedInterval (-12682753760 / 1000000000000) (-12682753264 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 115 12 (1443546898318957 / 4000000000000)) (orderedInterval (-15914524881 / 1000000000000) (-15914524880 / 1000000000000), orderedInterval (-38846605369 / 1000000000000) (-38846605368 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 157 12 (1971039877034189 / 4000000000000)) (orderedInterval (-11138230773 / 1000000000000) (-11138230772 / 1000000000000), orderedInterval (-34163065272 / 1000000000000) (-34163065271 / 1000000000000))) = true
  rfl'

theorem compactCertificate584_stateChecks8 :
    compactCertificate584.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (833432190332343 / 4000000000000)) (orderedInterval (53858475531 / 1000000000000) (53858476902 / 1000000000000), orderedInterval (-12565847313 / 1000000000000) (-12565845942 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 270 12 (3387855582929303 / 4000000000000)) (orderedInterval (-12681395219 / 1000000000000) (-12681395187 / 1000000000000), orderedInterval (24314512822 / 1000000000000) (24314512854 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 180 12 (2262930522401977 / 4000000000000)) (orderedInterval (28778028814 / 1000000000000) (28778028815 / 1000000000000), orderedInterval (17211918777 / 1000000000000) (17211918778 / 1000000000000))) = true
  rfl'

theorem compactCertificate584_states : ∀ j,
    BesselStateValid (compactCertificate584.point j) (compactCertificate584.state j) :=
  compactCertificate584.statesValid_of_checks3 compactCertificate584_stateChecks0
    compactCertificate584_stateChecks1 compactCertificate584_stateChecks2
    compactCertificate584_stateChecks3 compactCertificate584_stateChecks4
    compactCertificate584_stateChecks5 compactCertificate584_stateChecks6
    compactCertificate584_stateChecks7 compactCertificate584_stateChecks8

theorem compactCertificate584_chunkChecks0_0 :
    compactCertificate584.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (911 / 2) 0 (IntervalRat.scale (911 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-25597330043 / 1000000000000) (-25597330042 / 1000000000000), orderedInterval (-27219016074 / 1000000000000) (-27219016073 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1342076953537811 / 4000000000000) 0 (IntervalRat.scale (911 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-6675197792 / 1000000000000) (-6675197791 / 1000000000000), orderedInterval (-43034916750 / 1000000000000) (-43034916749 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (434000112062963 / 800000000000) 0 (IntervalRat.scale (911 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (7148470389 / 1000000000000) (7148470394 / 1000000000000), orderedInterval (-33508710634 / 1000000000000) (-33508710629 / 1000000000000)))) (orderedInterval (-9788605061 / 1000000000000) (-9788605028 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (391614707854777 / 4000000000000) 0 (IntervalRat.scale (911 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-77664999259 / 1000000000000) (-77664999257 / 1000000000000), orderedInterval (-21296381920 / 1000000000000) (-21296381919 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (1051932190463269 / 4000000000000) 0 (IntervalRat.scale (911 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-6173806721 / 1000000000000) (-6173806708 / 1000000000000), orderedInterval (48824153253 / 1000000000000) (48824153266 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2856200527061073 / 4000000000000) 0 (IntervalRat.scale (911 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29633350934 / 1000000000000) (-29633343742 / 1000000000000), orderedInterval (3684929963 / 1000000000000) (3684937155 / 1000000000000)))) (orderedInterval (2723817455 / 1000000000000) (2723818022 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (2103864380927449 / 4000000000000) 0 (IntervalRat.scale (911 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-29938361024 / 1000000000000) (-29938262107 / 1000000000000), orderedInterval (17750681772 / 1000000000000) (17750780689 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3605007475938877 / 4000000000000) 0 (IntervalRat.scale (911 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-10350735615 / 1000000000000) (-10350735614 / 1000000000000), orderedInterval (-24473536787 / 1000000000000) (-24473536786 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2655432190332343 / 4000000000000) 0 (IntervalRat.scale (911 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-30371838302 / 1000000000000) (-30371826664 / 1000000000000), orderedInterval (6066151592 / 1000000000000) (6066163230 / 1000000000000)))) (orderedInterval (-414769322 / 1000000000000) (-414769014 / 1000000000000))) = true
  rfl'

theorem compactCertificate584_chunkChecks0_1 :
    compactCertificate584.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (4074115855004089 / 4000000000000) 0 (IntervalRat.scale (911 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (24781373331 / 1000000000000) (24781375776 / 1000000000000), orderedInterval (3292657050 / 1000000000000) (3292659495 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2352191885596081 / 4000000000000) 0 (IntervalRat.scale (911 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-32142042699 / 1000000000000) (-32142042647 / 1000000000000), orderedInterval (-7007377581 / 1000000000000) (-7007377529 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (4174005778014629 / 4000000000000) 0 (IntervalRat.scale (911 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (23648321213 / 1000000000000) (23648321638 / 1000000000000), orderedInterval (7118691637 / 1000000000000) (7118692061 / 1000000000000)))) (orderedInterval (-3423064026 / 1000000000000) (-3423063347 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3899897635610201 / 4000000000000) 0 (IntervalRat.scale (911 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (24448006991 / 1000000000000) (24448116027 / 1000000000000), orderedInterval (-7445804370 / 1000000000000) (-7445695334 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2783150972069033 / 4000000000000) 0 (IntervalRat.scale (911 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-22935473935 / 1000000000000) (-22935464933 / 1000000000000), orderedInterval (19737704622 / 1000000000000) (19737713624 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (3155796571389807 / 4000000000000) 0 (IntervalRat.scale (911 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-26420140766 / 1000000000000) (-26420140744 / 1000000000000), orderedInterval (-10418639358 / 1000000000000) (-10418639337 / 1000000000000)))) (orderedInterval (-2476506987 / 1000000000000) (-2476504112 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2630974172893183 / 4000000000000) 0 (IntervalRat.scale (911 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-29060394692 / 1000000000000) (-29060340534 / 1000000000000), orderedInterval (11129685681 / 1000000000000) (11129739839 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2324545471192843 / 4000000000000) 0 (IntervalRat.scale (911 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-21995693246 / 1000000000000) (-21995693245 / 1000000000000), orderedInterval (-24712907216 / 1000000000000) (-24712907215 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (673743881063457 / 800000000000) 0 (IntervalRat.scale (911 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (23402910148 / 1000000000000) (23402910150 / 1000000000000), orderedInterval (14416031677 / 1000000000000) (14416031679 / 1000000000000)))) (orderedInterval (1522367504 / 1000000000000) (1522368174 / 1000000000000))) = true
  rfl'

theorem compactCertificate584_chunkChecks0_2 :
    compactCertificate584.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1863611032219379 / 4000000000000) 0 (IntervalRat.scale (911 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (36484833142 / 1000000000000) (36484835990 / 1000000000000), orderedInterval (-5978692033 / 1000000000000) (-5978689184 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1579803710939419 / 4000000000000) 0 (IntervalRat.scale (911 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-4194462920 / 1000000000000) (-4194462917 / 1000000000000), orderedInterval (39934041884 / 1000000000000) (39934041887 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (988567809667657 / 4000000000000) 0 (IntervalRat.scale (911 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (12997460220 / 1000000000000) (12997460327 / 1000000000000), orderedInterval (-49087463326 / 1000000000000) (-49087463219 / 1000000000000)))) (orderedInterval (-5173107323 / 1000000000000) (-5173106750 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (531655055867319 / 4000000000000) 0 (IntervalRat.scale (911 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (68082797426 / 1000000000000) (68082797922 / 1000000000000), orderedInterval (-12682753760 / 1000000000000) (-12682753264 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1443546898318957 / 4000000000000) 0 (IntervalRat.scale (911 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-15914524881 / 1000000000000) (-15914524880 / 1000000000000), orderedInterval (-38846605369 / 1000000000000) (-38846605368 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1971039877034189 / 4000000000000) 0 (IntervalRat.scale (911 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-11138230773 / 1000000000000) (-11138230772 / 1000000000000), orderedInterval (-34163065272 / 1000000000000) (-34163065271 / 1000000000000)))) (orderedInterval (-42484807 / 1000000000000) (-42484743 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (833432190332343 / 4000000000000) 0 (IntervalRat.scale (911 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (53858475531 / 1000000000000) (53858476902 / 1000000000000), orderedInterval (-12565847313 / 1000000000000) (-12565845942 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3387855582929303 / 4000000000000) 0 (IntervalRat.scale (911 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-12681395219 / 1000000000000) (-12681395187 / 1000000000000), orderedInterval (24314512822 / 1000000000000) (24314512854 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2262930522401977 / 4000000000000) 0 (IntervalRat.scale (911 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (28778028814 / 1000000000000) (28778028815 / 1000000000000), orderedInterval (17211918777 / 1000000000000) (17211918778 / 1000000000000)))) (orderedInterval (-4042557004 / 1000000000000) (-4042556867 / 1000000000000))) = true
  rfl'

theorem compactCertificate584_chunkChecks0 :
    compactCertificate584.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate584.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate584_chunkChecks0_0
    compactCertificate584_chunkChecks0_1 compactCertificate584_chunkChecks0_2

theorem compactCertificate584_chunkChecks1_0 :
    compactCertificate584.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (911 / 2) 1 (IntervalRat.scale (911 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-25597330043 / 1000000000000) (-25597330042 / 1000000000000), orderedInterval (-27219016074 / 1000000000000) (-27219016073 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1342076953537811 / 4000000000000) 1 (IntervalRat.scale (911 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-6675197792 / 1000000000000) (-6675197791 / 1000000000000), orderedInterval (-43034916750 / 1000000000000) (-43034916749 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (434000112062963 / 800000000000) 1 (IntervalRat.scale (911 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (7148470389 / 1000000000000) (7148470394 / 1000000000000), orderedInterval (-33508710634 / 1000000000000) (-33508710629 / 1000000000000)))) (orderedInterval (-13425938035 / 1000000000000) (-13425937998 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (391614707854777 / 4000000000000) 1 (IntervalRat.scale (911 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-77664999259 / 1000000000000) (-77664999257 / 1000000000000), orderedInterval (-21296381920 / 1000000000000) (-21296381919 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (1051932190463269 / 4000000000000) 1 (IntervalRat.scale (911 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-6173806721 / 1000000000000) (-6173806708 / 1000000000000), orderedInterval (48824153253 / 1000000000000) (48824153266 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2856200527061073 / 4000000000000) 1 (IntervalRat.scale (911 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29633350934 / 1000000000000) (-29633343742 / 1000000000000), orderedInterval (3684929963 / 1000000000000) (3684937155 / 1000000000000)))) (orderedInterval (668222994 / 1000000000000) (668223858 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (2103864380927449 / 4000000000000) 1 (IntervalRat.scale (911 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-29938361024 / 1000000000000) (-29938262107 / 1000000000000), orderedInterval (17750681772 / 1000000000000) (17750780689 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3605007475938877 / 4000000000000) 1 (IntervalRat.scale (911 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-10350735615 / 1000000000000) (-10350735614 / 1000000000000), orderedInterval (-24473536787 / 1000000000000) (-24473536786 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2655432190332343 / 4000000000000) 1 (IntervalRat.scale (911 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-30371838302 / 1000000000000) (-30371826664 / 1000000000000), orderedInterval (6066151592 / 1000000000000) (6066163230 / 1000000000000)))) (orderedInterval (1707237700 / 1000000000000) (1707238155 / 1000000000000))) = true
  rfl'

theorem compactCertificate584_chunkChecks1_1 :
    compactCertificate584.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (4074115855004089 / 4000000000000) 1 (IntervalRat.scale (911 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (24781373331 / 1000000000000) (24781375776 / 1000000000000), orderedInterval (3292657050 / 1000000000000) (3292659495 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2352191885596081 / 4000000000000) 1 (IntervalRat.scale (911 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-32142042699 / 1000000000000) (-32142042647 / 1000000000000), orderedInterval (-7007377581 / 1000000000000) (-7007377529 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (4174005778014629 / 4000000000000) 1 (IntervalRat.scale (911 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (23648321213 / 1000000000000) (23648321638 / 1000000000000), orderedInterval (7118691637 / 1000000000000) (7118692061 / 1000000000000)))) (orderedInterval (339783142 / 1000000000000) (339784630 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3899897635610201 / 4000000000000) 1 (IntervalRat.scale (911 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (24448006991 / 1000000000000) (24448116027 / 1000000000000), orderedInterval (-7445804370 / 1000000000000) (-7445695334 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2783150972069033 / 4000000000000) 1 (IntervalRat.scale (911 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-22935473935 / 1000000000000) (-22935464933 / 1000000000000), orderedInterval (19737704622 / 1000000000000) (19737713624 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (3155796571389807 / 4000000000000) 1 (IntervalRat.scale (911 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-26420140766 / 1000000000000) (-26420140744 / 1000000000000), orderedInterval (-10418639358 / 1000000000000) (-10418639337 / 1000000000000)))) (orderedInterval (3230090969 / 1000000000000) (3230096571 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2630974172893183 / 4000000000000) 1 (IntervalRat.scale (911 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-29060394692 / 1000000000000) (-29060340534 / 1000000000000), orderedInterval (11129685681 / 1000000000000) (11129739839 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2324545471192843 / 4000000000000) 1 (IntervalRat.scale (911 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-21995693246 / 1000000000000) (-21995693245 / 1000000000000), orderedInterval (-24712907216 / 1000000000000) (-24712907215 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (673743881063457 / 800000000000) 1 (IntervalRat.scale (911 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (23402910148 / 1000000000000) (23402910150 / 1000000000000), orderedInterval (14416031677 / 1000000000000) (14416031679 / 1000000000000)))) (orderedInterval (2672347124 / 1000000000000) (2672348091 / 1000000000000))) = true
  rfl'

theorem compactCertificate584_chunkChecks1_2 :
    compactCertificate584.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1863611032219379 / 4000000000000) 1 (IntervalRat.scale (911 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (36484833142 / 1000000000000) (36484835990 / 1000000000000), orderedInterval (-5978692033 / 1000000000000) (-5978689184 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1579803710939419 / 4000000000000) 1 (IntervalRat.scale (911 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-4194462920 / 1000000000000) (-4194462917 / 1000000000000), orderedInterval (39934041884 / 1000000000000) (39934041887 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (988567809667657 / 4000000000000) 1 (IntervalRat.scale (911 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (12997460220 / 1000000000000) (12997460327 / 1000000000000), orderedInterval (-49087463326 / 1000000000000) (-49087463219 / 1000000000000)))) (orderedInterval (-1849093180 / 1000000000000) (-1849092606 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (531655055867319 / 4000000000000) 1 (IntervalRat.scale (911 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (68082797426 / 1000000000000) (68082797922 / 1000000000000), orderedInterval (-12682753760 / 1000000000000) (-12682753264 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1443546898318957 / 4000000000000) 1 (IntervalRat.scale (911 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-15914524881 / 1000000000000) (-15914524880 / 1000000000000), orderedInterval (-38846605369 / 1000000000000) (-38846605368 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1971039877034189 / 4000000000000) 1 (IntervalRat.scale (911 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-11138230773 / 1000000000000) (-11138230772 / 1000000000000), orderedInterval (-34163065272 / 1000000000000) (-34163065271 / 1000000000000)))) (orderedInterval (3598973537 / 1000000000000) (3598973589 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (833432190332343 / 4000000000000) 1 (IntervalRat.scale (911 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (53858475531 / 1000000000000) (53858476902 / 1000000000000), orderedInterval (-12565847313 / 1000000000000) (-12565845942 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3387855582929303 / 4000000000000) 1 (IntervalRat.scale (911 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-12681395219 / 1000000000000) (-12681395187 / 1000000000000), orderedInterval (24314512822 / 1000000000000) (24314512854 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2262930522401977 / 4000000000000) 1 (IntervalRat.scale (911 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (28778028814 / 1000000000000) (28778028815 / 1000000000000), orderedInterval (17211918777 / 1000000000000) (17211918778 / 1000000000000)))) (orderedInterval (-7725831201 / 1000000000000) (-7725831015 / 1000000000000))) = true
  rfl'

theorem compactCertificate584_chunkChecks1 :
    compactCertificate584.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate584.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate584_chunkChecks1_0
    compactCertificate584_chunkChecks1_1 compactCertificate584_chunkChecks1_2

theorem compactCertificate584_chunkChecks2_0 :
    compactCertificate584.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (911 / 2) 2 (IntervalRat.scale (911 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-25597330043 / 1000000000000) (-25597330042 / 1000000000000), orderedInterval (-27219016074 / 1000000000000) (-27219016073 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1342076953537811 / 4000000000000) 2 (IntervalRat.scale (911 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-6675197792 / 1000000000000) (-6675197791 / 1000000000000), orderedInterval (-43034916750 / 1000000000000) (-43034916749 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (434000112062963 / 800000000000) 2 (IntervalRat.scale (911 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (7148470389 / 1000000000000) (7148470394 / 1000000000000), orderedInterval (-33508710634 / 1000000000000) (-33508710629 / 1000000000000)))) (orderedInterval (9614084488 / 1000000000000) (9614084530 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (391614707854777 / 4000000000000) 2 (IntervalRat.scale (911 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-77664999259 / 1000000000000) (-77664999257 / 1000000000000), orderedInterval (-21296381920 / 1000000000000) (-21296381919 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (1051932190463269 / 4000000000000) 2 (IntervalRat.scale (911 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-6173806721 / 1000000000000) (-6173806708 / 1000000000000), orderedInterval (48824153253 / 1000000000000) (48824153266 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2856200527061073 / 4000000000000) 2 (IntervalRat.scale (911 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29633350934 / 1000000000000) (-29633343742 / 1000000000000), orderedInterval (3684929963 / 1000000000000) (3684937155 / 1000000000000)))) (orderedInterval (-5142130576 / 1000000000000) (-5142129232 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (2103864380927449 / 4000000000000) 2 (IntervalRat.scale (911 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-29938361024 / 1000000000000) (-29938262107 / 1000000000000), orderedInterval (17750681772 / 1000000000000) (17750780689 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3605007475938877 / 4000000000000) 2 (IntervalRat.scale (911 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-10350735615 / 1000000000000) (-10350735614 / 1000000000000), orderedInterval (-24473536787 / 1000000000000) (-24473536786 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2655432190332343 / 4000000000000) 2 (IntervalRat.scale (911 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-30371838302 / 1000000000000) (-30371826664 / 1000000000000), orderedInterval (6066151592 / 1000000000000) (6066163230 / 1000000000000)))) (orderedInterval (305545440 / 1000000000000) (305546118 / 1000000000000))) = true
  rfl'

theorem compactCertificate584_chunkChecks2_1 :
    compactCertificate584.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (4074115855004089 / 4000000000000) 2 (IntervalRat.scale (911 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (24781373331 / 1000000000000) (24781375776 / 1000000000000), orderedInterval (3292657050 / 1000000000000) (3292659495 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2352191885596081 / 4000000000000) 2 (IntervalRat.scale (911 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-32142042699 / 1000000000000) (-32142042647 / 1000000000000), orderedInterval (-7007377581 / 1000000000000) (-7007377529 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (4174005778014629 / 4000000000000) 2 (IntervalRat.scale (911 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (23648321213 / 1000000000000) (23648321638 / 1000000000000), orderedInterval (7118691637 / 1000000000000) (7118692061 / 1000000000000)))) (orderedInterval (8342023888 / 1000000000000) (8342027188 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3899897635610201 / 4000000000000) 2 (IntervalRat.scale (911 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (24448006991 / 1000000000000) (24448116027 / 1000000000000), orderedInterval (-7445804370 / 1000000000000) (-7445695334 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2783150972069033 / 4000000000000) 2 (IntervalRat.scale (911 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-22935473935 / 1000000000000) (-22935464933 / 1000000000000), orderedInterval (19737704622 / 1000000000000) (19737713624 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (3155796571389807 / 4000000000000) 2 (IntervalRat.scale (911 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-26420140766 / 1000000000000) (-26420140744 / 1000000000000), orderedInterval (-10418639358 / 1000000000000) (-10418639337 / 1000000000000)))) (orderedInterval (6674548670 / 1000000000000) (6674559833 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2630974172893183 / 4000000000000) 2 (IntervalRat.scale (911 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-29060394692 / 1000000000000) (-29060340534 / 1000000000000), orderedInterval (11129685681 / 1000000000000) (11129739839 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2324545471192843 / 4000000000000) 2 (IntervalRat.scale (911 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-21995693246 / 1000000000000) (-21995693245 / 1000000000000), orderedInterval (-24712907216 / 1000000000000) (-24712907215 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (673743881063457 / 800000000000) 2 (IntervalRat.scale (911 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (23402910148 / 1000000000000) (23402910150 / 1000000000000), orderedInterval (14416031677 / 1000000000000) (14416031679 / 1000000000000)))) (orderedInterval (-3403387019 / 1000000000000) (-3403385618 / 1000000000000))) = true
  rfl'

theorem compactCertificate584_chunkChecks2_2 :
    compactCertificate584.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1863611032219379 / 4000000000000) 2 (IntervalRat.scale (911 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (36484833142 / 1000000000000) (36484835990 / 1000000000000), orderedInterval (-5978692033 / 1000000000000) (-5978689184 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1579803710939419 / 4000000000000) 2 (IntervalRat.scale (911 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-4194462920 / 1000000000000) (-4194462917 / 1000000000000), orderedInterval (39934041884 / 1000000000000) (39934041887 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (988567809667657 / 4000000000000) 2 (IntervalRat.scale (911 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (12997460220 / 1000000000000) (12997460327 / 1000000000000), orderedInterval (-49087463326 / 1000000000000) (-49087463219 / 1000000000000)))) (orderedInterval (5804160126 / 1000000000000) (5804160706 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (531655055867319 / 4000000000000) 2 (IntervalRat.scale (911 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (68082797426 / 1000000000000) (68082797922 / 1000000000000), orderedInterval (-12682753760 / 1000000000000) (-12682753264 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1443546898318957 / 4000000000000) 2 (IntervalRat.scale (911 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-15914524881 / 1000000000000) (-15914524880 / 1000000000000), orderedInterval (-38846605369 / 1000000000000) (-38846605368 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1971039877034189 / 4000000000000) 2 (IntervalRat.scale (911 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-11138230773 / 1000000000000) (-11138230772 / 1000000000000), orderedInterval (-34163065272 / 1000000000000) (-34163065271 / 1000000000000)))) (orderedInterval (-1126483745 / 1000000000000) (-1126483695 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (833432190332343 / 4000000000000) 2 (IntervalRat.scale (911 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (53858475531 / 1000000000000) (53858476902 / 1000000000000), orderedInterval (-12565847313 / 1000000000000) (-12565845942 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3387855582929303 / 4000000000000) 2 (IntervalRat.scale (911 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-12681395219 / 1000000000000) (-12681395187 / 1000000000000), orderedInterval (24314512822 / 1000000000000) (24314512854 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2262930522401977 / 4000000000000) 2 (IntervalRat.scale (911 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (28778028814 / 1000000000000) (28778028815 / 1000000000000), orderedInterval (17211918777 / 1000000000000) (17211918778 / 1000000000000)))) (orderedInterval (4709120670 / 1000000000000) (4709120943 / 1000000000000))) = true
  rfl'

theorem compactCertificate584_chunkChecks2 :
    compactCertificate584.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate584.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate584_chunkChecks2_0
    compactCertificate584_chunkChecks2_1 compactCertificate584_chunkChecks2_2

theorem compactCertificate584_chunkChecks3_0 :
    compactCertificate584.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (911 / 2) 3 (IntervalRat.scale (911 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-25597330043 / 1000000000000) (-25597330042 / 1000000000000), orderedInterval (-27219016074 / 1000000000000) (-27219016073 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1342076953537811 / 4000000000000) 3 (IntervalRat.scale (911 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-6675197792 / 1000000000000) (-6675197791 / 1000000000000), orderedInterval (-43034916750 / 1000000000000) (-43034916749 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (434000112062963 / 800000000000) 3 (IntervalRat.scale (911 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (7148470389 / 1000000000000) (7148470394 / 1000000000000), orderedInterval (-33508710634 / 1000000000000) (-33508710629 / 1000000000000)))) (orderedInterval (14249688396 / 1000000000000) (14249688445 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (391614707854777 / 4000000000000) 3 (IntervalRat.scale (911 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-77664999259 / 1000000000000) (-77664999257 / 1000000000000), orderedInterval (-21296381920 / 1000000000000) (-21296381919 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (1051932190463269 / 4000000000000) 3 (IntervalRat.scale (911 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-6173806721 / 1000000000000) (-6173806708 / 1000000000000), orderedInterval (48824153253 / 1000000000000) (48824153266 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2856200527061073 / 4000000000000) 3 (IntervalRat.scale (911 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29633350934 / 1000000000000) (-29633343742 / 1000000000000), orderedInterval (3684929963 / 1000000000000) (3684937155 / 1000000000000)))) (orderedInterval (675077624 / 1000000000000) (675079726 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (2103864380927449 / 4000000000000) 3 (IntervalRat.scale (911 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-29938361024 / 1000000000000) (-29938262107 / 1000000000000), orderedInterval (17750681772 / 1000000000000) (17750780689 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3605007475938877 / 4000000000000) 3 (IntervalRat.scale (911 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-10350735615 / 1000000000000) (-10350735614 / 1000000000000), orderedInterval (-24473536787 / 1000000000000) (-24473536786 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2655432190332343 / 4000000000000) 3 (IntervalRat.scale (911 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-30371838302 / 1000000000000) (-30371826664 / 1000000000000), orderedInterval (6066151592 / 1000000000000) (6066163230 / 1000000000000)))) (orderedInterval (-6301620501 / 1000000000000) (-6301619484 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate584_chunkChecks3_1 :
    compactCertificate584.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (4074115855004089 / 4000000000000) 3 (IntervalRat.scale (911 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (24781373331 / 1000000000000) (24781375776 / 1000000000000), orderedInterval (3292657050 / 1000000000000) (3292659495 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2352191885596081 / 4000000000000) 3 (IntervalRat.scale (911 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-32142042699 / 1000000000000) (-32142042647 / 1000000000000), orderedInterval (-7007377581 / 1000000000000) (-7007377529 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (4174005778014629 / 4000000000000) 3 (IntervalRat.scale (911 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (23648321213 / 1000000000000) (23648321638 / 1000000000000), orderedInterval (7118691637 / 1000000000000) (7118692061 / 1000000000000)))) (orderedInterval (-4526842566 / 1000000000000) (-4526835213 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3899897635610201 / 4000000000000) 3 (IntervalRat.scale (911 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (24448006991 / 1000000000000) (24448116027 / 1000000000000), orderedInterval (-7445804370 / 1000000000000) (-7445695334 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2783150972069033 / 4000000000000) 3 (IntervalRat.scale (911 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-22935473935 / 1000000000000) (-22935464933 / 1000000000000), orderedInterval (19737704622 / 1000000000000) (19737713624 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (3155796571389807 / 4000000000000) 3 (IntervalRat.scale (911 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-26420140766 / 1000000000000) (-26420140744 / 1000000000000), orderedInterval (-10418639358 / 1000000000000) (-10418639337 / 1000000000000)))) (orderedInterval (-8259255836 / 1000000000000) (-8259233226 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2630974172893183 / 4000000000000) 3 (IntervalRat.scale (911 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-29060394692 / 1000000000000) (-29060340534 / 1000000000000), orderedInterval (11129685681 / 1000000000000) (11129739839 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2324545471192843 / 4000000000000) 3 (IntervalRat.scale (911 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-21995693246 / 1000000000000) (-21995693245 / 1000000000000), orderedInterval (-24712907216 / 1000000000000) (-24712907215 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (673743881063457 / 800000000000) 3 (IntervalRat.scale (911 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (23402910148 / 1000000000000) (23402910150 / 1000000000000), orderedInterval (14416031677 / 1000000000000) (14416031679 / 1000000000000)))) (orderedInterval (-5649338565 / 1000000000000) (-5649336534 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate584_chunkChecks3_2 :
    compactCertificate584.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1863611032219379 / 4000000000000) 3 (IntervalRat.scale (911 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (36484833142 / 1000000000000) (36484835990 / 1000000000000), orderedInterval (-5978692033 / 1000000000000) (-5978689184 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1579803710939419 / 4000000000000) 3 (IntervalRat.scale (911 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-4194462920 / 1000000000000) (-4194462917 / 1000000000000), orderedInterval (39934041884 / 1000000000000) (39934041887 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (988567809667657 / 4000000000000) 3 (IntervalRat.scale (911 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (12997460220 / 1000000000000) (12997460327 / 1000000000000), orderedInterval (-49087463326 / 1000000000000) (-49087463219 / 1000000000000)))) (orderedInterval (692957996 / 1000000000000) (692958583 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (531655055867319 / 4000000000000) 3 (IntervalRat.scale (911 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (68082797426 / 1000000000000) (68082797922 / 1000000000000), orderedInterval (-12682753760 / 1000000000000) (-12682753264 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1443546898318957 / 4000000000000) 3 (IntervalRat.scale (911 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-15914524881 / 1000000000000) (-15914524880 / 1000000000000), orderedInterval (-38846605369 / 1000000000000) (-38846605368 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1971039877034189 / 4000000000000) 3 (IntervalRat.scale (911 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-11138230773 / 1000000000000) (-11138230772 / 1000000000000), orderedInterval (-34163065272 / 1000000000000) (-34163065271 / 1000000000000)))) (orderedInterval (-3756353184 / 1000000000000) (-3756353133 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (833432190332343 / 4000000000000) 3 (IntervalRat.scale (911 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (53858475531 / 1000000000000) (53858476902 / 1000000000000), orderedInterval (-12565847313 / 1000000000000) (-12565845942 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3387855582929303 / 4000000000000) 3 (IntervalRat.scale (911 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-12681395219 / 1000000000000) (-12681395187 / 1000000000000), orderedInterval (24314512822 / 1000000000000) (24314512854 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2262930522401977 / 4000000000000) 3 (IntervalRat.scale (911 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (28778028814 / 1000000000000) (28778028815 / 1000000000000), orderedInterval (17211918777 / 1000000000000) (17211918778 / 1000000000000)))) (orderedInterval (18908201431 / 1000000000000) (18908201852 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate584_chunkChecks3 :
    compactCertificate584.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate584.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate584_chunkChecks3_0
    compactCertificate584_chunkChecks3_1 compactCertificate584_chunkChecks3_2

theorem compactCertificate584_chunkChecks4_0 :
    compactCertificate584.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (911 / 2) 4 (IntervalRat.scale (911 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-25597330043 / 1000000000000) (-25597330042 / 1000000000000), orderedInterval (-27219016074 / 1000000000000) (-27219016073 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1342076953537811 / 4000000000000) 4 (IntervalRat.scale (911 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-6675197792 / 1000000000000) (-6675197791 / 1000000000000), orderedInterval (-43034916750 / 1000000000000) (-43034916749 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (434000112062963 / 800000000000) 4 (IntervalRat.scale (911 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (7148470389 / 1000000000000) (7148470394 / 1000000000000), orderedInterval (-33508710634 / 1000000000000) (-33508710629 / 1000000000000)))) (orderedInterval (-9382687699 / 1000000000000) (-9382687642 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (391614707854777 / 4000000000000) 4 (IntervalRat.scale (911 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-77664999259 / 1000000000000) (-77664999257 / 1000000000000), orderedInterval (-21296381920 / 1000000000000) (-21296381919 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (1051932190463269 / 4000000000000) 4 (IntervalRat.scale (911 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-6173806721 / 1000000000000) (-6173806708 / 1000000000000), orderedInterval (48824153253 / 1000000000000) (48824153266 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2856200527061073 / 4000000000000) 4 (IntervalRat.scale (911 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29633350934 / 1000000000000) (-29633343742 / 1000000000000), orderedInterval (3684929963 / 1000000000000) (3684937155 / 1000000000000)))) (orderedInterval (12695554410 / 1000000000000) (12695557705 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (2103864380927449 / 4000000000000) 4 (IntervalRat.scale (911 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-29938361024 / 1000000000000) (-29938262107 / 1000000000000), orderedInterval (17750681772 / 1000000000000) (17750780689 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3605007475938877 / 4000000000000) 4 (IntervalRat.scale (911 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-10350735615 / 1000000000000) (-10350735614 / 1000000000000), orderedInterval (-24473536787 / 1000000000000) (-24473536786 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2655432190332343 / 4000000000000) 4 (IntervalRat.scale (911 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-30371838302 / 1000000000000) (-30371826664 / 1000000000000), orderedInterval (6066151592 / 1000000000000) (6066163230 / 1000000000000)))) (orderedInterval (1608880603 / 1000000000000) (1608882143 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate584_chunkChecks4_1 :
    compactCertificate584.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (4074115855004089 / 4000000000000) 4 (IntervalRat.scale (911 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (24781373331 / 1000000000000) (24781375776 / 1000000000000), orderedInterval (3292657050 / 1000000000000) (3292659495 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2352191885596081 / 4000000000000) 4 (IntervalRat.scale (911 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-32142042699 / 1000000000000) (-32142042647 / 1000000000000), orderedInterval (-7007377581 / 1000000000000) (-7007377529 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (4174005778014629 / 4000000000000) 4 (IntervalRat.scale (911 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (23648321213 / 1000000000000) (23648321638 / 1000000000000), orderedInterval (7118691637 / 1000000000000) (7118692061 / 1000000000000)))) (orderedInterval (-24084816953 / 1000000000000) (-24084800491 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3899897635610201 / 4000000000000) 4 (IntervalRat.scale (911 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (24448006991 / 1000000000000) (24448116027 / 1000000000000), orderedInterval (-7445804370 / 1000000000000) (-7445695334 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2783150972069033 / 4000000000000) 4 (IntervalRat.scale (911 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-22935473935 / 1000000000000) (-22935464933 / 1000000000000), orderedInterval (19737704622 / 1000000000000) (19737713624 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (3155796571389807 / 4000000000000) 4 (IntervalRat.scale (911 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-26420140766 / 1000000000000) (-26420140744 / 1000000000000), orderedInterval (-10418639358 / 1000000000000) (-10418639337 / 1000000000000)))) (orderedInterval (-19832921272 / 1000000000000) (-19832874791 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2630974172893183 / 4000000000000) 4 (IntervalRat.scale (911 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-29060394692 / 1000000000000) (-29060340534 / 1000000000000), orderedInterval (11129685681 / 1000000000000) (11129739839 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2324545471192843 / 4000000000000) 4 (IntervalRat.scale (911 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-21995693246 / 1000000000000) (-21995693245 / 1000000000000), orderedInterval (-24712907216 / 1000000000000) (-24712907215 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (673743881063457 / 800000000000) 4 (IntervalRat.scale (911 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (23402910148 / 1000000000000) (23402910150 / 1000000000000), orderedInterval (14416031677 / 1000000000000) (14416031679 / 1000000000000)))) (orderedInterval (8903067941 / 1000000000000) (8903070898 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate584_chunkChecks4_2 :
    compactCertificate584.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1863611032219379 / 4000000000000) 4 (IntervalRat.scale (911 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (36484833142 / 1000000000000) (36484835990 / 1000000000000), orderedInterval (-5978692033 / 1000000000000) (-5978689184 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1579803710939419 / 4000000000000) 4 (IntervalRat.scale (911 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-4194462920 / 1000000000000) (-4194462917 / 1000000000000), orderedInterval (39934041884 / 1000000000000) (39934041887 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (988567809667657 / 4000000000000) 4 (IntervalRat.scale (911 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (12997460220 / 1000000000000) (12997460327 / 1000000000000), orderedInterval (-49087463326 / 1000000000000) (-49087463219 / 1000000000000)))) (orderedInterval (-6217260647 / 1000000000000) (-6217260050 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (531655055867319 / 4000000000000) 4 (IntervalRat.scale (911 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (68082797426 / 1000000000000) (68082797922 / 1000000000000), orderedInterval (-12682753760 / 1000000000000) (-12682753264 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1443546898318957 / 4000000000000) 4 (IntervalRat.scale (911 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-15914524881 / 1000000000000) (-15914524880 / 1000000000000), orderedInterval (-38846605369 / 1000000000000) (-38846605368 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1971039877034189 / 4000000000000) 4 (IntervalRat.scale (911 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-11138230773 / 1000000000000) (-11138230772 / 1000000000000), orderedInterval (-34163065272 / 1000000000000) (-34163065271 / 1000000000000)))) (orderedInterval (1318743565 / 1000000000000) (1318743618 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (833432190332343 / 4000000000000) 4 (IntervalRat.scale (911 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (53858475531 / 1000000000000) (53858476902 / 1000000000000), orderedInterval (-12565847313 / 1000000000000) (-12565845942 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3387855582929303 / 4000000000000) 4 (IntervalRat.scale (911 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-12681395219 / 1000000000000) (-12681395187 / 1000000000000), orderedInterval (24314512822 / 1000000000000) (24314512854 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2262930522401977 / 4000000000000) 4 (IntervalRat.scale (911 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (28778028814 / 1000000000000) (28778028815 / 1000000000000), orderedInterval (17211918777 / 1000000000000) (17211918778 / 1000000000000)))) (orderedInterval (-577346481 / 1000000000000) (-577345801 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate584_chunkChecks4 :
    compactCertificate584.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate584.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate584_chunkChecks4_0
    compactCertificate584_chunkChecks4_1 compactCertificate584_chunkChecks4_2

theorem compactCertificate584_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate584.chunkCheck r b = true :=
  compactCertificate584.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate584_chunkChecks0
    · exact compactCertificate584_chunkChecks1
    · exact compactCertificate584_chunkChecks2
    · exact compactCertificate584_chunkChecks3
    · exact compactCertificate584_chunkChecks4)

theorem compactCertificate584_coefficient0 :
    compactCertificate584.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate584_coefficient1 :
    compactCertificate584.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate584_coefficient2 :
    compactCertificate584.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate584_coefficient3 :
    compactCertificate584.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate584_coefficient4 :
    compactCertificate584.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate584_coefficients : ∀ r : Fin 5,
    compactCertificate584.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate584_coefficient0
  · exact compactCertificate584_coefficient1
  · exact compactCertificate584_coefficient2
  · exact compactCertificate584_coefficient3
  · exact compactCertificate584_coefficient4

theorem compactCertificate584_lower : (1 : ℚ) ≤ compactCertificate584.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate584, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate584_proves {t : ℝ} (ht : t ∈ compactCertificate584.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate584.proves compactCertificate584_states compactCertificate584_chunks
    compactCertificate584_coefficients compactCertificate584_lower ht

end Erdos232
