/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate400 : CompactCertificate where
  left := 271
  right := 272
  center := 543 / 2
  grid := fun i =>
    match i.val with
    | 0 => 86
    | 1 => 64
    | 2 => 103
    | 3 => 19
    | 4 => 50
    | 5 => 136
    | 6 => 100
    | 7 => 171
    | 8 => 126
    | 9 => 193
    | 10 => 112
    | 11 => 198
    | 12 => 185
    | 13 => 132
    | 14 => 150
    | 15 => 125
    | 16 => 110
    | 17 => 160
    | 18 => 88
    | 19 => 75
    | 20 => 47
    | 21 => 25
    | 22 => 69
    | 23 => 94
    | 24 => 40
    | 25 => 161
    | _ => 107
  point := fun i =>
    match i.val with
    | 0 => 543 / 2
    | 1 => 799942684710243 / 4000000000000
    | 2 => 258685028375619 / 800000000000
    | 3 => 233421280313001 / 4000000000000
    | 4 => 627002392339797 / 4000000000000
    | 5 => 1702433464538049 / 4000000000000
    | 6 => 1254004784680137 / 4000000000000
    | 7 => 2148758572376301 / 4000000000000
    | 8 => 1582765839023559 / 4000000000000
    | 9 => 2428369823564457 / 4000000000000
    | 10 => 1402019971326753 / 4000000000000
    | 11 => 2487909042219477 / 4000000000000
    | 12 => 2324527350314313 / 4000000000000
    | 13 => 1658892401573529 / 4000000000000
    | 14 => 1881007177019391 / 4000000000000
    | 15 => 1568187679342479 / 4000000000000
    | 16 => 1385541373060059 / 4000000000000
    | 17 => 401583893981841 / 800000000000
    | 18 => 1110802184956227 / 4000000000000
    | 19 => 941639313984747 / 4000000000000
    | 20 => 589234160976441 / 4000000000000
    | 21 => 316892091477447 / 4000000000000
    | 22 => 860423672653341 / 4000000000000
    | 23 => 1174834965125757 / 4000000000000
    | 24 => 496765839023559 / 4000000000000
    | 25 => 2019325556016039 / 4000000000000
    | _ => 1348815887666601 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (41603309518 / 1000000000000) (41603353507 / 1000000000000), orderedInterval (-24855360418 / 1000000000000) (-24855316429 / 1000000000000))
    | 1 => (orderedInterval (-16213976593 / 1000000000000) (-16213976363 / 1000000000000), orderedInterval (54081653309 / 1000000000000) (54081653539 / 1000000000000))
    | 2 => (orderedInterval (-23465928838 / 1000000000000) (-23465928837 / 1000000000000), orderedInterval (-37621896136 / 1000000000000) (-37621896135 / 1000000000000))
    | 3 => (orderedInterval (54742453270 / 1000000000000) (54742463464 / 1000000000000), orderedInterval (-89423010998 / 1000000000000) (-89423000804 / 1000000000000))
    | 4 => (orderedInterval (28038720622 / 1000000000000) (28038720623 / 1000000000000), orderedInterval (57139904533 / 1000000000000) (57139904534 / 1000000000000))
    | 5 => (orderedInterval (-29388725707 / 1000000000000) (-29388691621 / 1000000000000), orderedInterval (25175934911 / 1000000000000) (25175968997 / 1000000000000))
    | 6 => (orderedInterval (5704512451 / 1000000000000) (5704512452 / 1000000000000), orderedInterval (44691442986 / 1000000000000) (44691442987 / 1000000000000))
    | 7 => (orderedInterval (-23777672171 / 1000000000000) (-23777672170 / 1000000000000), orderedInterval (-24871953939 / 1000000000000) (-24871953938 / 1000000000000))
    | 8 => (orderedInterval (23820846771 / 1000000000000) (23820846772 / 1000000000000), orderedInterval (32241355744 / 1000000000000) (32241355745 / 1000000000000))
    | 9 => (orderedInterval (-32375839793 / 1000000000000) (-32375838995 / 1000000000000), orderedInterval (-638115541 / 1000000000000) (-638114742 / 1000000000000))
    | 10 => (orderedInterval (-22938531641 / 1000000000000) (-22938529026 / 1000000000000), orderedInterval (35950928108 / 1000000000000) (35950930723 / 1000000000000))
    | 11 => (orderedInterval (21266119294 / 1000000000000) (21266119295 / 1000000000000), orderedInterval (23884663471 / 1000000000000) (23884663472 / 1000000000000))
    | 12 => (orderedInterval (-21883512587 / 1000000000000) (-21883512586 / 1000000000000), orderedInterval (-24812491643 / 1000000000000) (-24812491642 / 1000000000000))
    | 13 => (orderedInterval (28591650528 / 1000000000000) (28591650529 / 1000000000000), orderedInterval (26752937180 / 1000000000000) (26752937181 / 1000000000000))
    | 14 => (orderedInterval (-7380877147 / 1000000000000) (-7380877139 / 1000000000000), orderedInterval (36053766324 / 1000000000000) (36053766332 / 1000000000000))
    | 15 => (orderedInterval (-5340394797 / 1000000000000) (-5340394796 / 1000000000000), orderedInterval (-39934610289 / 1000000000000) (-39934610288 / 1000000000000))
    | 16 => (orderedInterval (42857898090 / 1000000000000) (42857898356 / 1000000000000), orderedInterval (-1107477315 / 1000000000000) (-1107477049 / 1000000000000))
    | 17 => (orderedInterval (3916226788 / 1000000000000) (3916226789 / 1000000000000), orderedInterval (35392165674 / 1000000000000) (35392165675 / 1000000000000))
    | 18 => (orderedInterval (43018030997 / 1000000000000) (43018052251 / 1000000000000), orderedInterval (-21099222852 / 1000000000000) (-21099201599 / 1000000000000))
    | 19 => (orderedInterval (-28291730876 / 1000000000000) (-28291730875 / 1000000000000), orderedInterval (-43573435845 / 1000000000000) (-43573435844 / 1000000000000))
    | 20 => (orderedInterval (-27895934819 / 1000000000000) (-27895934818 / 1000000000000), orderedInterval (-59432693236 / 1000000000000) (-59432693235 / 1000000000000))
    | 21 => (orderedInterval (-89159488272 / 1000000000000) (-89159488266 / 1000000000000), orderedInterval (-8722867883 / 1000000000000) (-8722867877 / 1000000000000))
    | 22 => (orderedInterval (41900328290 / 1000000000000) (41900427354 / 1000000000000), orderedInterval (-34795004896 / 1000000000000) (-34794905832 / 1000000000000))
    | 23 => (orderedInterval (-33912227206 / 1000000000000) (-33912186520 / 1000000000000), orderedInterval (31955714106 / 1000000000000) (31955754791 / 1000000000000))
    | 24 => (orderedInterval (-45455349737 / 1000000000000) (-45455322146 / 1000000000000), orderedInterval (55499675632 / 1000000000000) (55499703223 / 1000000000000))
    | 25 => (orderedInterval (6353301891 / 1000000000000) (6353301895 / 1000000000000), orderedInterval (-34944672414 / 1000000000000) (-34944672409 / 1000000000000))
    | _ => (orderedInterval (-41901725224 / 1000000000000) (-41901720779 / 1000000000000), orderedInterval (11559109749 / 1000000000000) (11559114194 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (14962005214 / 1000000000000) (14962022671 / 1000000000000)
      | 1 => orderedInterval (2519057250 / 1000000000000) (2519059817 / 1000000000000)
      | 2 => orderedInterval (1309101404 / 1000000000000) (1309101420 / 1000000000000)
      | 3 => orderedInterval (7076343354 / 1000000000000) (7076343797 / 1000000000000)
      | 4 => orderedInterval (3136124826 / 1000000000000) (3136124859 / 1000000000000)
      | 5 => orderedInterval (-2414013361 / 1000000000000) (-2414013319 / 1000000000000)
      | 6 => orderedInterval (-6185110454 / 1000000000000) (-6185106987 / 1000000000000)
      | 7 => orderedInterval (3294742807 / 1000000000000) (3294748206 / 1000000000000)
      | _ => orderedInterval (7070684486 / 1000000000000) (7070685562 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-12109961624 / 1000000000000) (-12109944165 / 1000000000000)
      | 1 => orderedInterval (-1392606329 / 1000000000000) (-1392602469 / 1000000000000)
      | 2 => orderedInterval (2653525095 / 1000000000000) (2653525122 / 1000000000000)
      | 3 => orderedInterval (11470688806 / 1000000000000) (11470689597 / 1000000000000)
      | 4 => orderedInterval (4507165305 / 1000000000000) (4507165358 / 1000000000000)
      | 5 => orderedInterval (1090399889 / 1000000000000) (1090399946 / 1000000000000)
      | 6 => orderedInterval (4539272046 / 1000000000000) (4539275585 / 1000000000000)
      | 7 => orderedInterval (-1976965157 / 1000000000000) (-1976959973 / 1000000000000)
      | _ => orderedInterval (2748605374 / 1000000000000) (2748606593 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-14410279333 / 1000000000000) (-14410261807 / 1000000000000)
      | 1 => orderedInterval (-5442820805 / 1000000000000) (-5442814779 / 1000000000000)
      | 2 => orderedInterval (-4103768857 / 1000000000000) (-4103768809 / 1000000000000)
      | 3 => orderedInterval (-41839452549 / 1000000000000) (-41839451036 / 1000000000000)
      | 4 => orderedInterval (-8247306713 / 1000000000000) (-8247306625 / 1000000000000)
      | 5 => orderedInterval (3773966363 / 1000000000000) (3773966444 / 1000000000000)
      | 6 => orderedInterval (6242762671 / 1000000000000) (6242766300 / 1000000000000)
      | 7 => orderedInterval (-2577777815 / 1000000000000) (-2577772707 / 1000000000000)
      | _ => orderedInterval (-10292225857 / 1000000000000) (-10292224374 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (13432985821 / 1000000000000) (13433003351 / 1000000000000)
      | 1 => orderedInterval (6503551123 / 1000000000000) (6503560558 / 1000000000000)
      | 2 => orderedInterval (-8339350578 / 1000000000000) (-8339350492 / 1000000000000)
      | 3 => orderedInterval (-47667079878 / 1000000000000) (-47667076820 / 1000000000000)
      | 4 => orderedInterval (-12431158305 / 1000000000000) (-12431158157 / 1000000000000)
      | 5 => orderedInterval (-4484470563 / 1000000000000) (-4484470445 / 1000000000000)
      | 6 => orderedInterval (-4931642668 / 1000000000000) (-4931638960 / 1000000000000)
      | 7 => orderedInterval (2713426176 / 1000000000000) (2713431290 / 1000000000000)
      | _ => orderedInterval (-14126003837 / 1000000000000) (-14126001975 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (13575816731 / 1000000000000) (13575834329 / 1000000000000)
      | 1 => orderedInterval (12681260020 / 1000000000000) (12681274841 / 1000000000000)
      | 2 => orderedInterval (13898944583 / 1000000000000) (13898944743 / 1000000000000)
      | 3 => orderedInterval (222716257720 / 1000000000000) (222716264148 / 1000000000000)
      | 4 => orderedInterval (23440360123 / 1000000000000) (23440360380 / 1000000000000)
      | 5 => orderedInterval (-5561401239 / 1000000000000) (-5561401061 / 1000000000000)
      | 6 => orderedInterval (-6665656621 / 1000000000000) (-6665652816 / 1000000000000)
      | 7 => orderedInterval (3176884060 / 1000000000000) (3176889285 / 1000000000000)
      | _ => orderedInterval (12617348153 / 1000000000000) (12617350547 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (30768935526 / 1000000000000) (30768966026 / 1000000000000)
    | 1 => orderedInterval (11530123405 / 1000000000000) (11530155594 / 1000000000000)
    | 2 => orderedInterval (-76896902895 / 1000000000000) (-76896867393 / 1000000000000)
    | 3 => orderedInterval (-69329742709 / 1000000000000) (-69329701650 / 1000000000000)
    | _ => orderedInterval (289879813530 / 1000000000000) (289879864396 / 1000000000000)

theorem compactCertificate400_stateChecks0 :
    compactCertificate400.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 86 12 (543 / 2)) (orderedInterval (41603309518 / 1000000000000) (41603353507 / 1000000000000), orderedInterval (-24855360418 / 1000000000000) (-24855316429 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (799942684710243 / 4000000000000)) (orderedInterval (-16213976593 / 1000000000000) (-16213976363 / 1000000000000), orderedInterval (54081653309 / 1000000000000) (54081653539 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 103 12 (258685028375619 / 800000000000)) (orderedInterval (-23465928838 / 1000000000000) (-23465928837 / 1000000000000), orderedInterval (-37621896136 / 1000000000000) (-37621896135 / 1000000000000))) = true
  rfl'

theorem compactCertificate400_stateChecks1 :
    compactCertificate400.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 19 12 (233421280313001 / 4000000000000)) (orderedInterval (54742453270 / 1000000000000) (54742463464 / 1000000000000), orderedInterval (-89423010998 / 1000000000000) (-89423000804 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 50 12 (627002392339797 / 4000000000000)) (orderedInterval (28038720622 / 1000000000000) (28038720623 / 1000000000000), orderedInterval (57139904533 / 1000000000000) (57139904534 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 136 12 (1702433464538049 / 4000000000000)) (orderedInterval (-29388725707 / 1000000000000) (-29388691621 / 1000000000000), orderedInterval (25175934911 / 1000000000000) (25175968997 / 1000000000000))) = true
  rfl'

theorem compactCertificate400_stateChecks2 :
    compactCertificate400.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 100 12 (1254004784680137 / 4000000000000)) (orderedInterval (5704512451 / 1000000000000) (5704512452 / 1000000000000), orderedInterval (44691442986 / 1000000000000) (44691442987 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 171 12 (2148758572376301 / 4000000000000)) (orderedInterval (-23777672171 / 1000000000000) (-23777672170 / 1000000000000), orderedInterval (-24871953939 / 1000000000000) (-24871953938 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 126 12 (1582765839023559 / 4000000000000)) (orderedInterval (23820846771 / 1000000000000) (23820846772 / 1000000000000), orderedInterval (32241355744 / 1000000000000) (32241355745 / 1000000000000))) = true
  rfl'

theorem compactCertificate400_stateChecks3 :
    compactCertificate400.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 193 12 (2428369823564457 / 4000000000000)) (orderedInterval (-32375839793 / 1000000000000) (-32375838995 / 1000000000000), orderedInterval (-638115541 / 1000000000000) (-638114742 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 112 12 (1402019971326753 / 4000000000000)) (orderedInterval (-22938531641 / 1000000000000) (-22938529026 / 1000000000000), orderedInterval (35950928108 / 1000000000000) (35950930723 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 198 12 (2487909042219477 / 4000000000000)) (orderedInterval (21266119294 / 1000000000000) (21266119295 / 1000000000000), orderedInterval (23884663471 / 1000000000000) (23884663472 / 1000000000000))) = true
  rfl'

theorem compactCertificate400_stateChecks4 :
    compactCertificate400.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 185 12 (2324527350314313 / 4000000000000)) (orderedInterval (-21883512587 / 1000000000000) (-21883512586 / 1000000000000), orderedInterval (-24812491643 / 1000000000000) (-24812491642 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 132 12 (1658892401573529 / 4000000000000)) (orderedInterval (28591650528 / 1000000000000) (28591650529 / 1000000000000), orderedInterval (26752937180 / 1000000000000) (26752937181 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 150 12 (1881007177019391 / 4000000000000)) (orderedInterval (-7380877147 / 1000000000000) (-7380877139 / 1000000000000), orderedInterval (36053766324 / 1000000000000) (36053766332 / 1000000000000))) = true
  rfl'

theorem compactCertificate400_stateChecks5 :
    compactCertificate400.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 125 12 (1568187679342479 / 4000000000000)) (orderedInterval (-5340394797 / 1000000000000) (-5340394796 / 1000000000000), orderedInterval (-39934610289 / 1000000000000) (-39934610288 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 110 12 (1385541373060059 / 4000000000000)) (orderedInterval (42857898090 / 1000000000000) (42857898356 / 1000000000000), orderedInterval (-1107477315 / 1000000000000) (-1107477049 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 160 12 (401583893981841 / 800000000000)) (orderedInterval (3916226788 / 1000000000000) (3916226789 / 1000000000000), orderedInterval (35392165674 / 1000000000000) (35392165675 / 1000000000000))) = true
  rfl'

theorem compactCertificate400_stateChecks6 :
    compactCertificate400.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 88 12 (1110802184956227 / 4000000000000)) (orderedInterval (43018030997 / 1000000000000) (43018052251 / 1000000000000), orderedInterval (-21099222852 / 1000000000000) (-21099201599 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 75 12 (941639313984747 / 4000000000000)) (orderedInterval (-28291730876 / 1000000000000) (-28291730875 / 1000000000000), orderedInterval (-43573435845 / 1000000000000) (-43573435844 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 47 12 (589234160976441 / 4000000000000)) (orderedInterval (-27895934819 / 1000000000000) (-27895934818 / 1000000000000), orderedInterval (-59432693236 / 1000000000000) (-59432693235 / 1000000000000))) = true
  rfl'

theorem compactCertificate400_stateChecks7 :
    compactCertificate400.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 25 12 (316892091477447 / 4000000000000)) (orderedInterval (-89159488272 / 1000000000000) (-89159488266 / 1000000000000), orderedInterval (-8722867883 / 1000000000000) (-8722867877 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (860423672653341 / 4000000000000)) (orderedInterval (41900328290 / 1000000000000) (41900427354 / 1000000000000), orderedInterval (-34795004896 / 1000000000000) (-34794905832 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 94 12 (1174834965125757 / 4000000000000)) (orderedInterval (-33912227206 / 1000000000000) (-33912186520 / 1000000000000), orderedInterval (31955714106 / 1000000000000) (31955754791 / 1000000000000))) = true
  rfl'

theorem compactCertificate400_stateChecks8 :
    compactCertificate400.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 40 12 (496765839023559 / 4000000000000)) (orderedInterval (-45455349737 / 1000000000000) (-45455322146 / 1000000000000), orderedInterval (55499675632 / 1000000000000) (55499703223 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 161 12 (2019325556016039 / 4000000000000)) (orderedInterval (6353301891 / 1000000000000) (6353301895 / 1000000000000), orderedInterval (-34944672414 / 1000000000000) (-34944672409 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 107 12 (1348815887666601 / 4000000000000)) (orderedInterval (-41901725224 / 1000000000000) (-41901720779 / 1000000000000), orderedInterval (11559109749 / 1000000000000) (11559114194 / 1000000000000))) = true
  rfl'

theorem compactCertificate400_states : ∀ j,
    BesselStateValid (compactCertificate400.point j) (compactCertificate400.state j) :=
  compactCertificate400.statesValid_of_checks3 compactCertificate400_stateChecks0
    compactCertificate400_stateChecks1 compactCertificate400_stateChecks2
    compactCertificate400_stateChecks3 compactCertificate400_stateChecks4
    compactCertificate400_stateChecks5 compactCertificate400_stateChecks6
    compactCertificate400_stateChecks7 compactCertificate400_stateChecks8

theorem compactCertificate400_chunkChecks0_0 :
    compactCertificate400.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (543 / 2) 0 (IntervalRat.scale (543 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (41603309518 / 1000000000000) (41603353507 / 1000000000000), orderedInterval (-24855360418 / 1000000000000) (-24855316429 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (799942684710243 / 4000000000000) 0 (IntervalRat.scale (543 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-16213976593 / 1000000000000) (-16213976363 / 1000000000000), orderedInterval (54081653309 / 1000000000000) (54081653539 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (258685028375619 / 800000000000) 0 (IntervalRat.scale (543 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-23465928838 / 1000000000000) (-23465928837 / 1000000000000), orderedInterval (-37621896136 / 1000000000000) (-37621896135 / 1000000000000)))) (orderedInterval (14962005214 / 1000000000000) (14962022671 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (233421280313001 / 4000000000000) 0 (IntervalRat.scale (543 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (54742453270 / 1000000000000) (54742463464 / 1000000000000), orderedInterval (-89423010998 / 1000000000000) (-89423000804 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (627002392339797 / 4000000000000) 0 (IntervalRat.scale (543 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (28038720622 / 1000000000000) (28038720623 / 1000000000000), orderedInterval (57139904533 / 1000000000000) (57139904534 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1702433464538049 / 4000000000000) 0 (IntervalRat.scale (543 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29388725707 / 1000000000000) (-29388691621 / 1000000000000), orderedInterval (25175934911 / 1000000000000) (25175968997 / 1000000000000)))) (orderedInterval (2519057250 / 1000000000000) (2519059817 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1254004784680137 / 4000000000000) 0 (IntervalRat.scale (543 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (5704512451 / 1000000000000) (5704512452 / 1000000000000), orderedInterval (44691442986 / 1000000000000) (44691442987 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2148758572376301 / 4000000000000) 0 (IntervalRat.scale (543 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-23777672171 / 1000000000000) (-23777672170 / 1000000000000), orderedInterval (-24871953939 / 1000000000000) (-24871953938 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1582765839023559 / 4000000000000) 0 (IntervalRat.scale (543 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (23820846771 / 1000000000000) (23820846772 / 1000000000000), orderedInterval (32241355744 / 1000000000000) (32241355745 / 1000000000000)))) (orderedInterval (1309101404 / 1000000000000) (1309101420 / 1000000000000))) = true
  rfl'

theorem compactCertificate400_chunkChecks0_1 :
    compactCertificate400.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2428369823564457 / 4000000000000) 0 (IntervalRat.scale (543 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-32375839793 / 1000000000000) (-32375838995 / 1000000000000), orderedInterval (-638115541 / 1000000000000) (-638114742 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1402019971326753 / 4000000000000) 0 (IntervalRat.scale (543 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-22938531641 / 1000000000000) (-22938529026 / 1000000000000), orderedInterval (35950928108 / 1000000000000) (35950930723 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2487909042219477 / 4000000000000) 0 (IntervalRat.scale (543 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (21266119294 / 1000000000000) (21266119295 / 1000000000000), orderedInterval (23884663471 / 1000000000000) (23884663472 / 1000000000000)))) (orderedInterval (7076343354 / 1000000000000) (7076343797 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2324527350314313 / 4000000000000) 0 (IntervalRat.scale (543 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-21883512587 / 1000000000000) (-21883512586 / 1000000000000), orderedInterval (-24812491643 / 1000000000000) (-24812491642 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1658892401573529 / 4000000000000) 0 (IntervalRat.scale (543 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (28591650528 / 1000000000000) (28591650529 / 1000000000000), orderedInterval (26752937180 / 1000000000000) (26752937181 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1881007177019391 / 4000000000000) 0 (IntervalRat.scale (543 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-7380877147 / 1000000000000) (-7380877139 / 1000000000000), orderedInterval (36053766324 / 1000000000000) (36053766332 / 1000000000000)))) (orderedInterval (3136124826 / 1000000000000) (3136124859 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1568187679342479 / 4000000000000) 0 (IntervalRat.scale (543 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-5340394797 / 1000000000000) (-5340394796 / 1000000000000), orderedInterval (-39934610289 / 1000000000000) (-39934610288 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1385541373060059 / 4000000000000) 0 (IntervalRat.scale (543 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (42857898090 / 1000000000000) (42857898356 / 1000000000000), orderedInterval (-1107477315 / 1000000000000) (-1107477049 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (401583893981841 / 800000000000) 0 (IntervalRat.scale (543 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (3916226788 / 1000000000000) (3916226789 / 1000000000000), orderedInterval (35392165674 / 1000000000000) (35392165675 / 1000000000000)))) (orderedInterval (-2414013361 / 1000000000000) (-2414013319 / 1000000000000))) = true
  rfl'

theorem compactCertificate400_chunkChecks0_2 :
    compactCertificate400.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1110802184956227 / 4000000000000) 0 (IntervalRat.scale (543 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (43018030997 / 1000000000000) (43018052251 / 1000000000000), orderedInterval (-21099222852 / 1000000000000) (-21099201599 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (941639313984747 / 4000000000000) 0 (IntervalRat.scale (543 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-28291730876 / 1000000000000) (-28291730875 / 1000000000000), orderedInterval (-43573435845 / 1000000000000) (-43573435844 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (589234160976441 / 4000000000000) 0 (IntervalRat.scale (543 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-27895934819 / 1000000000000) (-27895934818 / 1000000000000), orderedInterval (-59432693236 / 1000000000000) (-59432693235 / 1000000000000)))) (orderedInterval (-6185110454 / 1000000000000) (-6185106987 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (316892091477447 / 4000000000000) 0 (IntervalRat.scale (543 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-89159488272 / 1000000000000) (-89159488266 / 1000000000000), orderedInterval (-8722867883 / 1000000000000) (-8722867877 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (860423672653341 / 4000000000000) 0 (IntervalRat.scale (543 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (41900328290 / 1000000000000) (41900427354 / 1000000000000), orderedInterval (-34795004896 / 1000000000000) (-34794905832 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1174834965125757 / 4000000000000) 0 (IntervalRat.scale (543 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-33912227206 / 1000000000000) (-33912186520 / 1000000000000), orderedInterval (31955714106 / 1000000000000) (31955754791 / 1000000000000)))) (orderedInterval (3294742807 / 1000000000000) (3294748206 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (496765839023559 / 4000000000000) 0 (IntervalRat.scale (543 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-45455349737 / 1000000000000) (-45455322146 / 1000000000000), orderedInterval (55499675632 / 1000000000000) (55499703223 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2019325556016039 / 4000000000000) 0 (IntervalRat.scale (543 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (6353301891 / 1000000000000) (6353301895 / 1000000000000), orderedInterval (-34944672414 / 1000000000000) (-34944672409 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1348815887666601 / 4000000000000) 0 (IntervalRat.scale (543 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-41901725224 / 1000000000000) (-41901720779 / 1000000000000), orderedInterval (11559109749 / 1000000000000) (11559114194 / 1000000000000)))) (orderedInterval (7070684486 / 1000000000000) (7070685562 / 1000000000000))) = true
  rfl'

theorem compactCertificate400_chunkChecks0 :
    compactCertificate400.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate400.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate400_chunkChecks0_0
    compactCertificate400_chunkChecks0_1 compactCertificate400_chunkChecks0_2

theorem compactCertificate400_chunkChecks1_0 :
    compactCertificate400.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (543 / 2) 1 (IntervalRat.scale (543 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (41603309518 / 1000000000000) (41603353507 / 1000000000000), orderedInterval (-24855360418 / 1000000000000) (-24855316429 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (799942684710243 / 4000000000000) 1 (IntervalRat.scale (543 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-16213976593 / 1000000000000) (-16213976363 / 1000000000000), orderedInterval (54081653309 / 1000000000000) (54081653539 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (258685028375619 / 800000000000) 1 (IntervalRat.scale (543 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-23465928838 / 1000000000000) (-23465928837 / 1000000000000), orderedInterval (-37621896136 / 1000000000000) (-37621896135 / 1000000000000)))) (orderedInterval (-12109961624 / 1000000000000) (-12109944165 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (233421280313001 / 4000000000000) 1 (IntervalRat.scale (543 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (54742453270 / 1000000000000) (54742463464 / 1000000000000), orderedInterval (-89423010998 / 1000000000000) (-89423000804 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (627002392339797 / 4000000000000) 1 (IntervalRat.scale (543 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (28038720622 / 1000000000000) (28038720623 / 1000000000000), orderedInterval (57139904533 / 1000000000000) (57139904534 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1702433464538049 / 4000000000000) 1 (IntervalRat.scale (543 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29388725707 / 1000000000000) (-29388691621 / 1000000000000), orderedInterval (25175934911 / 1000000000000) (25175968997 / 1000000000000)))) (orderedInterval (-1392606329 / 1000000000000) (-1392602469 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1254004784680137 / 4000000000000) 1 (IntervalRat.scale (543 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (5704512451 / 1000000000000) (5704512452 / 1000000000000), orderedInterval (44691442986 / 1000000000000) (44691442987 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2148758572376301 / 4000000000000) 1 (IntervalRat.scale (543 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-23777672171 / 1000000000000) (-23777672170 / 1000000000000), orderedInterval (-24871953939 / 1000000000000) (-24871953938 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1582765839023559 / 4000000000000) 1 (IntervalRat.scale (543 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (23820846771 / 1000000000000) (23820846772 / 1000000000000), orderedInterval (32241355744 / 1000000000000) (32241355745 / 1000000000000)))) (orderedInterval (2653525095 / 1000000000000) (2653525122 / 1000000000000))) = true
  rfl'

theorem compactCertificate400_chunkChecks1_1 :
    compactCertificate400.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2428369823564457 / 4000000000000) 1 (IntervalRat.scale (543 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-32375839793 / 1000000000000) (-32375838995 / 1000000000000), orderedInterval (-638115541 / 1000000000000) (-638114742 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1402019971326753 / 4000000000000) 1 (IntervalRat.scale (543 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-22938531641 / 1000000000000) (-22938529026 / 1000000000000), orderedInterval (35950928108 / 1000000000000) (35950930723 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2487909042219477 / 4000000000000) 1 (IntervalRat.scale (543 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (21266119294 / 1000000000000) (21266119295 / 1000000000000), orderedInterval (23884663471 / 1000000000000) (23884663472 / 1000000000000)))) (orderedInterval (11470688806 / 1000000000000) (11470689597 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2324527350314313 / 4000000000000) 1 (IntervalRat.scale (543 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-21883512587 / 1000000000000) (-21883512586 / 1000000000000), orderedInterval (-24812491643 / 1000000000000) (-24812491642 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1658892401573529 / 4000000000000) 1 (IntervalRat.scale (543 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (28591650528 / 1000000000000) (28591650529 / 1000000000000), orderedInterval (26752937180 / 1000000000000) (26752937181 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1881007177019391 / 4000000000000) 1 (IntervalRat.scale (543 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-7380877147 / 1000000000000) (-7380877139 / 1000000000000), orderedInterval (36053766324 / 1000000000000) (36053766332 / 1000000000000)))) (orderedInterval (4507165305 / 1000000000000) (4507165358 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1568187679342479 / 4000000000000) 1 (IntervalRat.scale (543 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-5340394797 / 1000000000000) (-5340394796 / 1000000000000), orderedInterval (-39934610289 / 1000000000000) (-39934610288 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1385541373060059 / 4000000000000) 1 (IntervalRat.scale (543 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (42857898090 / 1000000000000) (42857898356 / 1000000000000), orderedInterval (-1107477315 / 1000000000000) (-1107477049 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (401583893981841 / 800000000000) 1 (IntervalRat.scale (543 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (3916226788 / 1000000000000) (3916226789 / 1000000000000), orderedInterval (35392165674 / 1000000000000) (35392165675 / 1000000000000)))) (orderedInterval (1090399889 / 1000000000000) (1090399946 / 1000000000000))) = true
  rfl'

theorem compactCertificate400_chunkChecks1_2 :
    compactCertificate400.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1110802184956227 / 4000000000000) 1 (IntervalRat.scale (543 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (43018030997 / 1000000000000) (43018052251 / 1000000000000), orderedInterval (-21099222852 / 1000000000000) (-21099201599 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (941639313984747 / 4000000000000) 1 (IntervalRat.scale (543 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-28291730876 / 1000000000000) (-28291730875 / 1000000000000), orderedInterval (-43573435845 / 1000000000000) (-43573435844 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (589234160976441 / 4000000000000) 1 (IntervalRat.scale (543 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-27895934819 / 1000000000000) (-27895934818 / 1000000000000), orderedInterval (-59432693236 / 1000000000000) (-59432693235 / 1000000000000)))) (orderedInterval (4539272046 / 1000000000000) (4539275585 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (316892091477447 / 4000000000000) 1 (IntervalRat.scale (543 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-89159488272 / 1000000000000) (-89159488266 / 1000000000000), orderedInterval (-8722867883 / 1000000000000) (-8722867877 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (860423672653341 / 4000000000000) 1 (IntervalRat.scale (543 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (41900328290 / 1000000000000) (41900427354 / 1000000000000), orderedInterval (-34795004896 / 1000000000000) (-34794905832 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1174834965125757 / 4000000000000) 1 (IntervalRat.scale (543 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-33912227206 / 1000000000000) (-33912186520 / 1000000000000), orderedInterval (31955714106 / 1000000000000) (31955754791 / 1000000000000)))) (orderedInterval (-1976965157 / 1000000000000) (-1976959973 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (496765839023559 / 4000000000000) 1 (IntervalRat.scale (543 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-45455349737 / 1000000000000) (-45455322146 / 1000000000000), orderedInterval (55499675632 / 1000000000000) (55499703223 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2019325556016039 / 4000000000000) 1 (IntervalRat.scale (543 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (6353301891 / 1000000000000) (6353301895 / 1000000000000), orderedInterval (-34944672414 / 1000000000000) (-34944672409 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1348815887666601 / 4000000000000) 1 (IntervalRat.scale (543 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-41901725224 / 1000000000000) (-41901720779 / 1000000000000), orderedInterval (11559109749 / 1000000000000) (11559114194 / 1000000000000)))) (orderedInterval (2748605374 / 1000000000000) (2748606593 / 1000000000000))) = true
  rfl'

theorem compactCertificate400_chunkChecks1 :
    compactCertificate400.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate400.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate400_chunkChecks1_0
    compactCertificate400_chunkChecks1_1 compactCertificate400_chunkChecks1_2

theorem compactCertificate400_chunkChecks2_0 :
    compactCertificate400.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (543 / 2) 2 (IntervalRat.scale (543 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (41603309518 / 1000000000000) (41603353507 / 1000000000000), orderedInterval (-24855360418 / 1000000000000) (-24855316429 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (799942684710243 / 4000000000000) 2 (IntervalRat.scale (543 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-16213976593 / 1000000000000) (-16213976363 / 1000000000000), orderedInterval (54081653309 / 1000000000000) (54081653539 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (258685028375619 / 800000000000) 2 (IntervalRat.scale (543 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-23465928838 / 1000000000000) (-23465928837 / 1000000000000), orderedInterval (-37621896136 / 1000000000000) (-37621896135 / 1000000000000)))) (orderedInterval (-14410279333 / 1000000000000) (-14410261807 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (233421280313001 / 4000000000000) 2 (IntervalRat.scale (543 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (54742453270 / 1000000000000) (54742463464 / 1000000000000), orderedInterval (-89423010998 / 1000000000000) (-89423000804 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (627002392339797 / 4000000000000) 2 (IntervalRat.scale (543 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (28038720622 / 1000000000000) (28038720623 / 1000000000000), orderedInterval (57139904533 / 1000000000000) (57139904534 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1702433464538049 / 4000000000000) 2 (IntervalRat.scale (543 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29388725707 / 1000000000000) (-29388691621 / 1000000000000), orderedInterval (25175934911 / 1000000000000) (25175968997 / 1000000000000)))) (orderedInterval (-5442820805 / 1000000000000) (-5442814779 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1254004784680137 / 4000000000000) 2 (IntervalRat.scale (543 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (5704512451 / 1000000000000) (5704512452 / 1000000000000), orderedInterval (44691442986 / 1000000000000) (44691442987 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2148758572376301 / 4000000000000) 2 (IntervalRat.scale (543 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-23777672171 / 1000000000000) (-23777672170 / 1000000000000), orderedInterval (-24871953939 / 1000000000000) (-24871953938 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1582765839023559 / 4000000000000) 2 (IntervalRat.scale (543 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (23820846771 / 1000000000000) (23820846772 / 1000000000000), orderedInterval (32241355744 / 1000000000000) (32241355745 / 1000000000000)))) (orderedInterval (-4103768857 / 1000000000000) (-4103768809 / 1000000000000))) = true
  rfl'

theorem compactCertificate400_chunkChecks2_1 :
    compactCertificate400.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2428369823564457 / 4000000000000) 2 (IntervalRat.scale (543 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-32375839793 / 1000000000000) (-32375838995 / 1000000000000), orderedInterval (-638115541 / 1000000000000) (-638114742 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1402019971326753 / 4000000000000) 2 (IntervalRat.scale (543 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-22938531641 / 1000000000000) (-22938529026 / 1000000000000), orderedInterval (35950928108 / 1000000000000) (35950930723 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2487909042219477 / 4000000000000) 2 (IntervalRat.scale (543 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (21266119294 / 1000000000000) (21266119295 / 1000000000000), orderedInterval (23884663471 / 1000000000000) (23884663472 / 1000000000000)))) (orderedInterval (-41839452549 / 1000000000000) (-41839451036 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2324527350314313 / 4000000000000) 2 (IntervalRat.scale (543 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-21883512587 / 1000000000000) (-21883512586 / 1000000000000), orderedInterval (-24812491643 / 1000000000000) (-24812491642 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1658892401573529 / 4000000000000) 2 (IntervalRat.scale (543 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (28591650528 / 1000000000000) (28591650529 / 1000000000000), orderedInterval (26752937180 / 1000000000000) (26752937181 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1881007177019391 / 4000000000000) 2 (IntervalRat.scale (543 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-7380877147 / 1000000000000) (-7380877139 / 1000000000000), orderedInterval (36053766324 / 1000000000000) (36053766332 / 1000000000000)))) (orderedInterval (-8247306713 / 1000000000000) (-8247306625 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1568187679342479 / 4000000000000) 2 (IntervalRat.scale (543 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-5340394797 / 1000000000000) (-5340394796 / 1000000000000), orderedInterval (-39934610289 / 1000000000000) (-39934610288 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1385541373060059 / 4000000000000) 2 (IntervalRat.scale (543 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (42857898090 / 1000000000000) (42857898356 / 1000000000000), orderedInterval (-1107477315 / 1000000000000) (-1107477049 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (401583893981841 / 800000000000) 2 (IntervalRat.scale (543 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (3916226788 / 1000000000000) (3916226789 / 1000000000000), orderedInterval (35392165674 / 1000000000000) (35392165675 / 1000000000000)))) (orderedInterval (3773966363 / 1000000000000) (3773966444 / 1000000000000))) = true
  rfl'

theorem compactCertificate400_chunkChecks2_2 :
    compactCertificate400.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1110802184956227 / 4000000000000) 2 (IntervalRat.scale (543 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (43018030997 / 1000000000000) (43018052251 / 1000000000000), orderedInterval (-21099222852 / 1000000000000) (-21099201599 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (941639313984747 / 4000000000000) 2 (IntervalRat.scale (543 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-28291730876 / 1000000000000) (-28291730875 / 1000000000000), orderedInterval (-43573435845 / 1000000000000) (-43573435844 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (589234160976441 / 4000000000000) 2 (IntervalRat.scale (543 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-27895934819 / 1000000000000) (-27895934818 / 1000000000000), orderedInterval (-59432693236 / 1000000000000) (-59432693235 / 1000000000000)))) (orderedInterval (6242762671 / 1000000000000) (6242766300 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (316892091477447 / 4000000000000) 2 (IntervalRat.scale (543 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-89159488272 / 1000000000000) (-89159488266 / 1000000000000), orderedInterval (-8722867883 / 1000000000000) (-8722867877 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (860423672653341 / 4000000000000) 2 (IntervalRat.scale (543 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (41900328290 / 1000000000000) (41900427354 / 1000000000000), orderedInterval (-34795004896 / 1000000000000) (-34794905832 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1174834965125757 / 4000000000000) 2 (IntervalRat.scale (543 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-33912227206 / 1000000000000) (-33912186520 / 1000000000000), orderedInterval (31955714106 / 1000000000000) (31955754791 / 1000000000000)))) (orderedInterval (-2577777815 / 1000000000000) (-2577772707 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (496765839023559 / 4000000000000) 2 (IntervalRat.scale (543 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-45455349737 / 1000000000000) (-45455322146 / 1000000000000), orderedInterval (55499675632 / 1000000000000) (55499703223 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2019325556016039 / 4000000000000) 2 (IntervalRat.scale (543 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (6353301891 / 1000000000000) (6353301895 / 1000000000000), orderedInterval (-34944672414 / 1000000000000) (-34944672409 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1348815887666601 / 4000000000000) 2 (IntervalRat.scale (543 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-41901725224 / 1000000000000) (-41901720779 / 1000000000000), orderedInterval (11559109749 / 1000000000000) (11559114194 / 1000000000000)))) (orderedInterval (-10292225857 / 1000000000000) (-10292224374 / 1000000000000))) = true
  rfl'

theorem compactCertificate400_chunkChecks2 :
    compactCertificate400.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate400.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate400_chunkChecks2_0
    compactCertificate400_chunkChecks2_1 compactCertificate400_chunkChecks2_2

theorem compactCertificate400_chunkChecks3_0 :
    compactCertificate400.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (543 / 2) 3 (IntervalRat.scale (543 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (41603309518 / 1000000000000) (41603353507 / 1000000000000), orderedInterval (-24855360418 / 1000000000000) (-24855316429 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (799942684710243 / 4000000000000) 3 (IntervalRat.scale (543 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-16213976593 / 1000000000000) (-16213976363 / 1000000000000), orderedInterval (54081653309 / 1000000000000) (54081653539 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (258685028375619 / 800000000000) 3 (IntervalRat.scale (543 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-23465928838 / 1000000000000) (-23465928837 / 1000000000000), orderedInterval (-37621896136 / 1000000000000) (-37621896135 / 1000000000000)))) (orderedInterval (13432985821 / 1000000000000) (13433003351 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (233421280313001 / 4000000000000) 3 (IntervalRat.scale (543 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (54742453270 / 1000000000000) (54742463464 / 1000000000000), orderedInterval (-89423010998 / 1000000000000) (-89423000804 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (627002392339797 / 4000000000000) 3 (IntervalRat.scale (543 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (28038720622 / 1000000000000) (28038720623 / 1000000000000), orderedInterval (57139904533 / 1000000000000) (57139904534 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1702433464538049 / 4000000000000) 3 (IntervalRat.scale (543 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29388725707 / 1000000000000) (-29388691621 / 1000000000000), orderedInterval (25175934911 / 1000000000000) (25175968997 / 1000000000000)))) (orderedInterval (6503551123 / 1000000000000) (6503560558 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1254004784680137 / 4000000000000) 3 (IntervalRat.scale (543 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (5704512451 / 1000000000000) (5704512452 / 1000000000000), orderedInterval (44691442986 / 1000000000000) (44691442987 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2148758572376301 / 4000000000000) 3 (IntervalRat.scale (543 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-23777672171 / 1000000000000) (-23777672170 / 1000000000000), orderedInterval (-24871953939 / 1000000000000) (-24871953938 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1582765839023559 / 4000000000000) 3 (IntervalRat.scale (543 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (23820846771 / 1000000000000) (23820846772 / 1000000000000), orderedInterval (32241355744 / 1000000000000) (32241355745 / 1000000000000)))) (orderedInterval (-8339350578 / 1000000000000) (-8339350492 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate400_chunkChecks3_1 :
    compactCertificate400.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2428369823564457 / 4000000000000) 3 (IntervalRat.scale (543 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-32375839793 / 1000000000000) (-32375838995 / 1000000000000), orderedInterval (-638115541 / 1000000000000) (-638114742 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1402019971326753 / 4000000000000) 3 (IntervalRat.scale (543 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-22938531641 / 1000000000000) (-22938529026 / 1000000000000), orderedInterval (35950928108 / 1000000000000) (35950930723 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2487909042219477 / 4000000000000) 3 (IntervalRat.scale (543 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (21266119294 / 1000000000000) (21266119295 / 1000000000000), orderedInterval (23884663471 / 1000000000000) (23884663472 / 1000000000000)))) (orderedInterval (-47667079878 / 1000000000000) (-47667076820 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2324527350314313 / 4000000000000) 3 (IntervalRat.scale (543 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-21883512587 / 1000000000000) (-21883512586 / 1000000000000), orderedInterval (-24812491643 / 1000000000000) (-24812491642 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1658892401573529 / 4000000000000) 3 (IntervalRat.scale (543 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (28591650528 / 1000000000000) (28591650529 / 1000000000000), orderedInterval (26752937180 / 1000000000000) (26752937181 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1881007177019391 / 4000000000000) 3 (IntervalRat.scale (543 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-7380877147 / 1000000000000) (-7380877139 / 1000000000000), orderedInterval (36053766324 / 1000000000000) (36053766332 / 1000000000000)))) (orderedInterval (-12431158305 / 1000000000000) (-12431158157 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1568187679342479 / 4000000000000) 3 (IntervalRat.scale (543 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-5340394797 / 1000000000000) (-5340394796 / 1000000000000), orderedInterval (-39934610289 / 1000000000000) (-39934610288 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1385541373060059 / 4000000000000) 3 (IntervalRat.scale (543 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (42857898090 / 1000000000000) (42857898356 / 1000000000000), orderedInterval (-1107477315 / 1000000000000) (-1107477049 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (401583893981841 / 800000000000) 3 (IntervalRat.scale (543 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (3916226788 / 1000000000000) (3916226789 / 1000000000000), orderedInterval (35392165674 / 1000000000000) (35392165675 / 1000000000000)))) (orderedInterval (-4484470563 / 1000000000000) (-4484470445 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate400_chunkChecks3_2 :
    compactCertificate400.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1110802184956227 / 4000000000000) 3 (IntervalRat.scale (543 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (43018030997 / 1000000000000) (43018052251 / 1000000000000), orderedInterval (-21099222852 / 1000000000000) (-21099201599 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (941639313984747 / 4000000000000) 3 (IntervalRat.scale (543 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-28291730876 / 1000000000000) (-28291730875 / 1000000000000), orderedInterval (-43573435845 / 1000000000000) (-43573435844 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (589234160976441 / 4000000000000) 3 (IntervalRat.scale (543 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-27895934819 / 1000000000000) (-27895934818 / 1000000000000), orderedInterval (-59432693236 / 1000000000000) (-59432693235 / 1000000000000)))) (orderedInterval (-4931642668 / 1000000000000) (-4931638960 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (316892091477447 / 4000000000000) 3 (IntervalRat.scale (543 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-89159488272 / 1000000000000) (-89159488266 / 1000000000000), orderedInterval (-8722867883 / 1000000000000) (-8722867877 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (860423672653341 / 4000000000000) 3 (IntervalRat.scale (543 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (41900328290 / 1000000000000) (41900427354 / 1000000000000), orderedInterval (-34795004896 / 1000000000000) (-34794905832 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1174834965125757 / 4000000000000) 3 (IntervalRat.scale (543 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-33912227206 / 1000000000000) (-33912186520 / 1000000000000), orderedInterval (31955714106 / 1000000000000) (31955754791 / 1000000000000)))) (orderedInterval (2713426176 / 1000000000000) (2713431290 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (496765839023559 / 4000000000000) 3 (IntervalRat.scale (543 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-45455349737 / 1000000000000) (-45455322146 / 1000000000000), orderedInterval (55499675632 / 1000000000000) (55499703223 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2019325556016039 / 4000000000000) 3 (IntervalRat.scale (543 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (6353301891 / 1000000000000) (6353301895 / 1000000000000), orderedInterval (-34944672414 / 1000000000000) (-34944672409 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1348815887666601 / 4000000000000) 3 (IntervalRat.scale (543 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-41901725224 / 1000000000000) (-41901720779 / 1000000000000), orderedInterval (11559109749 / 1000000000000) (11559114194 / 1000000000000)))) (orderedInterval (-14126003837 / 1000000000000) (-14126001975 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate400_chunkChecks3 :
    compactCertificate400.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate400.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate400_chunkChecks3_0
    compactCertificate400_chunkChecks3_1 compactCertificate400_chunkChecks3_2

theorem compactCertificate400_chunkChecks4_0 :
    compactCertificate400.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (543 / 2) 4 (IntervalRat.scale (543 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (41603309518 / 1000000000000) (41603353507 / 1000000000000), orderedInterval (-24855360418 / 1000000000000) (-24855316429 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (799942684710243 / 4000000000000) 4 (IntervalRat.scale (543 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-16213976593 / 1000000000000) (-16213976363 / 1000000000000), orderedInterval (54081653309 / 1000000000000) (54081653539 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (258685028375619 / 800000000000) 4 (IntervalRat.scale (543 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-23465928838 / 1000000000000) (-23465928837 / 1000000000000), orderedInterval (-37621896136 / 1000000000000) (-37621896135 / 1000000000000)))) (orderedInterval (13575816731 / 1000000000000) (13575834329 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (233421280313001 / 4000000000000) 4 (IntervalRat.scale (543 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (54742453270 / 1000000000000) (54742463464 / 1000000000000), orderedInterval (-89423010998 / 1000000000000) (-89423000804 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (627002392339797 / 4000000000000) 4 (IntervalRat.scale (543 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (28038720622 / 1000000000000) (28038720623 / 1000000000000), orderedInterval (57139904533 / 1000000000000) (57139904534 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1702433464538049 / 4000000000000) 4 (IntervalRat.scale (543 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29388725707 / 1000000000000) (-29388691621 / 1000000000000), orderedInterval (25175934911 / 1000000000000) (25175968997 / 1000000000000)))) (orderedInterval (12681260020 / 1000000000000) (12681274841 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1254004784680137 / 4000000000000) 4 (IntervalRat.scale (543 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (5704512451 / 1000000000000) (5704512452 / 1000000000000), orderedInterval (44691442986 / 1000000000000) (44691442987 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2148758572376301 / 4000000000000) 4 (IntervalRat.scale (543 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-23777672171 / 1000000000000) (-23777672170 / 1000000000000), orderedInterval (-24871953939 / 1000000000000) (-24871953938 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1582765839023559 / 4000000000000) 4 (IntervalRat.scale (543 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (23820846771 / 1000000000000) (23820846772 / 1000000000000), orderedInterval (32241355744 / 1000000000000) (32241355745 / 1000000000000)))) (orderedInterval (13898944583 / 1000000000000) (13898944743 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate400_chunkChecks4_1 :
    compactCertificate400.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2428369823564457 / 4000000000000) 4 (IntervalRat.scale (543 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-32375839793 / 1000000000000) (-32375838995 / 1000000000000), orderedInterval (-638115541 / 1000000000000) (-638114742 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1402019971326753 / 4000000000000) 4 (IntervalRat.scale (543 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-22938531641 / 1000000000000) (-22938529026 / 1000000000000), orderedInterval (35950928108 / 1000000000000) (35950930723 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2487909042219477 / 4000000000000) 4 (IntervalRat.scale (543 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (21266119294 / 1000000000000) (21266119295 / 1000000000000), orderedInterval (23884663471 / 1000000000000) (23884663472 / 1000000000000)))) (orderedInterval (222716257720 / 1000000000000) (222716264148 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2324527350314313 / 4000000000000) 4 (IntervalRat.scale (543 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-21883512587 / 1000000000000) (-21883512586 / 1000000000000), orderedInterval (-24812491643 / 1000000000000) (-24812491642 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1658892401573529 / 4000000000000) 4 (IntervalRat.scale (543 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (28591650528 / 1000000000000) (28591650529 / 1000000000000), orderedInterval (26752937180 / 1000000000000) (26752937181 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1881007177019391 / 4000000000000) 4 (IntervalRat.scale (543 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-7380877147 / 1000000000000) (-7380877139 / 1000000000000), orderedInterval (36053766324 / 1000000000000) (36053766332 / 1000000000000)))) (orderedInterval (23440360123 / 1000000000000) (23440360380 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1568187679342479 / 4000000000000) 4 (IntervalRat.scale (543 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-5340394797 / 1000000000000) (-5340394796 / 1000000000000), orderedInterval (-39934610289 / 1000000000000) (-39934610288 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1385541373060059 / 4000000000000) 4 (IntervalRat.scale (543 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (42857898090 / 1000000000000) (42857898356 / 1000000000000), orderedInterval (-1107477315 / 1000000000000) (-1107477049 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (401583893981841 / 800000000000) 4 (IntervalRat.scale (543 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (3916226788 / 1000000000000) (3916226789 / 1000000000000), orderedInterval (35392165674 / 1000000000000) (35392165675 / 1000000000000)))) (orderedInterval (-5561401239 / 1000000000000) (-5561401061 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate400_chunkChecks4_2 :
    compactCertificate400.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1110802184956227 / 4000000000000) 4 (IntervalRat.scale (543 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (43018030997 / 1000000000000) (43018052251 / 1000000000000), orderedInterval (-21099222852 / 1000000000000) (-21099201599 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (941639313984747 / 4000000000000) 4 (IntervalRat.scale (543 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-28291730876 / 1000000000000) (-28291730875 / 1000000000000), orderedInterval (-43573435845 / 1000000000000) (-43573435844 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (589234160976441 / 4000000000000) 4 (IntervalRat.scale (543 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-27895934819 / 1000000000000) (-27895934818 / 1000000000000), orderedInterval (-59432693236 / 1000000000000) (-59432693235 / 1000000000000)))) (orderedInterval (-6665656621 / 1000000000000) (-6665652816 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (316892091477447 / 4000000000000) 4 (IntervalRat.scale (543 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-89159488272 / 1000000000000) (-89159488266 / 1000000000000), orderedInterval (-8722867883 / 1000000000000) (-8722867877 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (860423672653341 / 4000000000000) 4 (IntervalRat.scale (543 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (41900328290 / 1000000000000) (41900427354 / 1000000000000), orderedInterval (-34795004896 / 1000000000000) (-34794905832 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1174834965125757 / 4000000000000) 4 (IntervalRat.scale (543 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-33912227206 / 1000000000000) (-33912186520 / 1000000000000), orderedInterval (31955714106 / 1000000000000) (31955754791 / 1000000000000)))) (orderedInterval (3176884060 / 1000000000000) (3176889285 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (496765839023559 / 4000000000000) 4 (IntervalRat.scale (543 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-45455349737 / 1000000000000) (-45455322146 / 1000000000000), orderedInterval (55499675632 / 1000000000000) (55499703223 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2019325556016039 / 4000000000000) 4 (IntervalRat.scale (543 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (6353301891 / 1000000000000) (6353301895 / 1000000000000), orderedInterval (-34944672414 / 1000000000000) (-34944672409 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1348815887666601 / 4000000000000) 4 (IntervalRat.scale (543 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-41901725224 / 1000000000000) (-41901720779 / 1000000000000), orderedInterval (11559109749 / 1000000000000) (11559114194 / 1000000000000)))) (orderedInterval (12617348153 / 1000000000000) (12617350547 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate400_chunkChecks4 :
    compactCertificate400.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate400.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate400_chunkChecks4_0
    compactCertificate400_chunkChecks4_1 compactCertificate400_chunkChecks4_2

theorem compactCertificate400_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate400.chunkCheck r b = true :=
  compactCertificate400.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate400_chunkChecks0
    · exact compactCertificate400_chunkChecks1
    · exact compactCertificate400_chunkChecks2
    · exact compactCertificate400_chunkChecks3
    · exact compactCertificate400_chunkChecks4)

theorem compactCertificate400_coefficient0 :
    compactCertificate400.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate400_coefficient1 :
    compactCertificate400.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate400_coefficient2 :
    compactCertificate400.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate400_coefficient3 :
    compactCertificate400.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate400_coefficient4 :
    compactCertificate400.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate400_coefficients : ∀ r : Fin 5,
    compactCertificate400.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate400_coefficient0
  · exact compactCertificate400_coefficient1
  · exact compactCertificate400_coefficient2
  · exact compactCertificate400_coefficient3
  · exact compactCertificate400_coefficient4

theorem compactCertificate400_lower : (1 : ℚ) ≤ compactCertificate400.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate400, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate400_proves {t : ℝ} (ht : t ∈ compactCertificate400.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate400.proves compactCertificate400_states compactCertificate400_chunks
    compactCertificate400_coefficients compactCertificate400_lower ht

end Erdos232
