/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate486 : CompactCertificate where
  left := 357
  right := 358
  center := 715 / 2
  grid := fun i =>
    match i.val with
    | 0 => 114
    | 1 => 84
    | 2 => 136
    | 3 => 24
    | 4 => 66
    | 5 => 178
    | 6 => 131
    | 7 => 225
    | 8 => 166
    | 9 => 255
    | 10 => 147
    | 11 => 261
    | 12 => 244
    | 13 => 174
    | 14 => 197
    | 15 => 164
    | 16 => 145
    | 17 => 211
    | 18 => 116
    | 19 => 99
    | 20 => 62
    | 21 => 33
    | 22 => 90
    | 23 => 123
    | 24 => 52
    | 25 => 212
    | _ => 141
  point := fun i =>
    match i.val with
    | 0 => 715 / 2
    | 1 => 210666305549843 / 800000000000
    | 2 => 68125154802419 / 160000000000
    | 3 => 61471902550201 / 800000000000
    | 4 => 165122176988197 / 800000000000
    | 5 => 448338831360849 / 800000000000
    | 6 => 330244353976537 / 800000000000
    | 7 => 565879329373501 / 800000000000
    | 8 => 416824152818359 / 800000000000
    | 9 => 639515441564857 / 800000000000
    | 10 => 369224412338353 / 800000000000
    | 11 => 655195198963877 / 800000000000
    | 12 => 612168344557913 / 800000000000
    | 13 => 436872216252329 / 800000000000
    | 14 => 495366530964591 / 800000000000
    | 15 => 412984968961279 / 800000000000
    | 16 => 364884744654859 / 800000000000
    | 17 => 105757821067041 / 160000000000
    | 18 => 292531698800627 / 800000000000
    | 19 => 247982360773147 / 800000000000
    | 20 => 155175847181641 / 800000000000
    | 21 => 83454086705847 / 800000000000
    | 22 => 226594079538541 / 800000000000
    | 23 => 309394843486157 / 800000000000
    | 24 => 130824152818359 / 800000000000
    | 25 => 531792918066839 / 800000000000
    | _ => 355213023823801 / 800000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (6034205836 / 1000000000000) (6034205837 / 1000000000000), orderedInterval (41756912695 / 1000000000000) (41756912696 / 1000000000000))
    | 1 => (orderedInterval (10922954197 / 1000000000000) (10922954198 / 1000000000000), orderedInterval (47919228783 / 1000000000000) (47919228784 / 1000000000000))
    | 2 => (orderedInterval (-24591793277 / 1000000000000) (-24591786943 / 1000000000000), orderedInterval (29868798630 / 1000000000000) (29868804964 / 1000000000000))
    | 3 => (orderedInterval (72204601388 / 1000000000000) (72204653832 / 1000000000000), orderedInterval (-55890634706 / 1000000000000) (-55890582262 / 1000000000000))
    | 4 => (orderedInterval (-8716503149 / 1000000000000) (-8716503116 / 1000000000000), orderedInterval (54869894833 / 1000000000000) (54869894866 / 1000000000000))
    | 5 => (orderedInterval (30573291592 / 1000000000000) (30573356046 / 1000000000000), orderedInterval (-14212984301 / 1000000000000) (-14212919847 / 1000000000000))
    | 6 => (orderedInterval (-34992762478 / 1000000000000) (-34992716309 / 1000000000000), orderedInterval (17866114271 / 1000000000000) (17866160440 / 1000000000000))
    | 7 => (orderedInterval (-28706275892 / 1000000000000) (-28706275852 / 1000000000000), orderedInterval (-8695060100 / 1000000000000) (-8695060061 / 1000000000000))
    | 8 => (orderedInterval (10695549778 / 1000000000000) (10695549779 / 1000000000000), orderedInterval (33268164867 / 1000000000000) (33268164868 / 1000000000000))
    | 9 => (orderedInterval (22564057391 / 1000000000000) (22564067688 / 1000000000000), orderedInterval (-16962295308 / 1000000000000) (-16962285010 / 1000000000000))
    | 10 => (orderedInterval (-17855383447 / 1000000000000) (-17855383446 / 1000000000000), orderedInterval (-32546778408 / 1000000000000) (-32546778407 / 1000000000000))
    | 11 => (orderedInterval (4893696071 / 1000000000000) (4893696072 / 1000000000000), orderedInterval (-27450593896 / 1000000000000) (-27450593894 / 1000000000000))
    | 12 => (orderedInterval (-15148462583 / 1000000000000) (-15148462418 / 1000000000000), orderedInterval (24555325918 / 1000000000000) (24555326083 / 1000000000000))
    | 13 => (orderedInterval (8060194701 / 1000000000000) (8060194702 / 1000000000000), orderedInterval (33171095593 / 1000000000000) (33171095594 / 1000000000000))
    | 14 => (orderedInterval (-28570218389 / 1000000000000) (-28570218387 / 1000000000000), orderedInterval (-14532395574 / 1000000000000) (-14532395572 / 1000000000000))
    | 15 => (orderedInterval (34236758784 / 1000000000000) (34236766056 / 1000000000000), orderedInterval (-7846629110 / 1000000000000) (-7846621838 / 1000000000000))
    | 16 => (orderedInterval (-36533977685 / 1000000000000) (-36533977664 / 1000000000000), orderedInterval (-7772725485 / 1000000000000) (-7772725464 / 1000000000000))
    | 17 => (orderedInterval (27720556967 / 1000000000000) (27720655648 / 1000000000000), orderedInterval (-13974645825 / 1000000000000) (-13974547144 / 1000000000000))
    | 18 => (orderedInterval (37495935718 / 1000000000000) (37495967697 / 1000000000000), orderedInterval (-18355553005 / 1000000000000) (-18355521026 / 1000000000000))
    | 19 => (orderedInterval (11419373442 / 1000000000000) (11419373506 / 1000000000000), orderedInterval (-43874530800 / 1000000000000) (-43874530736 / 1000000000000))
    | 20 => (orderedInterval (-1385219608 / 1000000000000) (-1385219603 / 1000000000000), orderedInterval (57276147384 / 1000000000000) (57276147389 / 1000000000000))
    | 21 => (orderedInterval (-77338113626 / 1000000000000) (-77338113622 / 1000000000000), orderedInterval (-10650013590 / 1000000000000) (-10650013586 / 1000000000000))
    | 22 => (orderedInterval (45475459680 / 1000000000000) (45475459682 / 1000000000000), orderedInterval (13320944137 / 1000000000000) (13320944139 / 1000000000000))
    | 23 => (orderedInterval (-36389616336 / 1000000000000) (-36389616335 / 1000000000000), orderedInterval (-17894472997 / 1000000000000) (-17894472996 / 1000000000000))
    | 24 => (orderedInterval (50824657396 / 1000000000000) (50824657397 / 1000000000000), orderedInterval (36036153262 / 1000000000000) (36036153263 / 1000000000000))
    | 25 => (orderedInterval (-14599368559 / 1000000000000) (-14599368416 / 1000000000000), orderedInterval (27297504226 / 1000000000000) (27297504368 / 1000000000000))
    | _ => (orderedInterval (-36533149667 / 1000000000000) (-36533142009 / 1000000000000), orderedInterval (9996245122 / 1000000000000) (9996252780 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (1050454220 / 1000000000000) (1050454617 / 1000000000000)
      | 1 => orderedInterval (-3275072977 / 1000000000000) (-3275067782 / 1000000000000)
      | 2 => orderedInterval (1143906727 / 1000000000000) (1143906748 / 1000000000000)
      | 3 => orderedInterval (-4636631712 / 1000000000000) (-4636629740 / 1000000000000)
      | 4 => orderedInterval (1180253346 / 1000000000000) (1180253392 / 1000000000000)
      | 5 => orderedInterval (3195828669 / 1000000000000) (3195831315 / 1000000000000)
      | 6 => orderedInterval (-6686754123 / 1000000000000) (-6686748916 / 1000000000000)
      | 7 => orderedInterval (3185220892 / 1000000000000) (3185220936 / 1000000000000)
      | _ => orderedInterval (8349388743 / 1000000000000) (8349390291 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (18967384952 / 1000000000000) (18967385424 / 1000000000000)
      | 1 => orderedInterval (2870900859 / 1000000000000) (2870908214 / 1000000000000)
      | 2 => orderedInterval (1702450487 / 1000000000000) (1702450525 / 1000000000000)
      | 3 => orderedInterval (-5313338726 / 1000000000000) (-5313334340 / 1000000000000)
      | 4 => orderedInterval (3969989951 / 1000000000000) (3969990028 / 1000000000000)
      | 5 => orderedInterval (-224899642 / 1000000000000) (-224894798 / 1000000000000)
      | 6 => orderedInterval (6166835061 / 1000000000000) (6166840378 / 1000000000000)
      | 7 => orderedInterval (1301539583 / 1000000000000) (1301539622 / 1000000000000)
      | _ => orderedInterval (-6361828029 / 1000000000000) (-6361826084 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-453056600 / 1000000000000) (-453056039 / 1000000000000)
      | 1 => orderedInterval (5475325275 / 1000000000000) (5475336650 / 1000000000000)
      | 2 => orderedInterval (-4020095979 / 1000000000000) (-4020095911 / 1000000000000)
      | 3 => orderedInterval (18615565208 / 1000000000000) (18615574998 / 1000000000000)
      | 4 => orderedInterval (-3476243755 / 1000000000000) (-3476243626 / 1000000000000)
      | 5 => orderedInterval (-6653138342 / 1000000000000) (-6653129440 / 1000000000000)
      | 6 => orderedInterval (6754236333 / 1000000000000) (6754241779 / 1000000000000)
      | 7 => orderedInterval (-2741397493 / 1000000000000) (-2741397454 / 1000000000000)
      | _ => orderedInterval (-14728871497 / 1000000000000) (-14728869029 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-19689099716 / 1000000000000) (-19689099048 / 1000000000000)
      | 1 => orderedInterval (-4299224028 / 1000000000000) (-4299206238 / 1000000000000)
      | 2 => orderedInterval (-4555157785 / 1000000000000) (-4555157662 / 1000000000000)
      | 3 => orderedInterval (18356050488 / 1000000000000) (18356072354 / 1000000000000)
      | 4 => orderedInterval (-7205260082 / 1000000000000) (-7205259859 / 1000000000000)
      | 5 => orderedInterval (1629197751 / 1000000000000) (1629214114 / 1000000000000)
      | 6 => orderedInterval (-5076099315 / 1000000000000) (-5076093749 / 1000000000000)
      | 7 => orderedInterval (-1583145650 / 1000000000000) (-1583145610 / 1000000000000)
      | _ => orderedInterval (17898910484 / 1000000000000) (17898913635 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-371730071 / 1000000000000) (-371729275 / 1000000000000)
      | 1 => orderedInterval (-13138284229 / 1000000000000) (-13138256303 / 1000000000000)
      | 2 => orderedInterval (14761667594 / 1000000000000) (14761667822 / 1000000000000)
      | 3 => orderedInterval (-84850326731 / 1000000000000) (-84850277809 / 1000000000000)
      | 4 => orderedInterval (11231609341 / 1000000000000) (11231609741 / 1000000000000)
      | 5 => orderedInterval (15543266339 / 1000000000000) (15543296504 / 1000000000000)
      | 6 => orderedInterval (-6902839648 / 1000000000000) (-6902833942 / 1000000000000)
      | 7 => orderedInterval (3432240851 / 1000000000000) (3432240893 / 1000000000000)
      | _ => orderedInterval (30429939212 / 1000000000000) (30429943294 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (3506593785 / 1000000000000) (3506610861 / 1000000000000)
    | 1 => orderedInterval (23079034496 / 1000000000000) (23079058969 / 1000000000000)
    | 2 => orderedInterval (-1227676850 / 1000000000000) (-1227638072 / 1000000000000)
    | 3 => orderedInterval (-4523827853 / 1000000000000) (-4523762063 / 1000000000000)
    | _ => orderedInterval (-29864457342 / 1000000000000) (-29864339075 / 1000000000000)

theorem compactCertificate486_stateChecks0 :
    compactCertificate486.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 114 12 (715 / 2)) (orderedInterval (6034205836 / 1000000000000) (6034205837 / 1000000000000), orderedInterval (41756912695 / 1000000000000) (41756912696 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 84 12 (210666305549843 / 800000000000)) (orderedInterval (10922954197 / 1000000000000) (10922954198 / 1000000000000), orderedInterval (47919228783 / 1000000000000) (47919228784 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 136 12 (68125154802419 / 160000000000)) (orderedInterval (-24591793277 / 1000000000000) (-24591786943 / 1000000000000), orderedInterval (29868798630 / 1000000000000) (29868804964 / 1000000000000))) = true
  rfl'

theorem compactCertificate486_stateChecks1 :
    compactCertificate486.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 24 12 (61471902550201 / 800000000000)) (orderedInterval (72204601388 / 1000000000000) (72204653832 / 1000000000000), orderedInterval (-55890634706 / 1000000000000) (-55890582262 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (165122176988197 / 800000000000)) (orderedInterval (-8716503149 / 1000000000000) (-8716503116 / 1000000000000), orderedInterval (54869894833 / 1000000000000) (54869894866 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 178 12 (448338831360849 / 800000000000)) (orderedInterval (30573291592 / 1000000000000) (30573356046 / 1000000000000), orderedInterval (-14212984301 / 1000000000000) (-14212919847 / 1000000000000))) = true
  rfl'

theorem compactCertificate486_stateChecks2 :
    compactCertificate486.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 131 12 (330244353976537 / 800000000000)) (orderedInterval (-34992762478 / 1000000000000) (-34992716309 / 1000000000000), orderedInterval (17866114271 / 1000000000000) (17866160440 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 225 12 (565879329373501 / 800000000000)) (orderedInterval (-28706275892 / 1000000000000) (-28706275852 / 1000000000000), orderedInterval (-8695060100 / 1000000000000) (-8695060061 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 166 12 (416824152818359 / 800000000000)) (orderedInterval (10695549778 / 1000000000000) (10695549779 / 1000000000000), orderedInterval (33268164867 / 1000000000000) (33268164868 / 1000000000000))) = true
  rfl'

theorem compactCertificate486_stateChecks3 :
    compactCertificate486.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 255 12 (639515441564857 / 800000000000)) (orderedInterval (22564057391 / 1000000000000) (22564067688 / 1000000000000), orderedInterval (-16962295308 / 1000000000000) (-16962285010 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 147 12 (369224412338353 / 800000000000)) (orderedInterval (-17855383447 / 1000000000000) (-17855383446 / 1000000000000), orderedInterval (-32546778408 / 1000000000000) (-32546778407 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 261 12 (655195198963877 / 800000000000)) (orderedInterval (4893696071 / 1000000000000) (4893696072 / 1000000000000), orderedInterval (-27450593896 / 1000000000000) (-27450593894 / 1000000000000))) = true
  rfl'

theorem compactCertificate486_stateChecks4 :
    compactCertificate486.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 244 12 (612168344557913 / 800000000000)) (orderedInterval (-15148462583 / 1000000000000) (-15148462418 / 1000000000000), orderedInterval (24555325918 / 1000000000000) (24555326083 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 174 12 (436872216252329 / 800000000000)) (orderedInterval (8060194701 / 1000000000000) (8060194702 / 1000000000000), orderedInterval (33171095593 / 1000000000000) (33171095594 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 197 12 (495366530964591 / 800000000000)) (orderedInterval (-28570218389 / 1000000000000) (-28570218387 / 1000000000000), orderedInterval (-14532395574 / 1000000000000) (-14532395572 / 1000000000000))) = true
  rfl'

theorem compactCertificate486_stateChecks5 :
    compactCertificate486.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 164 12 (412984968961279 / 800000000000)) (orderedInterval (34236758784 / 1000000000000) (34236766056 / 1000000000000), orderedInterval (-7846629110 / 1000000000000) (-7846621838 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 145 12 (364884744654859 / 800000000000)) (orderedInterval (-36533977685 / 1000000000000) (-36533977664 / 1000000000000), orderedInterval (-7772725485 / 1000000000000) (-7772725464 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 211 12 (105757821067041 / 160000000000)) (orderedInterval (27720556967 / 1000000000000) (27720655648 / 1000000000000), orderedInterval (-13974645825 / 1000000000000) (-13974547144 / 1000000000000))) = true
  rfl'

theorem compactCertificate486_stateChecks6 :
    compactCertificate486.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 116 12 (292531698800627 / 800000000000)) (orderedInterval (37495935718 / 1000000000000) (37495967697 / 1000000000000), orderedInterval (-18355553005 / 1000000000000) (-18355521026 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 99 12 (247982360773147 / 800000000000)) (orderedInterval (11419373442 / 1000000000000) (11419373506 / 1000000000000), orderedInterval (-43874530800 / 1000000000000) (-43874530736 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (155175847181641 / 800000000000)) (orderedInterval (-1385219608 / 1000000000000) (-1385219603 / 1000000000000), orderedInterval (57276147384 / 1000000000000) (57276147389 / 1000000000000))) = true
  rfl'

theorem compactCertificate486_stateChecks7 :
    compactCertificate486.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 33 12 (83454086705847 / 800000000000)) (orderedInterval (-77338113626 / 1000000000000) (-77338113622 / 1000000000000), orderedInterval (-10650013590 / 1000000000000) (-10650013586 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 90 12 (226594079538541 / 800000000000)) (orderedInterval (45475459680 / 1000000000000) (45475459682 / 1000000000000), orderedInterval (13320944137 / 1000000000000) (13320944139 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 123 12 (309394843486157 / 800000000000)) (orderedInterval (-36389616336 / 1000000000000) (-36389616335 / 1000000000000), orderedInterval (-17894472997 / 1000000000000) (-17894472996 / 1000000000000))) = true
  rfl'

theorem compactCertificate486_stateChecks8 :
    compactCertificate486.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 52 12 (130824152818359 / 800000000000)) (orderedInterval (50824657396 / 1000000000000) (50824657397 / 1000000000000), orderedInterval (36036153262 / 1000000000000) (36036153263 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 212 12 (531792918066839 / 800000000000)) (orderedInterval (-14599368559 / 1000000000000) (-14599368416 / 1000000000000), orderedInterval (27297504226 / 1000000000000) (27297504368 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 141 12 (355213023823801 / 800000000000)) (orderedInterval (-36533149667 / 1000000000000) (-36533142009 / 1000000000000), orderedInterval (9996245122 / 1000000000000) (9996252780 / 1000000000000))) = true
  rfl'

theorem compactCertificate486_states : ∀ j,
    BesselStateValid (compactCertificate486.point j) (compactCertificate486.state j) :=
  compactCertificate486.statesValid_of_checks3 compactCertificate486_stateChecks0
    compactCertificate486_stateChecks1 compactCertificate486_stateChecks2
    compactCertificate486_stateChecks3 compactCertificate486_stateChecks4
    compactCertificate486_stateChecks5 compactCertificate486_stateChecks6
    compactCertificate486_stateChecks7 compactCertificate486_stateChecks8

theorem compactCertificate486_chunkChecks0_0 :
    compactCertificate486.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (715 / 2) 0 (IntervalRat.scale (715 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (6034205836 / 1000000000000) (6034205837 / 1000000000000), orderedInterval (41756912695 / 1000000000000) (41756912696 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (210666305549843 / 800000000000) 0 (IntervalRat.scale (715 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (10922954197 / 1000000000000) (10922954198 / 1000000000000), orderedInterval (47919228783 / 1000000000000) (47919228784 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (68125154802419 / 160000000000) 0 (IntervalRat.scale (715 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-24591793277 / 1000000000000) (-24591786943 / 1000000000000), orderedInterval (29868798630 / 1000000000000) (29868804964 / 1000000000000)))) (orderedInterval (1050454220 / 1000000000000) (1050454617 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (61471902550201 / 800000000000) 0 (IntervalRat.scale (715 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (72204601388 / 1000000000000) (72204653832 / 1000000000000), orderedInterval (-55890634706 / 1000000000000) (-55890582262 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (165122176988197 / 800000000000) 0 (IntervalRat.scale (715 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-8716503149 / 1000000000000) (-8716503116 / 1000000000000), orderedInterval (54869894833 / 1000000000000) (54869894866 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (448338831360849 / 800000000000) 0 (IntervalRat.scale (715 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30573291592 / 1000000000000) (30573356046 / 1000000000000), orderedInterval (-14212984301 / 1000000000000) (-14212919847 / 1000000000000)))) (orderedInterval (-3275072977 / 1000000000000) (-3275067782 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (330244353976537 / 800000000000) 0 (IntervalRat.scale (715 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-34992762478 / 1000000000000) (-34992716309 / 1000000000000), orderedInterval (17866114271 / 1000000000000) (17866160440 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (565879329373501 / 800000000000) 0 (IntervalRat.scale (715 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-28706275892 / 1000000000000) (-28706275852 / 1000000000000), orderedInterval (-8695060100 / 1000000000000) (-8695060061 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (416824152818359 / 800000000000) 0 (IntervalRat.scale (715 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (10695549778 / 1000000000000) (10695549779 / 1000000000000), orderedInterval (33268164867 / 1000000000000) (33268164868 / 1000000000000)))) (orderedInterval (1143906727 / 1000000000000) (1143906748 / 1000000000000))) = true
  rfl'

theorem compactCertificate486_chunkChecks0_1 :
    compactCertificate486.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (639515441564857 / 800000000000) 0 (IntervalRat.scale (715 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (22564057391 / 1000000000000) (22564067688 / 1000000000000), orderedInterval (-16962295308 / 1000000000000) (-16962285010 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (369224412338353 / 800000000000) 0 (IntervalRat.scale (715 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-17855383447 / 1000000000000) (-17855383446 / 1000000000000), orderedInterval (-32546778408 / 1000000000000) (-32546778407 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (655195198963877 / 800000000000) 0 (IntervalRat.scale (715 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (4893696071 / 1000000000000) (4893696072 / 1000000000000), orderedInterval (-27450593896 / 1000000000000) (-27450593894 / 1000000000000)))) (orderedInterval (-4636631712 / 1000000000000) (-4636629740 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (612168344557913 / 800000000000) 0 (IntervalRat.scale (715 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-15148462583 / 1000000000000) (-15148462418 / 1000000000000), orderedInterval (24555325918 / 1000000000000) (24555326083 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (436872216252329 / 800000000000) 0 (IntervalRat.scale (715 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (8060194701 / 1000000000000) (8060194702 / 1000000000000), orderedInterval (33171095593 / 1000000000000) (33171095594 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (495366530964591 / 800000000000) 0 (IntervalRat.scale (715 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-28570218389 / 1000000000000) (-28570218387 / 1000000000000), orderedInterval (-14532395574 / 1000000000000) (-14532395572 / 1000000000000)))) (orderedInterval (1180253346 / 1000000000000) (1180253392 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (412984968961279 / 800000000000) 0 (IntervalRat.scale (715 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (34236758784 / 1000000000000) (34236766056 / 1000000000000), orderedInterval (-7846629110 / 1000000000000) (-7846621838 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (364884744654859 / 800000000000) 0 (IntervalRat.scale (715 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-36533977685 / 1000000000000) (-36533977664 / 1000000000000), orderedInterval (-7772725485 / 1000000000000) (-7772725464 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (105757821067041 / 160000000000) 0 (IntervalRat.scale (715 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (27720556967 / 1000000000000) (27720655648 / 1000000000000), orderedInterval (-13974645825 / 1000000000000) (-13974547144 / 1000000000000)))) (orderedInterval (3195828669 / 1000000000000) (3195831315 / 1000000000000))) = true
  rfl'

theorem compactCertificate486_chunkChecks0_2 :
    compactCertificate486.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (292531698800627 / 800000000000) 0 (IntervalRat.scale (715 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (37495935718 / 1000000000000) (37495967697 / 1000000000000), orderedInterval (-18355553005 / 1000000000000) (-18355521026 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (247982360773147 / 800000000000) 0 (IntervalRat.scale (715 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (11419373442 / 1000000000000) (11419373506 / 1000000000000), orderedInterval (-43874530800 / 1000000000000) (-43874530736 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (155175847181641 / 800000000000) 0 (IntervalRat.scale (715 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-1385219608 / 1000000000000) (-1385219603 / 1000000000000), orderedInterval (57276147384 / 1000000000000) (57276147389 / 1000000000000)))) (orderedInterval (-6686754123 / 1000000000000) (-6686748916 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (83454086705847 / 800000000000) 0 (IntervalRat.scale (715 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-77338113626 / 1000000000000) (-77338113622 / 1000000000000), orderedInterval (-10650013590 / 1000000000000) (-10650013586 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (226594079538541 / 800000000000) 0 (IntervalRat.scale (715 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (45475459680 / 1000000000000) (45475459682 / 1000000000000), orderedInterval (13320944137 / 1000000000000) (13320944139 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (309394843486157 / 800000000000) 0 (IntervalRat.scale (715 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-36389616336 / 1000000000000) (-36389616335 / 1000000000000), orderedInterval (-17894472997 / 1000000000000) (-17894472996 / 1000000000000)))) (orderedInterval (3185220892 / 1000000000000) (3185220936 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (130824152818359 / 800000000000) 0 (IntervalRat.scale (715 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (50824657396 / 1000000000000) (50824657397 / 1000000000000), orderedInterval (36036153262 / 1000000000000) (36036153263 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (531792918066839 / 800000000000) 0 (IntervalRat.scale (715 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-14599368559 / 1000000000000) (-14599368416 / 1000000000000), orderedInterval (27297504226 / 1000000000000) (27297504368 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (355213023823801 / 800000000000) 0 (IntervalRat.scale (715 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-36533149667 / 1000000000000) (-36533142009 / 1000000000000), orderedInterval (9996245122 / 1000000000000) (9996252780 / 1000000000000)))) (orderedInterval (8349388743 / 1000000000000) (8349390291 / 1000000000000))) = true
  rfl'

theorem compactCertificate486_chunkChecks0 :
    compactCertificate486.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate486.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate486_chunkChecks0_0
    compactCertificate486_chunkChecks0_1 compactCertificate486_chunkChecks0_2

theorem compactCertificate486_chunkChecks1_0 :
    compactCertificate486.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (715 / 2) 1 (IntervalRat.scale (715 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (6034205836 / 1000000000000) (6034205837 / 1000000000000), orderedInterval (41756912695 / 1000000000000) (41756912696 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (210666305549843 / 800000000000) 1 (IntervalRat.scale (715 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (10922954197 / 1000000000000) (10922954198 / 1000000000000), orderedInterval (47919228783 / 1000000000000) (47919228784 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (68125154802419 / 160000000000) 1 (IntervalRat.scale (715 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-24591793277 / 1000000000000) (-24591786943 / 1000000000000), orderedInterval (29868798630 / 1000000000000) (29868804964 / 1000000000000)))) (orderedInterval (18967384952 / 1000000000000) (18967385424 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (61471902550201 / 800000000000) 1 (IntervalRat.scale (715 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (72204601388 / 1000000000000) (72204653832 / 1000000000000), orderedInterval (-55890634706 / 1000000000000) (-55890582262 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (165122176988197 / 800000000000) 1 (IntervalRat.scale (715 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-8716503149 / 1000000000000) (-8716503116 / 1000000000000), orderedInterval (54869894833 / 1000000000000) (54869894866 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (448338831360849 / 800000000000) 1 (IntervalRat.scale (715 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30573291592 / 1000000000000) (30573356046 / 1000000000000), orderedInterval (-14212984301 / 1000000000000) (-14212919847 / 1000000000000)))) (orderedInterval (2870900859 / 1000000000000) (2870908214 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (330244353976537 / 800000000000) 1 (IntervalRat.scale (715 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-34992762478 / 1000000000000) (-34992716309 / 1000000000000), orderedInterval (17866114271 / 1000000000000) (17866160440 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (565879329373501 / 800000000000) 1 (IntervalRat.scale (715 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-28706275892 / 1000000000000) (-28706275852 / 1000000000000), orderedInterval (-8695060100 / 1000000000000) (-8695060061 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (416824152818359 / 800000000000) 1 (IntervalRat.scale (715 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (10695549778 / 1000000000000) (10695549779 / 1000000000000), orderedInterval (33268164867 / 1000000000000) (33268164868 / 1000000000000)))) (orderedInterval (1702450487 / 1000000000000) (1702450525 / 1000000000000))) = true
  rfl'

theorem compactCertificate486_chunkChecks1_1 :
    compactCertificate486.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (639515441564857 / 800000000000) 1 (IntervalRat.scale (715 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (22564057391 / 1000000000000) (22564067688 / 1000000000000), orderedInterval (-16962295308 / 1000000000000) (-16962285010 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (369224412338353 / 800000000000) 1 (IntervalRat.scale (715 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-17855383447 / 1000000000000) (-17855383446 / 1000000000000), orderedInterval (-32546778408 / 1000000000000) (-32546778407 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (655195198963877 / 800000000000) 1 (IntervalRat.scale (715 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (4893696071 / 1000000000000) (4893696072 / 1000000000000), orderedInterval (-27450593896 / 1000000000000) (-27450593894 / 1000000000000)))) (orderedInterval (-5313338726 / 1000000000000) (-5313334340 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (612168344557913 / 800000000000) 1 (IntervalRat.scale (715 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-15148462583 / 1000000000000) (-15148462418 / 1000000000000), orderedInterval (24555325918 / 1000000000000) (24555326083 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (436872216252329 / 800000000000) 1 (IntervalRat.scale (715 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (8060194701 / 1000000000000) (8060194702 / 1000000000000), orderedInterval (33171095593 / 1000000000000) (33171095594 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (495366530964591 / 800000000000) 1 (IntervalRat.scale (715 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-28570218389 / 1000000000000) (-28570218387 / 1000000000000), orderedInterval (-14532395574 / 1000000000000) (-14532395572 / 1000000000000)))) (orderedInterval (3969989951 / 1000000000000) (3969990028 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (412984968961279 / 800000000000) 1 (IntervalRat.scale (715 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (34236758784 / 1000000000000) (34236766056 / 1000000000000), orderedInterval (-7846629110 / 1000000000000) (-7846621838 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (364884744654859 / 800000000000) 1 (IntervalRat.scale (715 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-36533977685 / 1000000000000) (-36533977664 / 1000000000000), orderedInterval (-7772725485 / 1000000000000) (-7772725464 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (105757821067041 / 160000000000) 1 (IntervalRat.scale (715 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (27720556967 / 1000000000000) (27720655648 / 1000000000000), orderedInterval (-13974645825 / 1000000000000) (-13974547144 / 1000000000000)))) (orderedInterval (-224899642 / 1000000000000) (-224894798 / 1000000000000))) = true
  rfl'

theorem compactCertificate486_chunkChecks1_2 :
    compactCertificate486.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (292531698800627 / 800000000000) 1 (IntervalRat.scale (715 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (37495935718 / 1000000000000) (37495967697 / 1000000000000), orderedInterval (-18355553005 / 1000000000000) (-18355521026 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (247982360773147 / 800000000000) 1 (IntervalRat.scale (715 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (11419373442 / 1000000000000) (11419373506 / 1000000000000), orderedInterval (-43874530800 / 1000000000000) (-43874530736 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (155175847181641 / 800000000000) 1 (IntervalRat.scale (715 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-1385219608 / 1000000000000) (-1385219603 / 1000000000000), orderedInterval (57276147384 / 1000000000000) (57276147389 / 1000000000000)))) (orderedInterval (6166835061 / 1000000000000) (6166840378 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (83454086705847 / 800000000000) 1 (IntervalRat.scale (715 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-77338113626 / 1000000000000) (-77338113622 / 1000000000000), orderedInterval (-10650013590 / 1000000000000) (-10650013586 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (226594079538541 / 800000000000) 1 (IntervalRat.scale (715 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (45475459680 / 1000000000000) (45475459682 / 1000000000000), orderedInterval (13320944137 / 1000000000000) (13320944139 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (309394843486157 / 800000000000) 1 (IntervalRat.scale (715 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-36389616336 / 1000000000000) (-36389616335 / 1000000000000), orderedInterval (-17894472997 / 1000000000000) (-17894472996 / 1000000000000)))) (orderedInterval (1301539583 / 1000000000000) (1301539622 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (130824152818359 / 800000000000) 1 (IntervalRat.scale (715 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (50824657396 / 1000000000000) (50824657397 / 1000000000000), orderedInterval (36036153262 / 1000000000000) (36036153263 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (531792918066839 / 800000000000) 1 (IntervalRat.scale (715 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-14599368559 / 1000000000000) (-14599368416 / 1000000000000), orderedInterval (27297504226 / 1000000000000) (27297504368 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (355213023823801 / 800000000000) 1 (IntervalRat.scale (715 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-36533149667 / 1000000000000) (-36533142009 / 1000000000000), orderedInterval (9996245122 / 1000000000000) (9996252780 / 1000000000000)))) (orderedInterval (-6361828029 / 1000000000000) (-6361826084 / 1000000000000))) = true
  rfl'

theorem compactCertificate486_chunkChecks1 :
    compactCertificate486.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate486.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate486_chunkChecks1_0
    compactCertificate486_chunkChecks1_1 compactCertificate486_chunkChecks1_2

theorem compactCertificate486_chunkChecks2_0 :
    compactCertificate486.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (715 / 2) 2 (IntervalRat.scale (715 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (6034205836 / 1000000000000) (6034205837 / 1000000000000), orderedInterval (41756912695 / 1000000000000) (41756912696 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (210666305549843 / 800000000000) 2 (IntervalRat.scale (715 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (10922954197 / 1000000000000) (10922954198 / 1000000000000), orderedInterval (47919228783 / 1000000000000) (47919228784 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (68125154802419 / 160000000000) 2 (IntervalRat.scale (715 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-24591793277 / 1000000000000) (-24591786943 / 1000000000000), orderedInterval (29868798630 / 1000000000000) (29868804964 / 1000000000000)))) (orderedInterval (-453056600 / 1000000000000) (-453056039 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (61471902550201 / 800000000000) 2 (IntervalRat.scale (715 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (72204601388 / 1000000000000) (72204653832 / 1000000000000), orderedInterval (-55890634706 / 1000000000000) (-55890582262 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (165122176988197 / 800000000000) 2 (IntervalRat.scale (715 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-8716503149 / 1000000000000) (-8716503116 / 1000000000000), orderedInterval (54869894833 / 1000000000000) (54869894866 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (448338831360849 / 800000000000) 2 (IntervalRat.scale (715 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30573291592 / 1000000000000) (30573356046 / 1000000000000), orderedInterval (-14212984301 / 1000000000000) (-14212919847 / 1000000000000)))) (orderedInterval (5475325275 / 1000000000000) (5475336650 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (330244353976537 / 800000000000) 2 (IntervalRat.scale (715 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-34992762478 / 1000000000000) (-34992716309 / 1000000000000), orderedInterval (17866114271 / 1000000000000) (17866160440 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (565879329373501 / 800000000000) 2 (IntervalRat.scale (715 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-28706275892 / 1000000000000) (-28706275852 / 1000000000000), orderedInterval (-8695060100 / 1000000000000) (-8695060061 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (416824152818359 / 800000000000) 2 (IntervalRat.scale (715 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (10695549778 / 1000000000000) (10695549779 / 1000000000000), orderedInterval (33268164867 / 1000000000000) (33268164868 / 1000000000000)))) (orderedInterval (-4020095979 / 1000000000000) (-4020095911 / 1000000000000))) = true
  rfl'

theorem compactCertificate486_chunkChecks2_1 :
    compactCertificate486.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (639515441564857 / 800000000000) 2 (IntervalRat.scale (715 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (22564057391 / 1000000000000) (22564067688 / 1000000000000), orderedInterval (-16962295308 / 1000000000000) (-16962285010 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (369224412338353 / 800000000000) 2 (IntervalRat.scale (715 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-17855383447 / 1000000000000) (-17855383446 / 1000000000000), orderedInterval (-32546778408 / 1000000000000) (-32546778407 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (655195198963877 / 800000000000) 2 (IntervalRat.scale (715 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (4893696071 / 1000000000000) (4893696072 / 1000000000000), orderedInterval (-27450593896 / 1000000000000) (-27450593894 / 1000000000000)))) (orderedInterval (18615565208 / 1000000000000) (18615574998 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (612168344557913 / 800000000000) 2 (IntervalRat.scale (715 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-15148462583 / 1000000000000) (-15148462418 / 1000000000000), orderedInterval (24555325918 / 1000000000000) (24555326083 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (436872216252329 / 800000000000) 2 (IntervalRat.scale (715 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (8060194701 / 1000000000000) (8060194702 / 1000000000000), orderedInterval (33171095593 / 1000000000000) (33171095594 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (495366530964591 / 800000000000) 2 (IntervalRat.scale (715 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-28570218389 / 1000000000000) (-28570218387 / 1000000000000), orderedInterval (-14532395574 / 1000000000000) (-14532395572 / 1000000000000)))) (orderedInterval (-3476243755 / 1000000000000) (-3476243626 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (412984968961279 / 800000000000) 2 (IntervalRat.scale (715 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (34236758784 / 1000000000000) (34236766056 / 1000000000000), orderedInterval (-7846629110 / 1000000000000) (-7846621838 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (364884744654859 / 800000000000) 2 (IntervalRat.scale (715 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-36533977685 / 1000000000000) (-36533977664 / 1000000000000), orderedInterval (-7772725485 / 1000000000000) (-7772725464 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (105757821067041 / 160000000000) 2 (IntervalRat.scale (715 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (27720556967 / 1000000000000) (27720655648 / 1000000000000), orderedInterval (-13974645825 / 1000000000000) (-13974547144 / 1000000000000)))) (orderedInterval (-6653138342 / 1000000000000) (-6653129440 / 1000000000000))) = true
  rfl'

theorem compactCertificate486_chunkChecks2_2 :
    compactCertificate486.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (292531698800627 / 800000000000) 2 (IntervalRat.scale (715 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (37495935718 / 1000000000000) (37495967697 / 1000000000000), orderedInterval (-18355553005 / 1000000000000) (-18355521026 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (247982360773147 / 800000000000) 2 (IntervalRat.scale (715 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (11419373442 / 1000000000000) (11419373506 / 1000000000000), orderedInterval (-43874530800 / 1000000000000) (-43874530736 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (155175847181641 / 800000000000) 2 (IntervalRat.scale (715 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-1385219608 / 1000000000000) (-1385219603 / 1000000000000), orderedInterval (57276147384 / 1000000000000) (57276147389 / 1000000000000)))) (orderedInterval (6754236333 / 1000000000000) (6754241779 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (83454086705847 / 800000000000) 2 (IntervalRat.scale (715 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-77338113626 / 1000000000000) (-77338113622 / 1000000000000), orderedInterval (-10650013590 / 1000000000000) (-10650013586 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (226594079538541 / 800000000000) 2 (IntervalRat.scale (715 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (45475459680 / 1000000000000) (45475459682 / 1000000000000), orderedInterval (13320944137 / 1000000000000) (13320944139 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (309394843486157 / 800000000000) 2 (IntervalRat.scale (715 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-36389616336 / 1000000000000) (-36389616335 / 1000000000000), orderedInterval (-17894472997 / 1000000000000) (-17894472996 / 1000000000000)))) (orderedInterval (-2741397493 / 1000000000000) (-2741397454 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (130824152818359 / 800000000000) 2 (IntervalRat.scale (715 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (50824657396 / 1000000000000) (50824657397 / 1000000000000), orderedInterval (36036153262 / 1000000000000) (36036153263 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (531792918066839 / 800000000000) 2 (IntervalRat.scale (715 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-14599368559 / 1000000000000) (-14599368416 / 1000000000000), orderedInterval (27297504226 / 1000000000000) (27297504368 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (355213023823801 / 800000000000) 2 (IntervalRat.scale (715 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-36533149667 / 1000000000000) (-36533142009 / 1000000000000), orderedInterval (9996245122 / 1000000000000) (9996252780 / 1000000000000)))) (orderedInterval (-14728871497 / 1000000000000) (-14728869029 / 1000000000000))) = true
  rfl'

theorem compactCertificate486_chunkChecks2 :
    compactCertificate486.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate486.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate486_chunkChecks2_0
    compactCertificate486_chunkChecks2_1 compactCertificate486_chunkChecks2_2

theorem compactCertificate486_chunkChecks3_0 :
    compactCertificate486.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (715 / 2) 3 (IntervalRat.scale (715 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (6034205836 / 1000000000000) (6034205837 / 1000000000000), orderedInterval (41756912695 / 1000000000000) (41756912696 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (210666305549843 / 800000000000) 3 (IntervalRat.scale (715 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (10922954197 / 1000000000000) (10922954198 / 1000000000000), orderedInterval (47919228783 / 1000000000000) (47919228784 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (68125154802419 / 160000000000) 3 (IntervalRat.scale (715 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-24591793277 / 1000000000000) (-24591786943 / 1000000000000), orderedInterval (29868798630 / 1000000000000) (29868804964 / 1000000000000)))) (orderedInterval (-19689099716 / 1000000000000) (-19689099048 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (61471902550201 / 800000000000) 3 (IntervalRat.scale (715 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (72204601388 / 1000000000000) (72204653832 / 1000000000000), orderedInterval (-55890634706 / 1000000000000) (-55890582262 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (165122176988197 / 800000000000) 3 (IntervalRat.scale (715 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-8716503149 / 1000000000000) (-8716503116 / 1000000000000), orderedInterval (54869894833 / 1000000000000) (54869894866 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (448338831360849 / 800000000000) 3 (IntervalRat.scale (715 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30573291592 / 1000000000000) (30573356046 / 1000000000000), orderedInterval (-14212984301 / 1000000000000) (-14212919847 / 1000000000000)))) (orderedInterval (-4299224028 / 1000000000000) (-4299206238 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (330244353976537 / 800000000000) 3 (IntervalRat.scale (715 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-34992762478 / 1000000000000) (-34992716309 / 1000000000000), orderedInterval (17866114271 / 1000000000000) (17866160440 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (565879329373501 / 800000000000) 3 (IntervalRat.scale (715 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-28706275892 / 1000000000000) (-28706275852 / 1000000000000), orderedInterval (-8695060100 / 1000000000000) (-8695060061 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (416824152818359 / 800000000000) 3 (IntervalRat.scale (715 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (10695549778 / 1000000000000) (10695549779 / 1000000000000), orderedInterval (33268164867 / 1000000000000) (33268164868 / 1000000000000)))) (orderedInterval (-4555157785 / 1000000000000) (-4555157662 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate486_chunkChecks3_1 :
    compactCertificate486.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (639515441564857 / 800000000000) 3 (IntervalRat.scale (715 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (22564057391 / 1000000000000) (22564067688 / 1000000000000), orderedInterval (-16962295308 / 1000000000000) (-16962285010 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (369224412338353 / 800000000000) 3 (IntervalRat.scale (715 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-17855383447 / 1000000000000) (-17855383446 / 1000000000000), orderedInterval (-32546778408 / 1000000000000) (-32546778407 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (655195198963877 / 800000000000) 3 (IntervalRat.scale (715 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (4893696071 / 1000000000000) (4893696072 / 1000000000000), orderedInterval (-27450593896 / 1000000000000) (-27450593894 / 1000000000000)))) (orderedInterval (18356050488 / 1000000000000) (18356072354 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (612168344557913 / 800000000000) 3 (IntervalRat.scale (715 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-15148462583 / 1000000000000) (-15148462418 / 1000000000000), orderedInterval (24555325918 / 1000000000000) (24555326083 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (436872216252329 / 800000000000) 3 (IntervalRat.scale (715 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (8060194701 / 1000000000000) (8060194702 / 1000000000000), orderedInterval (33171095593 / 1000000000000) (33171095594 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (495366530964591 / 800000000000) 3 (IntervalRat.scale (715 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-28570218389 / 1000000000000) (-28570218387 / 1000000000000), orderedInterval (-14532395574 / 1000000000000) (-14532395572 / 1000000000000)))) (orderedInterval (-7205260082 / 1000000000000) (-7205259859 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (412984968961279 / 800000000000) 3 (IntervalRat.scale (715 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (34236758784 / 1000000000000) (34236766056 / 1000000000000), orderedInterval (-7846629110 / 1000000000000) (-7846621838 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (364884744654859 / 800000000000) 3 (IntervalRat.scale (715 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-36533977685 / 1000000000000) (-36533977664 / 1000000000000), orderedInterval (-7772725485 / 1000000000000) (-7772725464 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (105757821067041 / 160000000000) 3 (IntervalRat.scale (715 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (27720556967 / 1000000000000) (27720655648 / 1000000000000), orderedInterval (-13974645825 / 1000000000000) (-13974547144 / 1000000000000)))) (orderedInterval (1629197751 / 1000000000000) (1629214114 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate486_chunkChecks3_2 :
    compactCertificate486.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (292531698800627 / 800000000000) 3 (IntervalRat.scale (715 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (37495935718 / 1000000000000) (37495967697 / 1000000000000), orderedInterval (-18355553005 / 1000000000000) (-18355521026 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (247982360773147 / 800000000000) 3 (IntervalRat.scale (715 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (11419373442 / 1000000000000) (11419373506 / 1000000000000), orderedInterval (-43874530800 / 1000000000000) (-43874530736 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (155175847181641 / 800000000000) 3 (IntervalRat.scale (715 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-1385219608 / 1000000000000) (-1385219603 / 1000000000000), orderedInterval (57276147384 / 1000000000000) (57276147389 / 1000000000000)))) (orderedInterval (-5076099315 / 1000000000000) (-5076093749 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (83454086705847 / 800000000000) 3 (IntervalRat.scale (715 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-77338113626 / 1000000000000) (-77338113622 / 1000000000000), orderedInterval (-10650013590 / 1000000000000) (-10650013586 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (226594079538541 / 800000000000) 3 (IntervalRat.scale (715 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (45475459680 / 1000000000000) (45475459682 / 1000000000000), orderedInterval (13320944137 / 1000000000000) (13320944139 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (309394843486157 / 800000000000) 3 (IntervalRat.scale (715 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-36389616336 / 1000000000000) (-36389616335 / 1000000000000), orderedInterval (-17894472997 / 1000000000000) (-17894472996 / 1000000000000)))) (orderedInterval (-1583145650 / 1000000000000) (-1583145610 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (130824152818359 / 800000000000) 3 (IntervalRat.scale (715 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (50824657396 / 1000000000000) (50824657397 / 1000000000000), orderedInterval (36036153262 / 1000000000000) (36036153263 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (531792918066839 / 800000000000) 3 (IntervalRat.scale (715 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-14599368559 / 1000000000000) (-14599368416 / 1000000000000), orderedInterval (27297504226 / 1000000000000) (27297504368 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (355213023823801 / 800000000000) 3 (IntervalRat.scale (715 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-36533149667 / 1000000000000) (-36533142009 / 1000000000000), orderedInterval (9996245122 / 1000000000000) (9996252780 / 1000000000000)))) (orderedInterval (17898910484 / 1000000000000) (17898913635 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate486_chunkChecks3 :
    compactCertificate486.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate486.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate486_chunkChecks3_0
    compactCertificate486_chunkChecks3_1 compactCertificate486_chunkChecks3_2

theorem compactCertificate486_chunkChecks4_0 :
    compactCertificate486.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (715 / 2) 4 (IntervalRat.scale (715 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (6034205836 / 1000000000000) (6034205837 / 1000000000000), orderedInterval (41756912695 / 1000000000000) (41756912696 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (210666305549843 / 800000000000) 4 (IntervalRat.scale (715 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (10922954197 / 1000000000000) (10922954198 / 1000000000000), orderedInterval (47919228783 / 1000000000000) (47919228784 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (68125154802419 / 160000000000) 4 (IntervalRat.scale (715 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-24591793277 / 1000000000000) (-24591786943 / 1000000000000), orderedInterval (29868798630 / 1000000000000) (29868804964 / 1000000000000)))) (orderedInterval (-371730071 / 1000000000000) (-371729275 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (61471902550201 / 800000000000) 4 (IntervalRat.scale (715 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (72204601388 / 1000000000000) (72204653832 / 1000000000000), orderedInterval (-55890634706 / 1000000000000) (-55890582262 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (165122176988197 / 800000000000) 4 (IntervalRat.scale (715 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-8716503149 / 1000000000000) (-8716503116 / 1000000000000), orderedInterval (54869894833 / 1000000000000) (54869894866 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (448338831360849 / 800000000000) 4 (IntervalRat.scale (715 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30573291592 / 1000000000000) (30573356046 / 1000000000000), orderedInterval (-14212984301 / 1000000000000) (-14212919847 / 1000000000000)))) (orderedInterval (-13138284229 / 1000000000000) (-13138256303 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (330244353976537 / 800000000000) 4 (IntervalRat.scale (715 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-34992762478 / 1000000000000) (-34992716309 / 1000000000000), orderedInterval (17866114271 / 1000000000000) (17866160440 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (565879329373501 / 800000000000) 4 (IntervalRat.scale (715 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-28706275892 / 1000000000000) (-28706275852 / 1000000000000), orderedInterval (-8695060100 / 1000000000000) (-8695060061 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (416824152818359 / 800000000000) 4 (IntervalRat.scale (715 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (10695549778 / 1000000000000) (10695549779 / 1000000000000), orderedInterval (33268164867 / 1000000000000) (33268164868 / 1000000000000)))) (orderedInterval (14761667594 / 1000000000000) (14761667822 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate486_chunkChecks4_1 :
    compactCertificate486.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (639515441564857 / 800000000000) 4 (IntervalRat.scale (715 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (22564057391 / 1000000000000) (22564067688 / 1000000000000), orderedInterval (-16962295308 / 1000000000000) (-16962285010 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (369224412338353 / 800000000000) 4 (IntervalRat.scale (715 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-17855383447 / 1000000000000) (-17855383446 / 1000000000000), orderedInterval (-32546778408 / 1000000000000) (-32546778407 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (655195198963877 / 800000000000) 4 (IntervalRat.scale (715 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (4893696071 / 1000000000000) (4893696072 / 1000000000000), orderedInterval (-27450593896 / 1000000000000) (-27450593894 / 1000000000000)))) (orderedInterval (-84850326731 / 1000000000000) (-84850277809 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (612168344557913 / 800000000000) 4 (IntervalRat.scale (715 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-15148462583 / 1000000000000) (-15148462418 / 1000000000000), orderedInterval (24555325918 / 1000000000000) (24555326083 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (436872216252329 / 800000000000) 4 (IntervalRat.scale (715 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (8060194701 / 1000000000000) (8060194702 / 1000000000000), orderedInterval (33171095593 / 1000000000000) (33171095594 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (495366530964591 / 800000000000) 4 (IntervalRat.scale (715 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-28570218389 / 1000000000000) (-28570218387 / 1000000000000), orderedInterval (-14532395574 / 1000000000000) (-14532395572 / 1000000000000)))) (orderedInterval (11231609341 / 1000000000000) (11231609741 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (412984968961279 / 800000000000) 4 (IntervalRat.scale (715 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (34236758784 / 1000000000000) (34236766056 / 1000000000000), orderedInterval (-7846629110 / 1000000000000) (-7846621838 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (364884744654859 / 800000000000) 4 (IntervalRat.scale (715 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-36533977685 / 1000000000000) (-36533977664 / 1000000000000), orderedInterval (-7772725485 / 1000000000000) (-7772725464 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (105757821067041 / 160000000000) 4 (IntervalRat.scale (715 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (27720556967 / 1000000000000) (27720655648 / 1000000000000), orderedInterval (-13974645825 / 1000000000000) (-13974547144 / 1000000000000)))) (orderedInterval (15543266339 / 1000000000000) (15543296504 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate486_chunkChecks4_2 :
    compactCertificate486.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (292531698800627 / 800000000000) 4 (IntervalRat.scale (715 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (37495935718 / 1000000000000) (37495967697 / 1000000000000), orderedInterval (-18355553005 / 1000000000000) (-18355521026 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (247982360773147 / 800000000000) 4 (IntervalRat.scale (715 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (11419373442 / 1000000000000) (11419373506 / 1000000000000), orderedInterval (-43874530800 / 1000000000000) (-43874530736 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (155175847181641 / 800000000000) 4 (IntervalRat.scale (715 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-1385219608 / 1000000000000) (-1385219603 / 1000000000000), orderedInterval (57276147384 / 1000000000000) (57276147389 / 1000000000000)))) (orderedInterval (-6902839648 / 1000000000000) (-6902833942 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (83454086705847 / 800000000000) 4 (IntervalRat.scale (715 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-77338113626 / 1000000000000) (-77338113622 / 1000000000000), orderedInterval (-10650013590 / 1000000000000) (-10650013586 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (226594079538541 / 800000000000) 4 (IntervalRat.scale (715 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (45475459680 / 1000000000000) (45475459682 / 1000000000000), orderedInterval (13320944137 / 1000000000000) (13320944139 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (309394843486157 / 800000000000) 4 (IntervalRat.scale (715 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-36389616336 / 1000000000000) (-36389616335 / 1000000000000), orderedInterval (-17894472997 / 1000000000000) (-17894472996 / 1000000000000)))) (orderedInterval (3432240851 / 1000000000000) (3432240893 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (130824152818359 / 800000000000) 4 (IntervalRat.scale (715 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (50824657396 / 1000000000000) (50824657397 / 1000000000000), orderedInterval (36036153262 / 1000000000000) (36036153263 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (531792918066839 / 800000000000) 4 (IntervalRat.scale (715 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-14599368559 / 1000000000000) (-14599368416 / 1000000000000), orderedInterval (27297504226 / 1000000000000) (27297504368 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (355213023823801 / 800000000000) 4 (IntervalRat.scale (715 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-36533149667 / 1000000000000) (-36533142009 / 1000000000000), orderedInterval (9996245122 / 1000000000000) (9996252780 / 1000000000000)))) (orderedInterval (30429939212 / 1000000000000) (30429943294 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate486_chunkChecks4 :
    compactCertificate486.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate486.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate486_chunkChecks4_0
    compactCertificate486_chunkChecks4_1 compactCertificate486_chunkChecks4_2

theorem compactCertificate486_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate486.chunkCheck r b = true :=
  compactCertificate486.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate486_chunkChecks0
    · exact compactCertificate486_chunkChecks1
    · exact compactCertificate486_chunkChecks2
    · exact compactCertificate486_chunkChecks3
    · exact compactCertificate486_chunkChecks4)

theorem compactCertificate486_coefficient0 :
    compactCertificate486.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate486_coefficient1 :
    compactCertificate486.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate486_coefficient2 :
    compactCertificate486.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate486_coefficient3 :
    compactCertificate486.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate486_coefficient4 :
    compactCertificate486.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate486_coefficients : ∀ r : Fin 5,
    compactCertificate486.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate486_coefficient0
  · exact compactCertificate486_coefficient1
  · exact compactCertificate486_coefficient2
  · exact compactCertificate486_coefficient3
  · exact compactCertificate486_coefficient4

theorem compactCertificate486_lower : (1 : ℚ) ≤ compactCertificate486.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate486, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate486_proves {t : ℝ} (ht : t ∈ compactCertificate486.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate486.proves compactCertificate486_states compactCertificate486_chunks
    compactCertificate486_coefficients compactCertificate486_lower ht

end Erdos232
