/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate542 : CompactCertificate where
  left := 413
  right := 414
  center := 827 / 2
  grid := fun i =>
    match i.val with
    | 0 => 132
    | 1 => 97
    | 2 => 157
    | 3 => 28
    | 4 => 76
    | 5 => 206
    | 6 => 152
    | 7 => 261
    | 8 => 192
    | 9 => 294
    | 10 => 170
    | 11 => 302
    | 12 => 282
    | 13 => 201
    | 14 => 228
    | 15 => 190
    | 16 => 168
    | 17 => 243
    | 18 => 135
    | 19 => 114
    | 20 => 71
    | 21 => 38
    | 22 => 104
    | 23 => 142
    | 24 => 60
    | 25 => 245
    | _ => 164
  point := fun i =>
    match i.val with
    | 0 => 827 / 2
    | 1 => 1218328913914127 / 4000000000000
    | 2 => 393982538612591 / 800000000000
    | 3 => 355505338524589 / 4000000000000
    | 4 => 954937345239433 / 4000000000000
    | 5 => 2592840654093861 / 4000000000000
    | 6 => 1909874690479693 / 4000000000000
    | 7 => 3272602834908289 / 4000000000000
    | 8 => 2410584436229251 / 4000000000000
    | 9 => 3698456434784173 / 4000000000000
    | 10 => 2135304818208517 / 4000000000000
    | 11 => 3789135870930953 / 4000000000000
    | 12 => 3540302244401357 / 4000000000000
    | 13 => 2526526733151581 / 4000000000000
    | 14 => 2864812035718299 / 4000000000000
    | 15 => 2388381603713131 / 4000000000000
    | 16 => 2110207579227751 / 4000000000000
    | 17 => 611620405751349 / 800000000000
    | 18 => 1691774230126703 / 4000000000000
    | 19 => 1434135750764983 / 4000000000000
    | 20 => 897415563770749 / 4000000000000
    | 21 => 482633074865283 / 4000000000000
    | 22 => 1310442683764849 / 4000000000000
    | 23 => 1789297451489873 / 4000000000000
    | 24 => 756584436229251 / 4000000000000
    | 25 => 3075473728959971 / 4000000000000
    | _ => 2054273920994989 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-15465187344 / 1000000000000) (-15465187096 / 1000000000000), orderedInterval (36079996412 / 1000000000000) (36079996660 / 1000000000000))
    | 1 => (orderedInterval (-27035243635 / 1000000000000) (-27035243634 / 1000000000000), orderedInterval (-36823455452 / 1000000000000) (-36823455451 / 1000000000000))
    | 2 => (orderedInterval (-1196002682 / 1000000000000) (-1196002681 / 1000000000000), orderedInterval (-35932843551 / 1000000000000) (-35932843550 / 1000000000000))
    | 3 => (orderedInterval (83974081300 / 1000000000000) (83974081481 / 1000000000000), orderedInterval (-11018872345 / 1000000000000) (-11018872165 / 1000000000000))
    | 4 => (orderedInterval (35506981901 / 1000000000000) (35506981902 / 1000000000000), orderedInterval (37420965067 / 1000000000000) (37420965068 / 1000000000000))
    | 5 => (orderedInterval (30313597307 / 1000000000000) (30313616573 / 1000000000000), orderedInterval (-7973508818 / 1000000000000) (-7973489551 / 1000000000000))
    | 6 => (orderedInterval (24397449529 / 1000000000000) (24397449530 / 1000000000000), orderedInterval (27142210403 / 1000000000000) (27142210404 / 1000000000000))
    | 7 => (orderedInterval (23765412370 / 1000000000000) (23765435442 / 1000000000000), orderedInterval (-14620183717 / 1000000000000) (-14620160646 / 1000000000000))
    | 8 => (orderedInterval (7899632291 / 1000000000000) (7899632292 / 1000000000000), orderedInterval (31520740124 / 1000000000000) (31520740125 / 1000000000000))
    | 9 => (orderedInterval (25714936504 / 1000000000000) (25714978241 / 1000000000000), orderedInterval (-5235581279 / 1000000000000) (-5235539543 / 1000000000000))
    | 10 => (orderedInterval (17773176945 / 1000000000000) (17773176946 / 1000000000000), orderedInterval (29592041225 / 1000000000000) (29592041226 / 1000000000000))
    | 11 => (orderedInterval (-16536423851 / 1000000000000) (-16536423545 / 1000000000000), orderedInterval (19973551140 / 1000000000000) (19973551446 / 1000000000000))
    | 12 => (orderedInterval (-1830619582 / 1000000000000) (-1830619581 / 1000000000000), orderedInterval (26757938109 / 1000000000000) (26757938110 / 1000000000000))
    | 13 => (orderedInterval (-25948068721 / 1000000000000) (-25948068720 / 1000000000000), orderedInterval (-18271391386 / 1000000000000) (-18271391385 / 1000000000000))
    | 14 => (orderedInterval (19322997659 / 1000000000000) (19322997660 / 1000000000000), orderedInterval (22691212933 / 1000000000000) (22691212934 / 1000000000000))
    | 15 => (orderedInterval (27081226475 / 1000000000000) (27081226476 / 1000000000000), orderedInterval (18220168581 / 1000000000000) (18220168582 / 1000000000000))
    | 16 => (orderedInterval (18142116510 / 1000000000000) (18142116511 / 1000000000000), orderedInterval (29607242338 / 1000000000000) (29607242339 / 1000000000000))
    | 17 => (orderedInterval (-27272004664 / 1000000000000) (-27271939105 / 1000000000000), orderedInterval (9448526733 / 1000000000000) (9448592292 / 1000000000000))
    | 18 => (orderedInterval (14619046402 / 1000000000000) (14619046583 / 1000000000000), orderedInterval (-35954677589 / 1000000000000) (-35954677408 / 1000000000000))
    | 19 => (orderedInterval (38919653220 / 1000000000000) (38919653221 / 1000000000000), orderedInterval (16097462421 / 1000000000000) (16097462423 / 1000000000000))
    | 20 => (orderedInterval (-46363187686 / 1000000000000) (-46363158701 / 1000000000000), orderedInterval (26333484953 / 1000000000000) (26333513938 / 1000000000000))
    | 21 => (orderedInterval (64045296694 / 1000000000000) (64045310880 / 1000000000000), orderedInterval (-34534856919 / 1000000000000) (-34534842734 / 1000000000000))
    | 22 => (orderedInterval (43864988021 / 1000000000000) (43864988633 / 1000000000000), orderedInterval (-4435136669 / 1000000000000) (-4435136057 / 1000000000000))
    | 23 => (orderedInterval (34250792729 / 1000000000000) (34250830972 / 1000000000000), orderedInterval (-15851394226 / 1000000000000) (-15851355983 / 1000000000000))
    | 24 => (orderedInterval (57483197244 / 1000000000000) (57483197252 / 1000000000000), orderedInterval (7685606368 / 1000000000000) (7685606377 / 1000000000000))
    | 25 => (orderedInterval (1050979970 / 1000000000000) (1050979971 / 1000000000000), orderedInterval (-28756401800 / 1000000000000) (-28756401799 / 1000000000000))
    | _ => (orderedInterval (-26854997290 / 1000000000000) (-26854973732 / 1000000000000), orderedInterval (22794756437 / 1000000000000) (22794779995 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-6451957711 / 1000000000000) (-6451957584 / 1000000000000)
      | 1 => orderedInterval (-1769621487 / 1000000000000) (-1769620065 / 1000000000000)
      | 2 => orderedInterval (-542102600 / 1000000000000) (-542101865 / 1000000000000)
      | 3 => orderedInterval (-5603145160 / 1000000000000) (-5603137536 / 1000000000000)
      | 4 => orderedInterval (-2518460936 / 1000000000000) (-2518460886 / 1000000000000)
      | 5 => orderedInterval (-1423759039 / 1000000000000) (-1423757320 / 1000000000000)
      | 6 => orderedInterval (-6049691909 / 1000000000000) (-6049690833 / 1000000000000)
      | 7 => orderedInterval (-4802708110 / 1000000000000) (-4802704853 / 1000000000000)
      | _ => orderedInterval (5299681327 / 1000000000000) (5299685862 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (11536787157 / 1000000000000) (11536787289 / 1000000000000)
      | 1 => orderedInterval (1703108439 / 1000000000000) (1703110644 / 1000000000000)
      | 2 => orderedInterval (2002497215 / 1000000000000) (2002498663 / 1000000000000)
      | 3 => orderedInterval (11415399540 / 1000000000000) (11415416562 / 1000000000000)
      | 4 => orderedInterval (-3872115515 / 1000000000000) (-3872115435 / 1000000000000)
      | 5 => orderedInterval (-1410546605 / 1000000000000) (-1410543444 / 1000000000000)
      | 6 => orderedInterval (5555316890 / 1000000000000) (5555317528 / 1000000000000)
      | 7 => orderedInterval (1579998971 / 1000000000000) (1580002274 / 1000000000000)
      | _ => orderedInterval (-938176895 / 1000000000000) (-938171244 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (6338194066 / 1000000000000) (6338194203 / 1000000000000)
      | 1 => orderedInterval (4901542512 / 1000000000000) (4901545962 / 1000000000000)
      | 2 => orderedInterval (2459296323 / 1000000000000) (2459299184 / 1000000000000)
      | 3 => orderedInterval (32960994992 / 1000000000000) (32961033070 / 1000000000000)
      | 4 => orderedInterval (5876664453 / 1000000000000) (5876664586 / 1000000000000)
      | 5 => orderedInterval (3428271835 / 1000000000000) (3428277666 / 1000000000000)
      | 6 => orderedInterval (4532491853 / 1000000000000) (4532492254 / 1000000000000)
      | 7 => orderedInterval (3793500067 / 1000000000000) (3793503581 / 1000000000000)
      | _ => orderedInterval (-7547027254 / 1000000000000) (-7547020185 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-10616725586 / 1000000000000) (-10616725443 / 1000000000000)
      | 1 => orderedInterval (-2459594936 / 1000000000000) (-2459589534 / 1000000000000)
      | 2 => orderedInterval (-5857217569 / 1000000000000) (-5857211919 / 1000000000000)
      | 3 => orderedInterval (-49335971919 / 1000000000000) (-49335886798 / 1000000000000)
      | 4 => orderedInterval (11477860102 / 1000000000000) (11477860327 / 1000000000000)
      | 5 => orderedInterval (1347701964 / 1000000000000) (1347712719 / 1000000000000)
      | 6 => orderedInterval (-5705753095 / 1000000000000) (-5705752823 / 1000000000000)
      | 7 => orderedInterval (-1613054626 / 1000000000000) (-1613050847 / 1000000000000)
      | _ => orderedInterval (-6840820124 / 1000000000000) (-6840811272 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-6293845452 / 1000000000000) (-6293845302 / 1000000000000)
      | 1 => orderedInterval (-12859809559 / 1000000000000) (-12859801082 / 1000000000000)
      | 2 => orderedInterval (-10344617357 / 1000000000000) (-10344606182 / 1000000000000)
      | 3 => orderedInterval (-175082126500 / 1000000000000) (-175081935952 / 1000000000000)
      | 4 => orderedInterval (-13601017987 / 1000000000000) (-13601017597 / 1000000000000)
      | 5 => orderedInterval (-9557529629 / 1000000000000) (-9557509753 / 1000000000000)
      | 6 => orderedInterval (-3906717789 / 1000000000000) (-3906717587 / 1000000000000)
      | 7 => orderedInterval (-3987951116 / 1000000000000) (-3987947029 / 1000000000000)
      | _ => orderedInterval (11015303452 / 1000000000000) (11015314599 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-23861765625 / 1000000000000) (-23861745080 / 1000000000000)
    | 1 => orderedInterval (27572269197 / 1000000000000) (27572302837 / 1000000000000)
    | 2 => orderedInterval (56743928847 / 1000000000000) (56743990321 / 1000000000000)
    | 3 => orderedInterval (-69603575789 / 1000000000000) (-69603455590 / 1000000000000)
    | _ => orderedInterval (-224618311937 / 1000000000000) (-224618065885 / 1000000000000)

theorem compactCertificate542_stateChecks0 :
    compactCertificate542.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 132 12 (827 / 2)) (orderedInterval (-15465187344 / 1000000000000) (-15465187096 / 1000000000000), orderedInterval (36079996412 / 1000000000000) (36079996660 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 97 12 (1218328913914127 / 4000000000000)) (orderedInterval (-27035243635 / 1000000000000) (-27035243634 / 1000000000000), orderedInterval (-36823455452 / 1000000000000) (-36823455451 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 157 12 (393982538612591 / 800000000000)) (orderedInterval (-1196002682 / 1000000000000) (-1196002681 / 1000000000000), orderedInterval (-35932843551 / 1000000000000) (-35932843550 / 1000000000000))) = true
  rfl'

theorem compactCertificate542_stateChecks1 :
    compactCertificate542.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 28 12 (355505338524589 / 4000000000000)) (orderedInterval (83974081300 / 1000000000000) (83974081481 / 1000000000000), orderedInterval (-11018872345 / 1000000000000) (-11018872165 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 76 12 (954937345239433 / 4000000000000)) (orderedInterval (35506981901 / 1000000000000) (35506981902 / 1000000000000), orderedInterval (37420965067 / 1000000000000) (37420965068 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 206 12 (2592840654093861 / 4000000000000)) (orderedInterval (30313597307 / 1000000000000) (30313616573 / 1000000000000), orderedInterval (-7973508818 / 1000000000000) (-7973489551 / 1000000000000))) = true
  rfl'

theorem compactCertificate542_stateChecks2 :
    compactCertificate542.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 152 12 (1909874690479693 / 4000000000000)) (orderedInterval (24397449529 / 1000000000000) (24397449530 / 1000000000000), orderedInterval (27142210403 / 1000000000000) (27142210404 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 261 12 (3272602834908289 / 4000000000000)) (orderedInterval (23765412370 / 1000000000000) (23765435442 / 1000000000000), orderedInterval (-14620183717 / 1000000000000) (-14620160646 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 192 12 (2410584436229251 / 4000000000000)) (orderedInterval (7899632291 / 1000000000000) (7899632292 / 1000000000000), orderedInterval (31520740124 / 1000000000000) (31520740125 / 1000000000000))) = true
  rfl'

theorem compactCertificate542_stateChecks3 :
    compactCertificate542.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 294 12 (3698456434784173 / 4000000000000)) (orderedInterval (25714936504 / 1000000000000) (25714978241 / 1000000000000), orderedInterval (-5235581279 / 1000000000000) (-5235539543 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 170 12 (2135304818208517 / 4000000000000)) (orderedInterval (17773176945 / 1000000000000) (17773176946 / 1000000000000), orderedInterval (29592041225 / 1000000000000) (29592041226 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 302 12 (3789135870930953 / 4000000000000)) (orderedInterval (-16536423851 / 1000000000000) (-16536423545 / 1000000000000), orderedInterval (19973551140 / 1000000000000) (19973551446 / 1000000000000))) = true
  rfl'

theorem compactCertificate542_stateChecks4 :
    compactCertificate542.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 282 12 (3540302244401357 / 4000000000000)) (orderedInterval (-1830619582 / 1000000000000) (-1830619581 / 1000000000000), orderedInterval (26757938109 / 1000000000000) (26757938110 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 201 12 (2526526733151581 / 4000000000000)) (orderedInterval (-25948068721 / 1000000000000) (-25948068720 / 1000000000000), orderedInterval (-18271391386 / 1000000000000) (-18271391385 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 228 12 (2864812035718299 / 4000000000000)) (orderedInterval (19322997659 / 1000000000000) (19322997660 / 1000000000000), orderedInterval (22691212933 / 1000000000000) (22691212934 / 1000000000000))) = true
  rfl'

theorem compactCertificate542_stateChecks5 :
    compactCertificate542.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 190 12 (2388381603713131 / 4000000000000)) (orderedInterval (27081226475 / 1000000000000) (27081226476 / 1000000000000), orderedInterval (18220168581 / 1000000000000) (18220168582 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 168 12 (2110207579227751 / 4000000000000)) (orderedInterval (18142116510 / 1000000000000) (18142116511 / 1000000000000), orderedInterval (29607242338 / 1000000000000) (29607242339 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 243 12 (611620405751349 / 800000000000)) (orderedInterval (-27272004664 / 1000000000000) (-27271939105 / 1000000000000), orderedInterval (9448526733 / 1000000000000) (9448592292 / 1000000000000))) = true
  rfl'

theorem compactCertificate542_stateChecks6 :
    compactCertificate542.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 135 12 (1691774230126703 / 4000000000000)) (orderedInterval (14619046402 / 1000000000000) (14619046583 / 1000000000000), orderedInterval (-35954677589 / 1000000000000) (-35954677408 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 114 12 (1434135750764983 / 4000000000000)) (orderedInterval (38919653220 / 1000000000000) (38919653221 / 1000000000000), orderedInterval (16097462421 / 1000000000000) (16097462423 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (897415563770749 / 4000000000000)) (orderedInterval (-46363187686 / 1000000000000) (-46363158701 / 1000000000000), orderedInterval (26333484953 / 1000000000000) (26333513938 / 1000000000000))) = true
  rfl'

theorem compactCertificate542_stateChecks7 :
    compactCertificate542.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (482633074865283 / 4000000000000)) (orderedInterval (64045296694 / 1000000000000) (64045310880 / 1000000000000), orderedInterval (-34534856919 / 1000000000000) (-34534842734 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 104 12 (1310442683764849 / 4000000000000)) (orderedInterval (43864988021 / 1000000000000) (43864988633 / 1000000000000), orderedInterval (-4435136669 / 1000000000000) (-4435136057 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 142 12 (1789297451489873 / 4000000000000)) (orderedInterval (34250792729 / 1000000000000) (34250830972 / 1000000000000), orderedInterval (-15851394226 / 1000000000000) (-15851355983 / 1000000000000))) = true
  rfl'

theorem compactCertificate542_stateChecks8 :
    compactCertificate542.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 60 12 (756584436229251 / 4000000000000)) (orderedInterval (57483197244 / 1000000000000) (57483197252 / 1000000000000), orderedInterval (7685606368 / 1000000000000) (7685606377 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 245 12 (3075473728959971 / 4000000000000)) (orderedInterval (1050979970 / 1000000000000) (1050979971 / 1000000000000), orderedInterval (-28756401800 / 1000000000000) (-28756401799 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 164 12 (2054273920994989 / 4000000000000)) (orderedInterval (-26854997290 / 1000000000000) (-26854973732 / 1000000000000), orderedInterval (22794756437 / 1000000000000) (22794779995 / 1000000000000))) = true
  rfl'

theorem compactCertificate542_states : ∀ j,
    BesselStateValid (compactCertificate542.point j) (compactCertificate542.state j) :=
  compactCertificate542.statesValid_of_checks3 compactCertificate542_stateChecks0
    compactCertificate542_stateChecks1 compactCertificate542_stateChecks2
    compactCertificate542_stateChecks3 compactCertificate542_stateChecks4
    compactCertificate542_stateChecks5 compactCertificate542_stateChecks6
    compactCertificate542_stateChecks7 compactCertificate542_stateChecks8

theorem compactCertificate542_chunkChecks0_0 :
    compactCertificate542.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (827 / 2) 0 (IntervalRat.scale (827 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-15465187344 / 1000000000000) (-15465187096 / 1000000000000), orderedInterval (36079996412 / 1000000000000) (36079996660 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1218328913914127 / 4000000000000) 0 (IntervalRat.scale (827 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-27035243635 / 1000000000000) (-27035243634 / 1000000000000), orderedInterval (-36823455452 / 1000000000000) (-36823455451 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (393982538612591 / 800000000000) 0 (IntervalRat.scale (827 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-1196002682 / 1000000000000) (-1196002681 / 1000000000000), orderedInterval (-35932843551 / 1000000000000) (-35932843550 / 1000000000000)))) (orderedInterval (-6451957711 / 1000000000000) (-6451957584 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (355505338524589 / 4000000000000) 0 (IntervalRat.scale (827 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (83974081300 / 1000000000000) (83974081481 / 1000000000000), orderedInterval (-11018872345 / 1000000000000) (-11018872165 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (954937345239433 / 4000000000000) 0 (IntervalRat.scale (827 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (35506981901 / 1000000000000) (35506981902 / 1000000000000), orderedInterval (37420965067 / 1000000000000) (37420965068 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2592840654093861 / 4000000000000) 0 (IntervalRat.scale (827 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30313597307 / 1000000000000) (30313616573 / 1000000000000), orderedInterval (-7973508818 / 1000000000000) (-7973489551 / 1000000000000)))) (orderedInterval (-1769621487 / 1000000000000) (-1769620065 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1909874690479693 / 4000000000000) 0 (IntervalRat.scale (827 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (24397449529 / 1000000000000) (24397449530 / 1000000000000), orderedInterval (27142210403 / 1000000000000) (27142210404 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3272602834908289 / 4000000000000) 0 (IntervalRat.scale (827 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (23765412370 / 1000000000000) (23765435442 / 1000000000000), orderedInterval (-14620183717 / 1000000000000) (-14620160646 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2410584436229251 / 4000000000000) 0 (IntervalRat.scale (827 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (7899632291 / 1000000000000) (7899632292 / 1000000000000), orderedInterval (31520740124 / 1000000000000) (31520740125 / 1000000000000)))) (orderedInterval (-542102600 / 1000000000000) (-542101865 / 1000000000000))) = true
  rfl'

theorem compactCertificate542_chunkChecks0_1 :
    compactCertificate542.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3698456434784173 / 4000000000000) 0 (IntervalRat.scale (827 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (25714936504 / 1000000000000) (25714978241 / 1000000000000), orderedInterval (-5235581279 / 1000000000000) (-5235539543 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2135304818208517 / 4000000000000) 0 (IntervalRat.scale (827 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (17773176945 / 1000000000000) (17773176946 / 1000000000000), orderedInterval (29592041225 / 1000000000000) (29592041226 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3789135870930953 / 4000000000000) 0 (IntervalRat.scale (827 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-16536423851 / 1000000000000) (-16536423545 / 1000000000000), orderedInterval (19973551140 / 1000000000000) (19973551446 / 1000000000000)))) (orderedInterval (-5603145160 / 1000000000000) (-5603137536 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3540302244401357 / 4000000000000) 0 (IntervalRat.scale (827 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-1830619582 / 1000000000000) (-1830619581 / 1000000000000), orderedInterval (26757938109 / 1000000000000) (26757938110 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2526526733151581 / 4000000000000) 0 (IntervalRat.scale (827 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-25948068721 / 1000000000000) (-25948068720 / 1000000000000), orderedInterval (-18271391386 / 1000000000000) (-18271391385 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2864812035718299 / 4000000000000) 0 (IntervalRat.scale (827 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (19322997659 / 1000000000000) (19322997660 / 1000000000000), orderedInterval (22691212933 / 1000000000000) (22691212934 / 1000000000000)))) (orderedInterval (-2518460936 / 1000000000000) (-2518460886 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2388381603713131 / 4000000000000) 0 (IntervalRat.scale (827 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (27081226475 / 1000000000000) (27081226476 / 1000000000000), orderedInterval (18220168581 / 1000000000000) (18220168582 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2110207579227751 / 4000000000000) 0 (IntervalRat.scale (827 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (18142116510 / 1000000000000) (18142116511 / 1000000000000), orderedInterval (29607242338 / 1000000000000) (29607242339 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (611620405751349 / 800000000000) 0 (IntervalRat.scale (827 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-27272004664 / 1000000000000) (-27271939105 / 1000000000000), orderedInterval (9448526733 / 1000000000000) (9448592292 / 1000000000000)))) (orderedInterval (-1423759039 / 1000000000000) (-1423757320 / 1000000000000))) = true
  rfl'

theorem compactCertificate542_chunkChecks0_2 :
    compactCertificate542.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1691774230126703 / 4000000000000) 0 (IntervalRat.scale (827 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (14619046402 / 1000000000000) (14619046583 / 1000000000000), orderedInterval (-35954677589 / 1000000000000) (-35954677408 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1434135750764983 / 4000000000000) 0 (IntervalRat.scale (827 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (38919653220 / 1000000000000) (38919653221 / 1000000000000), orderedInterval (16097462421 / 1000000000000) (16097462423 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (897415563770749 / 4000000000000) 0 (IntervalRat.scale (827 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-46363187686 / 1000000000000) (-46363158701 / 1000000000000), orderedInterval (26333484953 / 1000000000000) (26333513938 / 1000000000000)))) (orderedInterval (-6049691909 / 1000000000000) (-6049690833 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (482633074865283 / 4000000000000) 0 (IntervalRat.scale (827 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (64045296694 / 1000000000000) (64045310880 / 1000000000000), orderedInterval (-34534856919 / 1000000000000) (-34534842734 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1310442683764849 / 4000000000000) 0 (IntervalRat.scale (827 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (43864988021 / 1000000000000) (43864988633 / 1000000000000), orderedInterval (-4435136669 / 1000000000000) (-4435136057 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1789297451489873 / 4000000000000) 0 (IntervalRat.scale (827 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (34250792729 / 1000000000000) (34250830972 / 1000000000000), orderedInterval (-15851394226 / 1000000000000) (-15851355983 / 1000000000000)))) (orderedInterval (-4802708110 / 1000000000000) (-4802704853 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (756584436229251 / 4000000000000) 0 (IntervalRat.scale (827 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (57483197244 / 1000000000000) (57483197252 / 1000000000000), orderedInterval (7685606368 / 1000000000000) (7685606377 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3075473728959971 / 4000000000000) 0 (IntervalRat.scale (827 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (1050979970 / 1000000000000) (1050979971 / 1000000000000), orderedInterval (-28756401800 / 1000000000000) (-28756401799 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2054273920994989 / 4000000000000) 0 (IntervalRat.scale (827 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-26854997290 / 1000000000000) (-26854973732 / 1000000000000), orderedInterval (22794756437 / 1000000000000) (22794779995 / 1000000000000)))) (orderedInterval (5299681327 / 1000000000000) (5299685862 / 1000000000000))) = true
  rfl'

theorem compactCertificate542_chunkChecks0 :
    compactCertificate542.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate542.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate542_chunkChecks0_0
    compactCertificate542_chunkChecks0_1 compactCertificate542_chunkChecks0_2

theorem compactCertificate542_chunkChecks1_0 :
    compactCertificate542.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (827 / 2) 1 (IntervalRat.scale (827 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-15465187344 / 1000000000000) (-15465187096 / 1000000000000), orderedInterval (36079996412 / 1000000000000) (36079996660 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1218328913914127 / 4000000000000) 1 (IntervalRat.scale (827 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-27035243635 / 1000000000000) (-27035243634 / 1000000000000), orderedInterval (-36823455452 / 1000000000000) (-36823455451 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (393982538612591 / 800000000000) 1 (IntervalRat.scale (827 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-1196002682 / 1000000000000) (-1196002681 / 1000000000000), orderedInterval (-35932843551 / 1000000000000) (-35932843550 / 1000000000000)))) (orderedInterval (11536787157 / 1000000000000) (11536787289 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (355505338524589 / 4000000000000) 1 (IntervalRat.scale (827 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (83974081300 / 1000000000000) (83974081481 / 1000000000000), orderedInterval (-11018872345 / 1000000000000) (-11018872165 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (954937345239433 / 4000000000000) 1 (IntervalRat.scale (827 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (35506981901 / 1000000000000) (35506981902 / 1000000000000), orderedInterval (37420965067 / 1000000000000) (37420965068 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2592840654093861 / 4000000000000) 1 (IntervalRat.scale (827 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30313597307 / 1000000000000) (30313616573 / 1000000000000), orderedInterval (-7973508818 / 1000000000000) (-7973489551 / 1000000000000)))) (orderedInterval (1703108439 / 1000000000000) (1703110644 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1909874690479693 / 4000000000000) 1 (IntervalRat.scale (827 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (24397449529 / 1000000000000) (24397449530 / 1000000000000), orderedInterval (27142210403 / 1000000000000) (27142210404 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3272602834908289 / 4000000000000) 1 (IntervalRat.scale (827 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (23765412370 / 1000000000000) (23765435442 / 1000000000000), orderedInterval (-14620183717 / 1000000000000) (-14620160646 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2410584436229251 / 4000000000000) 1 (IntervalRat.scale (827 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (7899632291 / 1000000000000) (7899632292 / 1000000000000), orderedInterval (31520740124 / 1000000000000) (31520740125 / 1000000000000)))) (orderedInterval (2002497215 / 1000000000000) (2002498663 / 1000000000000))) = true
  rfl'

theorem compactCertificate542_chunkChecks1_1 :
    compactCertificate542.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3698456434784173 / 4000000000000) 1 (IntervalRat.scale (827 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (25714936504 / 1000000000000) (25714978241 / 1000000000000), orderedInterval (-5235581279 / 1000000000000) (-5235539543 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2135304818208517 / 4000000000000) 1 (IntervalRat.scale (827 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (17773176945 / 1000000000000) (17773176946 / 1000000000000), orderedInterval (29592041225 / 1000000000000) (29592041226 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3789135870930953 / 4000000000000) 1 (IntervalRat.scale (827 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-16536423851 / 1000000000000) (-16536423545 / 1000000000000), orderedInterval (19973551140 / 1000000000000) (19973551446 / 1000000000000)))) (orderedInterval (11415399540 / 1000000000000) (11415416562 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3540302244401357 / 4000000000000) 1 (IntervalRat.scale (827 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-1830619582 / 1000000000000) (-1830619581 / 1000000000000), orderedInterval (26757938109 / 1000000000000) (26757938110 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2526526733151581 / 4000000000000) 1 (IntervalRat.scale (827 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-25948068721 / 1000000000000) (-25948068720 / 1000000000000), orderedInterval (-18271391386 / 1000000000000) (-18271391385 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2864812035718299 / 4000000000000) 1 (IntervalRat.scale (827 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (19322997659 / 1000000000000) (19322997660 / 1000000000000), orderedInterval (22691212933 / 1000000000000) (22691212934 / 1000000000000)))) (orderedInterval (-3872115515 / 1000000000000) (-3872115435 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2388381603713131 / 4000000000000) 1 (IntervalRat.scale (827 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (27081226475 / 1000000000000) (27081226476 / 1000000000000), orderedInterval (18220168581 / 1000000000000) (18220168582 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2110207579227751 / 4000000000000) 1 (IntervalRat.scale (827 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (18142116510 / 1000000000000) (18142116511 / 1000000000000), orderedInterval (29607242338 / 1000000000000) (29607242339 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (611620405751349 / 800000000000) 1 (IntervalRat.scale (827 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-27272004664 / 1000000000000) (-27271939105 / 1000000000000), orderedInterval (9448526733 / 1000000000000) (9448592292 / 1000000000000)))) (orderedInterval (-1410546605 / 1000000000000) (-1410543444 / 1000000000000))) = true
  rfl'

theorem compactCertificate542_chunkChecks1_2 :
    compactCertificate542.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1691774230126703 / 4000000000000) 1 (IntervalRat.scale (827 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (14619046402 / 1000000000000) (14619046583 / 1000000000000), orderedInterval (-35954677589 / 1000000000000) (-35954677408 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1434135750764983 / 4000000000000) 1 (IntervalRat.scale (827 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (38919653220 / 1000000000000) (38919653221 / 1000000000000), orderedInterval (16097462421 / 1000000000000) (16097462423 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (897415563770749 / 4000000000000) 1 (IntervalRat.scale (827 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-46363187686 / 1000000000000) (-46363158701 / 1000000000000), orderedInterval (26333484953 / 1000000000000) (26333513938 / 1000000000000)))) (orderedInterval (5555316890 / 1000000000000) (5555317528 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (482633074865283 / 4000000000000) 1 (IntervalRat.scale (827 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (64045296694 / 1000000000000) (64045310880 / 1000000000000), orderedInterval (-34534856919 / 1000000000000) (-34534842734 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1310442683764849 / 4000000000000) 1 (IntervalRat.scale (827 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (43864988021 / 1000000000000) (43864988633 / 1000000000000), orderedInterval (-4435136669 / 1000000000000) (-4435136057 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1789297451489873 / 4000000000000) 1 (IntervalRat.scale (827 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (34250792729 / 1000000000000) (34250830972 / 1000000000000), orderedInterval (-15851394226 / 1000000000000) (-15851355983 / 1000000000000)))) (orderedInterval (1579998971 / 1000000000000) (1580002274 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (756584436229251 / 4000000000000) 1 (IntervalRat.scale (827 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (57483197244 / 1000000000000) (57483197252 / 1000000000000), orderedInterval (7685606368 / 1000000000000) (7685606377 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3075473728959971 / 4000000000000) 1 (IntervalRat.scale (827 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (1050979970 / 1000000000000) (1050979971 / 1000000000000), orderedInterval (-28756401800 / 1000000000000) (-28756401799 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2054273920994989 / 4000000000000) 1 (IntervalRat.scale (827 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-26854997290 / 1000000000000) (-26854973732 / 1000000000000), orderedInterval (22794756437 / 1000000000000) (22794779995 / 1000000000000)))) (orderedInterval (-938176895 / 1000000000000) (-938171244 / 1000000000000))) = true
  rfl'

theorem compactCertificate542_chunkChecks1 :
    compactCertificate542.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate542.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate542_chunkChecks1_0
    compactCertificate542_chunkChecks1_1 compactCertificate542_chunkChecks1_2

theorem compactCertificate542_chunkChecks2_0 :
    compactCertificate542.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (827 / 2) 2 (IntervalRat.scale (827 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-15465187344 / 1000000000000) (-15465187096 / 1000000000000), orderedInterval (36079996412 / 1000000000000) (36079996660 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1218328913914127 / 4000000000000) 2 (IntervalRat.scale (827 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-27035243635 / 1000000000000) (-27035243634 / 1000000000000), orderedInterval (-36823455452 / 1000000000000) (-36823455451 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (393982538612591 / 800000000000) 2 (IntervalRat.scale (827 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-1196002682 / 1000000000000) (-1196002681 / 1000000000000), orderedInterval (-35932843551 / 1000000000000) (-35932843550 / 1000000000000)))) (orderedInterval (6338194066 / 1000000000000) (6338194203 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (355505338524589 / 4000000000000) 2 (IntervalRat.scale (827 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (83974081300 / 1000000000000) (83974081481 / 1000000000000), orderedInterval (-11018872345 / 1000000000000) (-11018872165 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (954937345239433 / 4000000000000) 2 (IntervalRat.scale (827 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (35506981901 / 1000000000000) (35506981902 / 1000000000000), orderedInterval (37420965067 / 1000000000000) (37420965068 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2592840654093861 / 4000000000000) 2 (IntervalRat.scale (827 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30313597307 / 1000000000000) (30313616573 / 1000000000000), orderedInterval (-7973508818 / 1000000000000) (-7973489551 / 1000000000000)))) (orderedInterval (4901542512 / 1000000000000) (4901545962 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1909874690479693 / 4000000000000) 2 (IntervalRat.scale (827 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (24397449529 / 1000000000000) (24397449530 / 1000000000000), orderedInterval (27142210403 / 1000000000000) (27142210404 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3272602834908289 / 4000000000000) 2 (IntervalRat.scale (827 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (23765412370 / 1000000000000) (23765435442 / 1000000000000), orderedInterval (-14620183717 / 1000000000000) (-14620160646 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2410584436229251 / 4000000000000) 2 (IntervalRat.scale (827 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (7899632291 / 1000000000000) (7899632292 / 1000000000000), orderedInterval (31520740124 / 1000000000000) (31520740125 / 1000000000000)))) (orderedInterval (2459296323 / 1000000000000) (2459299184 / 1000000000000))) = true
  rfl'

theorem compactCertificate542_chunkChecks2_1 :
    compactCertificate542.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3698456434784173 / 4000000000000) 2 (IntervalRat.scale (827 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (25714936504 / 1000000000000) (25714978241 / 1000000000000), orderedInterval (-5235581279 / 1000000000000) (-5235539543 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2135304818208517 / 4000000000000) 2 (IntervalRat.scale (827 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (17773176945 / 1000000000000) (17773176946 / 1000000000000), orderedInterval (29592041225 / 1000000000000) (29592041226 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3789135870930953 / 4000000000000) 2 (IntervalRat.scale (827 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-16536423851 / 1000000000000) (-16536423545 / 1000000000000), orderedInterval (19973551140 / 1000000000000) (19973551446 / 1000000000000)))) (orderedInterval (32960994992 / 1000000000000) (32961033070 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3540302244401357 / 4000000000000) 2 (IntervalRat.scale (827 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-1830619582 / 1000000000000) (-1830619581 / 1000000000000), orderedInterval (26757938109 / 1000000000000) (26757938110 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2526526733151581 / 4000000000000) 2 (IntervalRat.scale (827 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-25948068721 / 1000000000000) (-25948068720 / 1000000000000), orderedInterval (-18271391386 / 1000000000000) (-18271391385 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2864812035718299 / 4000000000000) 2 (IntervalRat.scale (827 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (19322997659 / 1000000000000) (19322997660 / 1000000000000), orderedInterval (22691212933 / 1000000000000) (22691212934 / 1000000000000)))) (orderedInterval (5876664453 / 1000000000000) (5876664586 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2388381603713131 / 4000000000000) 2 (IntervalRat.scale (827 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (27081226475 / 1000000000000) (27081226476 / 1000000000000), orderedInterval (18220168581 / 1000000000000) (18220168582 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2110207579227751 / 4000000000000) 2 (IntervalRat.scale (827 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (18142116510 / 1000000000000) (18142116511 / 1000000000000), orderedInterval (29607242338 / 1000000000000) (29607242339 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (611620405751349 / 800000000000) 2 (IntervalRat.scale (827 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-27272004664 / 1000000000000) (-27271939105 / 1000000000000), orderedInterval (9448526733 / 1000000000000) (9448592292 / 1000000000000)))) (orderedInterval (3428271835 / 1000000000000) (3428277666 / 1000000000000))) = true
  rfl'

theorem compactCertificate542_chunkChecks2_2 :
    compactCertificate542.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1691774230126703 / 4000000000000) 2 (IntervalRat.scale (827 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (14619046402 / 1000000000000) (14619046583 / 1000000000000), orderedInterval (-35954677589 / 1000000000000) (-35954677408 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1434135750764983 / 4000000000000) 2 (IntervalRat.scale (827 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (38919653220 / 1000000000000) (38919653221 / 1000000000000), orderedInterval (16097462421 / 1000000000000) (16097462423 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (897415563770749 / 4000000000000) 2 (IntervalRat.scale (827 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-46363187686 / 1000000000000) (-46363158701 / 1000000000000), orderedInterval (26333484953 / 1000000000000) (26333513938 / 1000000000000)))) (orderedInterval (4532491853 / 1000000000000) (4532492254 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (482633074865283 / 4000000000000) 2 (IntervalRat.scale (827 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (64045296694 / 1000000000000) (64045310880 / 1000000000000), orderedInterval (-34534856919 / 1000000000000) (-34534842734 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1310442683764849 / 4000000000000) 2 (IntervalRat.scale (827 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (43864988021 / 1000000000000) (43864988633 / 1000000000000), orderedInterval (-4435136669 / 1000000000000) (-4435136057 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1789297451489873 / 4000000000000) 2 (IntervalRat.scale (827 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (34250792729 / 1000000000000) (34250830972 / 1000000000000), orderedInterval (-15851394226 / 1000000000000) (-15851355983 / 1000000000000)))) (orderedInterval (3793500067 / 1000000000000) (3793503581 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (756584436229251 / 4000000000000) 2 (IntervalRat.scale (827 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (57483197244 / 1000000000000) (57483197252 / 1000000000000), orderedInterval (7685606368 / 1000000000000) (7685606377 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3075473728959971 / 4000000000000) 2 (IntervalRat.scale (827 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (1050979970 / 1000000000000) (1050979971 / 1000000000000), orderedInterval (-28756401800 / 1000000000000) (-28756401799 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2054273920994989 / 4000000000000) 2 (IntervalRat.scale (827 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-26854997290 / 1000000000000) (-26854973732 / 1000000000000), orderedInterval (22794756437 / 1000000000000) (22794779995 / 1000000000000)))) (orderedInterval (-7547027254 / 1000000000000) (-7547020185 / 1000000000000))) = true
  rfl'

theorem compactCertificate542_chunkChecks2 :
    compactCertificate542.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate542.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate542_chunkChecks2_0
    compactCertificate542_chunkChecks2_1 compactCertificate542_chunkChecks2_2

theorem compactCertificate542_chunkChecks3_0 :
    compactCertificate542.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (827 / 2) 3 (IntervalRat.scale (827 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-15465187344 / 1000000000000) (-15465187096 / 1000000000000), orderedInterval (36079996412 / 1000000000000) (36079996660 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1218328913914127 / 4000000000000) 3 (IntervalRat.scale (827 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-27035243635 / 1000000000000) (-27035243634 / 1000000000000), orderedInterval (-36823455452 / 1000000000000) (-36823455451 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (393982538612591 / 800000000000) 3 (IntervalRat.scale (827 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-1196002682 / 1000000000000) (-1196002681 / 1000000000000), orderedInterval (-35932843551 / 1000000000000) (-35932843550 / 1000000000000)))) (orderedInterval (-10616725586 / 1000000000000) (-10616725443 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (355505338524589 / 4000000000000) 3 (IntervalRat.scale (827 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (83974081300 / 1000000000000) (83974081481 / 1000000000000), orderedInterval (-11018872345 / 1000000000000) (-11018872165 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (954937345239433 / 4000000000000) 3 (IntervalRat.scale (827 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (35506981901 / 1000000000000) (35506981902 / 1000000000000), orderedInterval (37420965067 / 1000000000000) (37420965068 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2592840654093861 / 4000000000000) 3 (IntervalRat.scale (827 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30313597307 / 1000000000000) (30313616573 / 1000000000000), orderedInterval (-7973508818 / 1000000000000) (-7973489551 / 1000000000000)))) (orderedInterval (-2459594936 / 1000000000000) (-2459589534 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1909874690479693 / 4000000000000) 3 (IntervalRat.scale (827 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (24397449529 / 1000000000000) (24397449530 / 1000000000000), orderedInterval (27142210403 / 1000000000000) (27142210404 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3272602834908289 / 4000000000000) 3 (IntervalRat.scale (827 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (23765412370 / 1000000000000) (23765435442 / 1000000000000), orderedInterval (-14620183717 / 1000000000000) (-14620160646 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2410584436229251 / 4000000000000) 3 (IntervalRat.scale (827 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (7899632291 / 1000000000000) (7899632292 / 1000000000000), orderedInterval (31520740124 / 1000000000000) (31520740125 / 1000000000000)))) (orderedInterval (-5857217569 / 1000000000000) (-5857211919 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate542_chunkChecks3_1 :
    compactCertificate542.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3698456434784173 / 4000000000000) 3 (IntervalRat.scale (827 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (25714936504 / 1000000000000) (25714978241 / 1000000000000), orderedInterval (-5235581279 / 1000000000000) (-5235539543 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2135304818208517 / 4000000000000) 3 (IntervalRat.scale (827 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (17773176945 / 1000000000000) (17773176946 / 1000000000000), orderedInterval (29592041225 / 1000000000000) (29592041226 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3789135870930953 / 4000000000000) 3 (IntervalRat.scale (827 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-16536423851 / 1000000000000) (-16536423545 / 1000000000000), orderedInterval (19973551140 / 1000000000000) (19973551446 / 1000000000000)))) (orderedInterval (-49335971919 / 1000000000000) (-49335886798 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3540302244401357 / 4000000000000) 3 (IntervalRat.scale (827 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-1830619582 / 1000000000000) (-1830619581 / 1000000000000), orderedInterval (26757938109 / 1000000000000) (26757938110 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2526526733151581 / 4000000000000) 3 (IntervalRat.scale (827 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-25948068721 / 1000000000000) (-25948068720 / 1000000000000), orderedInterval (-18271391386 / 1000000000000) (-18271391385 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2864812035718299 / 4000000000000) 3 (IntervalRat.scale (827 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (19322997659 / 1000000000000) (19322997660 / 1000000000000), orderedInterval (22691212933 / 1000000000000) (22691212934 / 1000000000000)))) (orderedInterval (11477860102 / 1000000000000) (11477860327 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2388381603713131 / 4000000000000) 3 (IntervalRat.scale (827 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (27081226475 / 1000000000000) (27081226476 / 1000000000000), orderedInterval (18220168581 / 1000000000000) (18220168582 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2110207579227751 / 4000000000000) 3 (IntervalRat.scale (827 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (18142116510 / 1000000000000) (18142116511 / 1000000000000), orderedInterval (29607242338 / 1000000000000) (29607242339 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (611620405751349 / 800000000000) 3 (IntervalRat.scale (827 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-27272004664 / 1000000000000) (-27271939105 / 1000000000000), orderedInterval (9448526733 / 1000000000000) (9448592292 / 1000000000000)))) (orderedInterval (1347701964 / 1000000000000) (1347712719 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate542_chunkChecks3_2 :
    compactCertificate542.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1691774230126703 / 4000000000000) 3 (IntervalRat.scale (827 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (14619046402 / 1000000000000) (14619046583 / 1000000000000), orderedInterval (-35954677589 / 1000000000000) (-35954677408 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1434135750764983 / 4000000000000) 3 (IntervalRat.scale (827 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (38919653220 / 1000000000000) (38919653221 / 1000000000000), orderedInterval (16097462421 / 1000000000000) (16097462423 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (897415563770749 / 4000000000000) 3 (IntervalRat.scale (827 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-46363187686 / 1000000000000) (-46363158701 / 1000000000000), orderedInterval (26333484953 / 1000000000000) (26333513938 / 1000000000000)))) (orderedInterval (-5705753095 / 1000000000000) (-5705752823 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (482633074865283 / 4000000000000) 3 (IntervalRat.scale (827 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (64045296694 / 1000000000000) (64045310880 / 1000000000000), orderedInterval (-34534856919 / 1000000000000) (-34534842734 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1310442683764849 / 4000000000000) 3 (IntervalRat.scale (827 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (43864988021 / 1000000000000) (43864988633 / 1000000000000), orderedInterval (-4435136669 / 1000000000000) (-4435136057 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1789297451489873 / 4000000000000) 3 (IntervalRat.scale (827 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (34250792729 / 1000000000000) (34250830972 / 1000000000000), orderedInterval (-15851394226 / 1000000000000) (-15851355983 / 1000000000000)))) (orderedInterval (-1613054626 / 1000000000000) (-1613050847 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (756584436229251 / 4000000000000) 3 (IntervalRat.scale (827 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (57483197244 / 1000000000000) (57483197252 / 1000000000000), orderedInterval (7685606368 / 1000000000000) (7685606377 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3075473728959971 / 4000000000000) 3 (IntervalRat.scale (827 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (1050979970 / 1000000000000) (1050979971 / 1000000000000), orderedInterval (-28756401800 / 1000000000000) (-28756401799 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2054273920994989 / 4000000000000) 3 (IntervalRat.scale (827 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-26854997290 / 1000000000000) (-26854973732 / 1000000000000), orderedInterval (22794756437 / 1000000000000) (22794779995 / 1000000000000)))) (orderedInterval (-6840820124 / 1000000000000) (-6840811272 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate542_chunkChecks3 :
    compactCertificate542.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate542.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate542_chunkChecks3_0
    compactCertificate542_chunkChecks3_1 compactCertificate542_chunkChecks3_2

theorem compactCertificate542_chunkChecks4_0 :
    compactCertificate542.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (827 / 2) 4 (IntervalRat.scale (827 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-15465187344 / 1000000000000) (-15465187096 / 1000000000000), orderedInterval (36079996412 / 1000000000000) (36079996660 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1218328913914127 / 4000000000000) 4 (IntervalRat.scale (827 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-27035243635 / 1000000000000) (-27035243634 / 1000000000000), orderedInterval (-36823455452 / 1000000000000) (-36823455451 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (393982538612591 / 800000000000) 4 (IntervalRat.scale (827 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-1196002682 / 1000000000000) (-1196002681 / 1000000000000), orderedInterval (-35932843551 / 1000000000000) (-35932843550 / 1000000000000)))) (orderedInterval (-6293845452 / 1000000000000) (-6293845302 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (355505338524589 / 4000000000000) 4 (IntervalRat.scale (827 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (83974081300 / 1000000000000) (83974081481 / 1000000000000), orderedInterval (-11018872345 / 1000000000000) (-11018872165 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (954937345239433 / 4000000000000) 4 (IntervalRat.scale (827 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (35506981901 / 1000000000000) (35506981902 / 1000000000000), orderedInterval (37420965067 / 1000000000000) (37420965068 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2592840654093861 / 4000000000000) 4 (IntervalRat.scale (827 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30313597307 / 1000000000000) (30313616573 / 1000000000000), orderedInterval (-7973508818 / 1000000000000) (-7973489551 / 1000000000000)))) (orderedInterval (-12859809559 / 1000000000000) (-12859801082 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1909874690479693 / 4000000000000) 4 (IntervalRat.scale (827 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (24397449529 / 1000000000000) (24397449530 / 1000000000000), orderedInterval (27142210403 / 1000000000000) (27142210404 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3272602834908289 / 4000000000000) 4 (IntervalRat.scale (827 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (23765412370 / 1000000000000) (23765435442 / 1000000000000), orderedInterval (-14620183717 / 1000000000000) (-14620160646 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2410584436229251 / 4000000000000) 4 (IntervalRat.scale (827 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (7899632291 / 1000000000000) (7899632292 / 1000000000000), orderedInterval (31520740124 / 1000000000000) (31520740125 / 1000000000000)))) (orderedInterval (-10344617357 / 1000000000000) (-10344606182 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate542_chunkChecks4_1 :
    compactCertificate542.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3698456434784173 / 4000000000000) 4 (IntervalRat.scale (827 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (25714936504 / 1000000000000) (25714978241 / 1000000000000), orderedInterval (-5235581279 / 1000000000000) (-5235539543 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2135304818208517 / 4000000000000) 4 (IntervalRat.scale (827 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (17773176945 / 1000000000000) (17773176946 / 1000000000000), orderedInterval (29592041225 / 1000000000000) (29592041226 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3789135870930953 / 4000000000000) 4 (IntervalRat.scale (827 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-16536423851 / 1000000000000) (-16536423545 / 1000000000000), orderedInterval (19973551140 / 1000000000000) (19973551446 / 1000000000000)))) (orderedInterval (-175082126500 / 1000000000000) (-175081935952 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3540302244401357 / 4000000000000) 4 (IntervalRat.scale (827 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-1830619582 / 1000000000000) (-1830619581 / 1000000000000), orderedInterval (26757938109 / 1000000000000) (26757938110 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2526526733151581 / 4000000000000) 4 (IntervalRat.scale (827 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-25948068721 / 1000000000000) (-25948068720 / 1000000000000), orderedInterval (-18271391386 / 1000000000000) (-18271391385 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2864812035718299 / 4000000000000) 4 (IntervalRat.scale (827 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (19322997659 / 1000000000000) (19322997660 / 1000000000000), orderedInterval (22691212933 / 1000000000000) (22691212934 / 1000000000000)))) (orderedInterval (-13601017987 / 1000000000000) (-13601017597 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2388381603713131 / 4000000000000) 4 (IntervalRat.scale (827 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (27081226475 / 1000000000000) (27081226476 / 1000000000000), orderedInterval (18220168581 / 1000000000000) (18220168582 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2110207579227751 / 4000000000000) 4 (IntervalRat.scale (827 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (18142116510 / 1000000000000) (18142116511 / 1000000000000), orderedInterval (29607242338 / 1000000000000) (29607242339 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (611620405751349 / 800000000000) 4 (IntervalRat.scale (827 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-27272004664 / 1000000000000) (-27271939105 / 1000000000000), orderedInterval (9448526733 / 1000000000000) (9448592292 / 1000000000000)))) (orderedInterval (-9557529629 / 1000000000000) (-9557509753 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate542_chunkChecks4_2 :
    compactCertificate542.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1691774230126703 / 4000000000000) 4 (IntervalRat.scale (827 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (14619046402 / 1000000000000) (14619046583 / 1000000000000), orderedInterval (-35954677589 / 1000000000000) (-35954677408 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1434135750764983 / 4000000000000) 4 (IntervalRat.scale (827 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (38919653220 / 1000000000000) (38919653221 / 1000000000000), orderedInterval (16097462421 / 1000000000000) (16097462423 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (897415563770749 / 4000000000000) 4 (IntervalRat.scale (827 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-46363187686 / 1000000000000) (-46363158701 / 1000000000000), orderedInterval (26333484953 / 1000000000000) (26333513938 / 1000000000000)))) (orderedInterval (-3906717789 / 1000000000000) (-3906717587 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (482633074865283 / 4000000000000) 4 (IntervalRat.scale (827 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (64045296694 / 1000000000000) (64045310880 / 1000000000000), orderedInterval (-34534856919 / 1000000000000) (-34534842734 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1310442683764849 / 4000000000000) 4 (IntervalRat.scale (827 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (43864988021 / 1000000000000) (43864988633 / 1000000000000), orderedInterval (-4435136669 / 1000000000000) (-4435136057 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1789297451489873 / 4000000000000) 4 (IntervalRat.scale (827 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (34250792729 / 1000000000000) (34250830972 / 1000000000000), orderedInterval (-15851394226 / 1000000000000) (-15851355983 / 1000000000000)))) (orderedInterval (-3987951116 / 1000000000000) (-3987947029 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (756584436229251 / 4000000000000) 4 (IntervalRat.scale (827 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (57483197244 / 1000000000000) (57483197252 / 1000000000000), orderedInterval (7685606368 / 1000000000000) (7685606377 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3075473728959971 / 4000000000000) 4 (IntervalRat.scale (827 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (1050979970 / 1000000000000) (1050979971 / 1000000000000), orderedInterval (-28756401800 / 1000000000000) (-28756401799 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2054273920994989 / 4000000000000) 4 (IntervalRat.scale (827 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-26854997290 / 1000000000000) (-26854973732 / 1000000000000), orderedInterval (22794756437 / 1000000000000) (22794779995 / 1000000000000)))) (orderedInterval (11015303452 / 1000000000000) (11015314599 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate542_chunkChecks4 :
    compactCertificate542.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate542.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate542_chunkChecks4_0
    compactCertificate542_chunkChecks4_1 compactCertificate542_chunkChecks4_2

theorem compactCertificate542_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate542.chunkCheck r b = true :=
  compactCertificate542.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate542_chunkChecks0
    · exact compactCertificate542_chunkChecks1
    · exact compactCertificate542_chunkChecks2
    · exact compactCertificate542_chunkChecks3
    · exact compactCertificate542_chunkChecks4)

theorem compactCertificate542_coefficient0 :
    compactCertificate542.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate542_coefficient1 :
    compactCertificate542.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate542_coefficient2 :
    compactCertificate542.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate542_coefficient3 :
    compactCertificate542.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate542_coefficient4 :
    compactCertificate542.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate542_coefficients : ∀ r : Fin 5,
    compactCertificate542.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate542_coefficient0
  · exact compactCertificate542_coefficient1
  · exact compactCertificate542_coefficient2
  · exact compactCertificate542_coefficient3
  · exact compactCertificate542_coefficient4

theorem compactCertificate542_lower : (1 : ℚ) ≤ compactCertificate542.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate542, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate542_proves {t : ℝ} (ht : t ∈ compactCertificate542.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate542.proves compactCertificate542_states compactCertificate542_chunks
    compactCertificate542_coefficients compactCertificate542_lower ht

end Erdos232
