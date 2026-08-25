/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate445 : CompactCertificate where
  left := 316
  right := 317
  center := 633 / 2
  grid := fun i =>
    match i.val with
    | 0 => 101
    | 1 => 74
    | 2 => 120
    | 3 => 22
    | 4 => 58
    | 5 => 158
    | 6 => 116
    | 7 => 199
    | 8 => 147
    | 9 => 225
    | 10 => 130
    | 11 => 231
    | 12 => 216
    | 13 => 154
    | 14 => 175
    | 15 => 146
    | 16 => 129
    | 17 => 186
    | 18 => 103
    | 19 => 87
    | 20 => 55
    | 21 => 29
    | 22 => 80
    | 23 => 109
    | 24 => 46
    | 25 => 187
    | _ => 125
  point := fun i =>
    match i.val with
    | 0 => 633 / 2
    | 1 => 932529870021333 / 4000000000000
    | 2 => 301560999929589 / 800000000000
    | 3 => 272109890309631 / 4000000000000
    | 4 => 730925440793907 / 4000000000000
    | 5 => 1984604757002919 / 4000000000000
    | 6 => 1461850881588447 / 4000000000000
    | 7 => 2504906402051931 / 4000000000000
    | 8 => 1845102718419729 / 4000000000000
    | 9 => 2830862059514367 / 4000000000000
    | 10 => 1634398972099143 / 4000000000000
    | 11 => 2900269656951987 / 4000000000000
    | 12 => 2709808126609503 / 4000000000000
    | 13 => 1933846943270799 / 4000000000000
    | 14 => 2192776322381721 / 4000000000000
    | 15 => 1828108289178249 / 4000000000000
    | 16 => 1615189114451229 / 4000000000000
    | 17 => 468144760387671 / 800000000000
    | 18 => 1294913044341237 / 4000000000000
    | 19 => 1097712128457357 / 4000000000000
    | 20 => 686897281580271 / 4000000000000
    | 21 => 369415642551057 / 4000000000000
    | 22 => 1003035331104171 / 4000000000000
    | 23 => 1369558992494667 / 4000000000000
    | 24 => 579102718419729 / 4000000000000
    | 25 => 2354020399554609 / 4000000000000
    | _ => 1572376532031231 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (711042044 / 1000000000000) (711042046 / 1000000000000), orderedInterval (-44844559902 / 1000000000000) (-44844559900 / 1000000000000))
    | 1 => (orderedInterval (51806290248 / 1000000000000) (51806290260 / 1000000000000), orderedInterval (6731656126 / 1000000000000) (6731656139 / 1000000000000))
    | 2 => (orderedInterval (27867765485 / 1000000000000) (27867765486 / 1000000000000), orderedInterval (30166557783 / 1000000000000) (30166557784 / 1000000000000))
    | 3 => (orderedInterval (-28957589922 / 1000000000000) (-28957589296 / 1000000000000), orderedInterval (92516347041 / 1000000000000) (92516347667 / 1000000000000))
    | 4 => (orderedInterval (56931627058 / 1000000000000) (56931627060 / 1000000000000), orderedInterval (15422715977 / 1000000000000) (15422715979 / 1000000000000))
    | 5 => (orderedInterval (19169727465 / 1000000000000) (19169727466 / 1000000000000), orderedInterval (30240197726 / 1000000000000) (30240197727 / 1000000000000))
    | 6 => (orderedInterval (40416072304 / 1000000000000) (40416076690 / 1000000000000), orderedInterval (-10471386146 / 1000000000000) (-10471381759 / 1000000000000))
    | 7 => (orderedInterval (-30778917295 / 1000000000000) (-30778898669 / 1000000000000), orderedInterval (8346526210 / 1000000000000) (8346544835 / 1000000000000))
    | 8 => (orderedInterval (-9071761921 / 1000000000000) (-9071761920 / 1000000000000), orderedInterval (-36015608807 / 1000000000000) (-36015608806 / 1000000000000))
    | 9 => (orderedInterval (-29915531549 / 1000000000000) (-29915527487 / 1000000000000), orderedInterval (2166543970 / 1000000000000) (2166548032 / 1000000000000))
    | 10 => (orderedInterval (32732857789 / 1000000000000) (32732857790 / 1000000000000), orderedInterval (22019226417 / 1000000000000) (22019226418 / 1000000000000))
    | 11 => (orderedInterval (-4273788942 / 1000000000000) (-4273788941 / 1000000000000), orderedInterval (-29318538534 / 1000000000000) (-29318538533 / 1000000000000))
    | 12 => (orderedInterval (-10418389517 / 1000000000000) (-10418389502 / 1000000000000), orderedInterval (28837952508 / 1000000000000) (28837952523 / 1000000000000))
    | 13 => (orderedInterval (15509076552 / 1000000000000) (15509076553 / 1000000000000), orderedInterval (32790415990 / 1000000000000) (32790415991 / 1000000000000))
    | 14 => (orderedInterval (24433244542 / 1000000000000) (24433254862 / 1000000000000), orderedInterval (-23777708859 / 1000000000000) (-23777698538 / 1000000000000))
    | 15 => (orderedInterval (-28292524038 / 1000000000000) (-28292495309 / 1000000000000), orderedInterval (24372102949 / 1000000000000) (24372131678 / 1000000000000))
    | 16 => (orderedInterval (25062102666 / 1000000000000) (25062109332 / 1000000000000), orderedInterval (-30828336538 / 1000000000000) (-30828329873 / 1000000000000))
    | 17 => (orderedInterval (32925763313 / 1000000000000) (32925765097 / 1000000000000), orderedInterval (-1976485932 / 1000000000000) (-1976484148 / 1000000000000))
    | 18 => (orderedInterval (-35527802740 / 1000000000000) (-35527802739 / 1000000000000), orderedInterval (-26483773283 / 1000000000000) (-26483773282 / 1000000000000))
    | 19 => (orderedInterval (-45664175716 / 1000000000000) (-45664169991 / 1000000000000), orderedInterval (15399401138 / 1000000000000) (15399406862 / 1000000000000))
    | 20 => (orderedInterval (16744785590 / 1000000000000) (16744785825 / 1000000000000), orderedInterval (-58588015926 / 1000000000000) (-58588015692 / 1000000000000))
    | 21 => (orderedInterval (-74358956862 / 1000000000000) (-74358947709 / 1000000000000), orderedInterval (37334224698 / 1000000000000) (37334233851 / 1000000000000))
    | 22 => (orderedInterval (10814741240 / 1000000000000) (10814741241 / 1000000000000), orderedInterval (49190416572 / 1000000000000) (49190416573 / 1000000000000))
    | 23 => (orderedInterval (-29112958534 / 1000000000000) (-29112958533 / 1000000000000), orderedInterval (-31765947030 / 1000000000000) (-31765947029 / 1000000000000))
    | 24 => (orderedInterval (57419589776 / 1000000000000) (57419589777 / 1000000000000), orderedInterval (32971887838 / 1000000000000) (32971887839 / 1000000000000))
    | 25 => (orderedInterval (-31934338800 / 1000000000000) (-31934326326 / 1000000000000), orderedInterval (7898306394 / 1000000000000) (7898318868 / 1000000000000))
    | _ => (orderedInterval (-37211042653 / 1000000000000) (-37211042652 / 1000000000000), orderedInterval (-15277391057 / 1000000000000) (-15277391056 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (2399878532 / 1000000000000) (2399878556 / 1000000000000)
      | 1 => orderedInterval (1030073357 / 1000000000000) (1030073402 / 1000000000000)
      | 2 => orderedInterval (730097785 / 1000000000000) (730098378 / 1000000000000)
      | 3 => orderedInterval (7133319096 / 1000000000000) (7133319943 / 1000000000000)
      | 4 => orderedInterval (1531020447 / 1000000000000) (1531020538 / 1000000000000)
      | 5 => orderedInterval (-917904385 / 1000000000000) (-917903595 / 1000000000000)
      | 6 => orderedInterval (8810348144 / 1000000000000) (8810348556 / 1000000000000)
      | 7 => orderedInterval (3358878353 / 1000000000000) (3358878560 / 1000000000000)
      | _ => orderedInterval (9927433686 / 1000000000000) (9927434790 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-15620293685 / 1000000000000) (-15620293658 / 1000000000000)
      | 1 => orderedInterval (-3260638661 / 1000000000000) (-3260638616 / 1000000000000)
      | 2 => orderedInterval (-1777954961 / 1000000000000) (-1777953793 / 1000000000000)
      | 3 => orderedInterval (-8302621271 / 1000000000000) (-8302619396 / 1000000000000)
      | 4 => orderedInterval (3830550573 / 1000000000000) (3830550726 / 1000000000000)
      | 5 => orderedInterval (2563642631 / 1000000000000) (2563643726 / 1000000000000)
      | 6 => orderedInterval (2540644417 / 1000000000000) (2540644776 / 1000000000000)
      | 7 => orderedInterval (1548316176 / 1000000000000) (1548316260 / 1000000000000)
      | _ => orderedInterval (2455566522 / 1000000000000) (2455568534 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-2814053695 / 1000000000000) (-2814053665 / 1000000000000)
      | 1 => orderedInterval (2651802770 / 1000000000000) (2651802830 / 1000000000000)
      | 2 => orderedInterval (-3245229272 / 1000000000000) (-3245226964 / 1000000000000)
      | 3 => orderedInterval (-27405464139 / 1000000000000) (-27405459967 / 1000000000000)
      | 4 => orderedInterval (-3924901538 / 1000000000000) (-3924901278 / 1000000000000)
      | 5 => orderedInterval (125771809 / 1000000000000) (125773347 / 1000000000000)
      | 6 => orderedInterval (-8054692718 / 1000000000000) (-8054692400 / 1000000000000)
      | 7 => orderedInterval (-2578924899 / 1000000000000) (-2578924850 / 1000000000000)
      | _ => orderedInterval (-19837711204 / 1000000000000) (-19837707505 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (14767877338 / 1000000000000) (14767877372 / 1000000000000)
      | 1 => orderedInterval (8174740421 / 1000000000000) (8174740511 / 1000000000000)
      | 2 => orderedInterval (4698937843 / 1000000000000) (4698942400 / 1000000000000)
      | 3 => orderedInterval (50989909887 / 1000000000000) (50989919191 / 1000000000000)
      | 4 => orderedInterval (-6559193813 / 1000000000000) (-6559193366 / 1000000000000)
      | 5 => orderedInterval (-4191608191 / 1000000000000) (-4191606006 / 1000000000000)
      | 6 => orderedInterval (-3633054722 / 1000000000000) (-3633054440 / 1000000000000)
      | 7 => orderedInterval (-2501833773 / 1000000000000) (-2501833733 / 1000000000000)
      | _ => orderedInterval (-1314782260 / 1000000000000) (-1314775440 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (3620978472 / 1000000000000) (3620978512 / 1000000000000)
      | 1 => orderedInterval (-8049687808 / 1000000000000) (-8049687670 / 1000000000000)
      | 2 => orderedInterval (13530814564 / 1000000000000) (13530823582 / 1000000000000)
      | 3 => orderedInterval (122571100838 / 1000000000000) (122571121649 / 1000000000000)
      | 4 => orderedInterval (10861267562 / 1000000000000) (10861268339 / 1000000000000)
      | 5 => orderedInterval (4657716001 / 1000000000000) (4657719161 / 1000000000000)
      | 6 => orderedInterval (7748602579 / 1000000000000) (7748602831 / 1000000000000)
      | 7 => orderedInterval (2984852016 / 1000000000000) (2984852054 / 1000000000000)
      | _ => orderedInterval (47710663476 / 1000000000000) (47710676106 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (34003145015 / 1000000000000) (34003149128 / 1000000000000)
    | 1 => orderedInterval (-16022788259 / 1000000000000) (-16022781441 / 1000000000000)
    | 2 => orderedInterval (-65083402886 / 1000000000000) (-65083390452 / 1000000000000)
    | 3 => orderedInterval (60430992730 / 1000000000000) (60431016489 / 1000000000000)
    | _ => orderedInterval (205636307700 / 1000000000000) (205636354564 / 1000000000000)

theorem compactCertificate445_stateChecks0 :
    compactCertificate445.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 101 12 (633 / 2)) (orderedInterval (711042044 / 1000000000000) (711042046 / 1000000000000), orderedInterval (-44844559902 / 1000000000000) (-44844559900 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 74 12 (932529870021333 / 4000000000000)) (orderedInterval (51806290248 / 1000000000000) (51806290260 / 1000000000000), orderedInterval (6731656126 / 1000000000000) (6731656139 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 120 12 (301560999929589 / 800000000000)) (orderedInterval (27867765485 / 1000000000000) (27867765486 / 1000000000000), orderedInterval (30166557783 / 1000000000000) (30166557784 / 1000000000000))) = true
  rfl'

theorem compactCertificate445_stateChecks1 :
    compactCertificate445.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 22 12 (272109890309631 / 4000000000000)) (orderedInterval (-28957589922 / 1000000000000) (-28957589296 / 1000000000000), orderedInterval (92516347041 / 1000000000000) (92516347667 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (730925440793907 / 4000000000000)) (orderedInterval (56931627058 / 1000000000000) (56931627060 / 1000000000000), orderedInterval (15422715977 / 1000000000000) (15422715979 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 158 12 (1984604757002919 / 4000000000000)) (orderedInterval (19169727465 / 1000000000000) (19169727466 / 1000000000000), orderedInterval (30240197726 / 1000000000000) (30240197727 / 1000000000000))) = true
  rfl'

theorem compactCertificate445_stateChecks2 :
    compactCertificate445.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 116 12 (1461850881588447 / 4000000000000)) (orderedInterval (40416072304 / 1000000000000) (40416076690 / 1000000000000), orderedInterval (-10471386146 / 1000000000000) (-10471381759 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 199 12 (2504906402051931 / 4000000000000)) (orderedInterval (-30778917295 / 1000000000000) (-30778898669 / 1000000000000), orderedInterval (8346526210 / 1000000000000) (8346544835 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 147 12 (1845102718419729 / 4000000000000)) (orderedInterval (-9071761921 / 1000000000000) (-9071761920 / 1000000000000), orderedInterval (-36015608807 / 1000000000000) (-36015608806 / 1000000000000))) = true
  rfl'

theorem compactCertificate445_stateChecks3 :
    compactCertificate445.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 225 12 (2830862059514367 / 4000000000000)) (orderedInterval (-29915531549 / 1000000000000) (-29915527487 / 1000000000000), orderedInterval (2166543970 / 1000000000000) (2166548032 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 130 12 (1634398972099143 / 4000000000000)) (orderedInterval (32732857789 / 1000000000000) (32732857790 / 1000000000000), orderedInterval (22019226417 / 1000000000000) (22019226418 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 231 12 (2900269656951987 / 4000000000000)) (orderedInterval (-4273788942 / 1000000000000) (-4273788941 / 1000000000000), orderedInterval (-29318538534 / 1000000000000) (-29318538533 / 1000000000000))) = true
  rfl'

theorem compactCertificate445_stateChecks4 :
    compactCertificate445.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 216 12 (2709808126609503 / 4000000000000)) (orderedInterval (-10418389517 / 1000000000000) (-10418389502 / 1000000000000), orderedInterval (28837952508 / 1000000000000) (28837952523 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 154 12 (1933846943270799 / 4000000000000)) (orderedInterval (15509076552 / 1000000000000) (15509076553 / 1000000000000), orderedInterval (32790415990 / 1000000000000) (32790415991 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 175 12 (2192776322381721 / 4000000000000)) (orderedInterval (24433244542 / 1000000000000) (24433254862 / 1000000000000), orderedInterval (-23777708859 / 1000000000000) (-23777698538 / 1000000000000))) = true
  rfl'

theorem compactCertificate445_stateChecks5 :
    compactCertificate445.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 146 12 (1828108289178249 / 4000000000000)) (orderedInterval (-28292524038 / 1000000000000) (-28292495309 / 1000000000000), orderedInterval (24372102949 / 1000000000000) (24372131678 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 129 12 (1615189114451229 / 4000000000000)) (orderedInterval (25062102666 / 1000000000000) (25062109332 / 1000000000000), orderedInterval (-30828336538 / 1000000000000) (-30828329873 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 186 12 (468144760387671 / 800000000000)) (orderedInterval (32925763313 / 1000000000000) (32925765097 / 1000000000000), orderedInterval (-1976485932 / 1000000000000) (-1976484148 / 1000000000000))) = true
  rfl'

theorem compactCertificate445_stateChecks6 :
    compactCertificate445.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 103 12 (1294913044341237 / 4000000000000)) (orderedInterval (-35527802740 / 1000000000000) (-35527802739 / 1000000000000), orderedInterval (-26483773283 / 1000000000000) (-26483773282 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 87 12 (1097712128457357 / 4000000000000)) (orderedInterval (-45664175716 / 1000000000000) (-45664169991 / 1000000000000), orderedInterval (15399401138 / 1000000000000) (15399406862 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (686897281580271 / 4000000000000)) (orderedInterval (16744785590 / 1000000000000) (16744785825 / 1000000000000), orderedInterval (-58588015926 / 1000000000000) (-58588015692 / 1000000000000))) = true
  rfl'

theorem compactCertificate445_stateChecks7 :
    compactCertificate445.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 29 12 (369415642551057 / 4000000000000)) (orderedInterval (-74358956862 / 1000000000000) (-74358947709 / 1000000000000), orderedInterval (37334224698 / 1000000000000) (37334233851 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 80 12 (1003035331104171 / 4000000000000)) (orderedInterval (10814741240 / 1000000000000) (10814741241 / 1000000000000), orderedInterval (49190416572 / 1000000000000) (49190416573 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 109 12 (1369558992494667 / 4000000000000)) (orderedInterval (-29112958534 / 1000000000000) (-29112958533 / 1000000000000), orderedInterval (-31765947030 / 1000000000000) (-31765947029 / 1000000000000))) = true
  rfl'

theorem compactCertificate445_stateChecks8 :
    compactCertificate445.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (579102718419729 / 4000000000000)) (orderedInterval (57419589776 / 1000000000000) (57419589777 / 1000000000000), orderedInterval (32971887838 / 1000000000000) (32971887839 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 187 12 (2354020399554609 / 4000000000000)) (orderedInterval (-31934338800 / 1000000000000) (-31934326326 / 1000000000000), orderedInterval (7898306394 / 1000000000000) (7898318868 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 125 12 (1572376532031231 / 4000000000000)) (orderedInterval (-37211042653 / 1000000000000) (-37211042652 / 1000000000000), orderedInterval (-15277391057 / 1000000000000) (-15277391056 / 1000000000000))) = true
  rfl'

theorem compactCertificate445_states : ∀ j,
    BesselStateValid (compactCertificate445.point j) (compactCertificate445.state j) :=
  compactCertificate445.statesValid_of_checks3 compactCertificate445_stateChecks0
    compactCertificate445_stateChecks1 compactCertificate445_stateChecks2
    compactCertificate445_stateChecks3 compactCertificate445_stateChecks4
    compactCertificate445_stateChecks5 compactCertificate445_stateChecks6
    compactCertificate445_stateChecks7 compactCertificate445_stateChecks8

theorem compactCertificate445_chunkChecks0_0 :
    compactCertificate445.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (633 / 2) 0 (IntervalRat.scale (633 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (711042044 / 1000000000000) (711042046 / 1000000000000), orderedInterval (-44844559902 / 1000000000000) (-44844559900 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (932529870021333 / 4000000000000) 0 (IntervalRat.scale (633 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (51806290248 / 1000000000000) (51806290260 / 1000000000000), orderedInterval (6731656126 / 1000000000000) (6731656139 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (301560999929589 / 800000000000) 0 (IntervalRat.scale (633 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (27867765485 / 1000000000000) (27867765486 / 1000000000000), orderedInterval (30166557783 / 1000000000000) (30166557784 / 1000000000000)))) (orderedInterval (2399878532 / 1000000000000) (2399878556 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (272109890309631 / 4000000000000) 0 (IntervalRat.scale (633 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-28957589922 / 1000000000000) (-28957589296 / 1000000000000), orderedInterval (92516347041 / 1000000000000) (92516347667 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (730925440793907 / 4000000000000) 0 (IntervalRat.scale (633 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (56931627058 / 1000000000000) (56931627060 / 1000000000000), orderedInterval (15422715977 / 1000000000000) (15422715979 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1984604757002919 / 4000000000000) 0 (IntervalRat.scale (633 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (19169727465 / 1000000000000) (19169727466 / 1000000000000), orderedInterval (30240197726 / 1000000000000) (30240197727 / 1000000000000)))) (orderedInterval (1030073357 / 1000000000000) (1030073402 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1461850881588447 / 4000000000000) 0 (IntervalRat.scale (633 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (40416072304 / 1000000000000) (40416076690 / 1000000000000), orderedInterval (-10471386146 / 1000000000000) (-10471381759 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2504906402051931 / 4000000000000) 0 (IntervalRat.scale (633 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-30778917295 / 1000000000000) (-30778898669 / 1000000000000), orderedInterval (8346526210 / 1000000000000) (8346544835 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1845102718419729 / 4000000000000) 0 (IntervalRat.scale (633 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-9071761921 / 1000000000000) (-9071761920 / 1000000000000), orderedInterval (-36015608807 / 1000000000000) (-36015608806 / 1000000000000)))) (orderedInterval (730097785 / 1000000000000) (730098378 / 1000000000000))) = true
  rfl'

theorem compactCertificate445_chunkChecks0_1 :
    compactCertificate445.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2830862059514367 / 4000000000000) 0 (IntervalRat.scale (633 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-29915531549 / 1000000000000) (-29915527487 / 1000000000000), orderedInterval (2166543970 / 1000000000000) (2166548032 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1634398972099143 / 4000000000000) 0 (IntervalRat.scale (633 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (32732857789 / 1000000000000) (32732857790 / 1000000000000), orderedInterval (22019226417 / 1000000000000) (22019226418 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2900269656951987 / 4000000000000) 0 (IntervalRat.scale (633 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-4273788942 / 1000000000000) (-4273788941 / 1000000000000), orderedInterval (-29318538534 / 1000000000000) (-29318538533 / 1000000000000)))) (orderedInterval (7133319096 / 1000000000000) (7133319943 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2709808126609503 / 4000000000000) 0 (IntervalRat.scale (633 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-10418389517 / 1000000000000) (-10418389502 / 1000000000000), orderedInterval (28837952508 / 1000000000000) (28837952523 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1933846943270799 / 4000000000000) 0 (IntervalRat.scale (633 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (15509076552 / 1000000000000) (15509076553 / 1000000000000), orderedInterval (32790415990 / 1000000000000) (32790415991 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2192776322381721 / 4000000000000) 0 (IntervalRat.scale (633 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (24433244542 / 1000000000000) (24433254862 / 1000000000000), orderedInterval (-23777708859 / 1000000000000) (-23777698538 / 1000000000000)))) (orderedInterval (1531020447 / 1000000000000) (1531020538 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1828108289178249 / 4000000000000) 0 (IntervalRat.scale (633 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-28292524038 / 1000000000000) (-28292495309 / 1000000000000), orderedInterval (24372102949 / 1000000000000) (24372131678 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1615189114451229 / 4000000000000) 0 (IntervalRat.scale (633 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (25062102666 / 1000000000000) (25062109332 / 1000000000000), orderedInterval (-30828336538 / 1000000000000) (-30828329873 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (468144760387671 / 800000000000) 0 (IntervalRat.scale (633 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (32925763313 / 1000000000000) (32925765097 / 1000000000000), orderedInterval (-1976485932 / 1000000000000) (-1976484148 / 1000000000000)))) (orderedInterval (-917904385 / 1000000000000) (-917903595 / 1000000000000))) = true
  rfl'

theorem compactCertificate445_chunkChecks0_2 :
    compactCertificate445.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1294913044341237 / 4000000000000) 0 (IntervalRat.scale (633 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-35527802740 / 1000000000000) (-35527802739 / 1000000000000), orderedInterval (-26483773283 / 1000000000000) (-26483773282 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1097712128457357 / 4000000000000) 0 (IntervalRat.scale (633 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-45664175716 / 1000000000000) (-45664169991 / 1000000000000), orderedInterval (15399401138 / 1000000000000) (15399406862 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (686897281580271 / 4000000000000) 0 (IntervalRat.scale (633 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (16744785590 / 1000000000000) (16744785825 / 1000000000000), orderedInterval (-58588015926 / 1000000000000) (-58588015692 / 1000000000000)))) (orderedInterval (8810348144 / 1000000000000) (8810348556 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (369415642551057 / 4000000000000) 0 (IntervalRat.scale (633 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-74358956862 / 1000000000000) (-74358947709 / 1000000000000), orderedInterval (37334224698 / 1000000000000) (37334233851 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1003035331104171 / 4000000000000) 0 (IntervalRat.scale (633 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (10814741240 / 1000000000000) (10814741241 / 1000000000000), orderedInterval (49190416572 / 1000000000000) (49190416573 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1369558992494667 / 4000000000000) 0 (IntervalRat.scale (633 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-29112958534 / 1000000000000) (-29112958533 / 1000000000000), orderedInterval (-31765947030 / 1000000000000) (-31765947029 / 1000000000000)))) (orderedInterval (3358878353 / 1000000000000) (3358878560 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (579102718419729 / 4000000000000) 0 (IntervalRat.scale (633 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (57419589776 / 1000000000000) (57419589777 / 1000000000000), orderedInterval (32971887838 / 1000000000000) (32971887839 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2354020399554609 / 4000000000000) 0 (IntervalRat.scale (633 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-31934338800 / 1000000000000) (-31934326326 / 1000000000000), orderedInterval (7898306394 / 1000000000000) (7898318868 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1572376532031231 / 4000000000000) 0 (IntervalRat.scale (633 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-37211042653 / 1000000000000) (-37211042652 / 1000000000000), orderedInterval (-15277391057 / 1000000000000) (-15277391056 / 1000000000000)))) (orderedInterval (9927433686 / 1000000000000) (9927434790 / 1000000000000))) = true
  rfl'

theorem compactCertificate445_chunkChecks0 :
    compactCertificate445.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate445.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate445_chunkChecks0_0
    compactCertificate445_chunkChecks0_1 compactCertificate445_chunkChecks0_2

theorem compactCertificate445_chunkChecks1_0 :
    compactCertificate445.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (633 / 2) 1 (IntervalRat.scale (633 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (711042044 / 1000000000000) (711042046 / 1000000000000), orderedInterval (-44844559902 / 1000000000000) (-44844559900 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (932529870021333 / 4000000000000) 1 (IntervalRat.scale (633 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (51806290248 / 1000000000000) (51806290260 / 1000000000000), orderedInterval (6731656126 / 1000000000000) (6731656139 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (301560999929589 / 800000000000) 1 (IntervalRat.scale (633 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (27867765485 / 1000000000000) (27867765486 / 1000000000000), orderedInterval (30166557783 / 1000000000000) (30166557784 / 1000000000000)))) (orderedInterval (-15620293685 / 1000000000000) (-15620293658 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (272109890309631 / 4000000000000) 1 (IntervalRat.scale (633 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-28957589922 / 1000000000000) (-28957589296 / 1000000000000), orderedInterval (92516347041 / 1000000000000) (92516347667 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (730925440793907 / 4000000000000) 1 (IntervalRat.scale (633 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (56931627058 / 1000000000000) (56931627060 / 1000000000000), orderedInterval (15422715977 / 1000000000000) (15422715979 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1984604757002919 / 4000000000000) 1 (IntervalRat.scale (633 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (19169727465 / 1000000000000) (19169727466 / 1000000000000), orderedInterval (30240197726 / 1000000000000) (30240197727 / 1000000000000)))) (orderedInterval (-3260638661 / 1000000000000) (-3260638616 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1461850881588447 / 4000000000000) 1 (IntervalRat.scale (633 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (40416072304 / 1000000000000) (40416076690 / 1000000000000), orderedInterval (-10471386146 / 1000000000000) (-10471381759 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2504906402051931 / 4000000000000) 1 (IntervalRat.scale (633 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-30778917295 / 1000000000000) (-30778898669 / 1000000000000), orderedInterval (8346526210 / 1000000000000) (8346544835 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1845102718419729 / 4000000000000) 1 (IntervalRat.scale (633 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-9071761921 / 1000000000000) (-9071761920 / 1000000000000), orderedInterval (-36015608807 / 1000000000000) (-36015608806 / 1000000000000)))) (orderedInterval (-1777954961 / 1000000000000) (-1777953793 / 1000000000000))) = true
  rfl'

theorem compactCertificate445_chunkChecks1_1 :
    compactCertificate445.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2830862059514367 / 4000000000000) 1 (IntervalRat.scale (633 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-29915531549 / 1000000000000) (-29915527487 / 1000000000000), orderedInterval (2166543970 / 1000000000000) (2166548032 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1634398972099143 / 4000000000000) 1 (IntervalRat.scale (633 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (32732857789 / 1000000000000) (32732857790 / 1000000000000), orderedInterval (22019226417 / 1000000000000) (22019226418 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2900269656951987 / 4000000000000) 1 (IntervalRat.scale (633 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-4273788942 / 1000000000000) (-4273788941 / 1000000000000), orderedInterval (-29318538534 / 1000000000000) (-29318538533 / 1000000000000)))) (orderedInterval (-8302621271 / 1000000000000) (-8302619396 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2709808126609503 / 4000000000000) 1 (IntervalRat.scale (633 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-10418389517 / 1000000000000) (-10418389502 / 1000000000000), orderedInterval (28837952508 / 1000000000000) (28837952523 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1933846943270799 / 4000000000000) 1 (IntervalRat.scale (633 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (15509076552 / 1000000000000) (15509076553 / 1000000000000), orderedInterval (32790415990 / 1000000000000) (32790415991 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2192776322381721 / 4000000000000) 1 (IntervalRat.scale (633 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (24433244542 / 1000000000000) (24433254862 / 1000000000000), orderedInterval (-23777708859 / 1000000000000) (-23777698538 / 1000000000000)))) (orderedInterval (3830550573 / 1000000000000) (3830550726 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1828108289178249 / 4000000000000) 1 (IntervalRat.scale (633 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-28292524038 / 1000000000000) (-28292495309 / 1000000000000), orderedInterval (24372102949 / 1000000000000) (24372131678 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1615189114451229 / 4000000000000) 1 (IntervalRat.scale (633 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (25062102666 / 1000000000000) (25062109332 / 1000000000000), orderedInterval (-30828336538 / 1000000000000) (-30828329873 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (468144760387671 / 800000000000) 1 (IntervalRat.scale (633 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (32925763313 / 1000000000000) (32925765097 / 1000000000000), orderedInterval (-1976485932 / 1000000000000) (-1976484148 / 1000000000000)))) (orderedInterval (2563642631 / 1000000000000) (2563643726 / 1000000000000))) = true
  rfl'

theorem compactCertificate445_chunkChecks1_2 :
    compactCertificate445.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1294913044341237 / 4000000000000) 1 (IntervalRat.scale (633 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-35527802740 / 1000000000000) (-35527802739 / 1000000000000), orderedInterval (-26483773283 / 1000000000000) (-26483773282 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1097712128457357 / 4000000000000) 1 (IntervalRat.scale (633 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-45664175716 / 1000000000000) (-45664169991 / 1000000000000), orderedInterval (15399401138 / 1000000000000) (15399406862 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (686897281580271 / 4000000000000) 1 (IntervalRat.scale (633 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (16744785590 / 1000000000000) (16744785825 / 1000000000000), orderedInterval (-58588015926 / 1000000000000) (-58588015692 / 1000000000000)))) (orderedInterval (2540644417 / 1000000000000) (2540644776 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (369415642551057 / 4000000000000) 1 (IntervalRat.scale (633 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-74358956862 / 1000000000000) (-74358947709 / 1000000000000), orderedInterval (37334224698 / 1000000000000) (37334233851 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1003035331104171 / 4000000000000) 1 (IntervalRat.scale (633 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (10814741240 / 1000000000000) (10814741241 / 1000000000000), orderedInterval (49190416572 / 1000000000000) (49190416573 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1369558992494667 / 4000000000000) 1 (IntervalRat.scale (633 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-29112958534 / 1000000000000) (-29112958533 / 1000000000000), orderedInterval (-31765947030 / 1000000000000) (-31765947029 / 1000000000000)))) (orderedInterval (1548316176 / 1000000000000) (1548316260 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (579102718419729 / 4000000000000) 1 (IntervalRat.scale (633 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (57419589776 / 1000000000000) (57419589777 / 1000000000000), orderedInterval (32971887838 / 1000000000000) (32971887839 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2354020399554609 / 4000000000000) 1 (IntervalRat.scale (633 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-31934338800 / 1000000000000) (-31934326326 / 1000000000000), orderedInterval (7898306394 / 1000000000000) (7898318868 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1572376532031231 / 4000000000000) 1 (IntervalRat.scale (633 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-37211042653 / 1000000000000) (-37211042652 / 1000000000000), orderedInterval (-15277391057 / 1000000000000) (-15277391056 / 1000000000000)))) (orderedInterval (2455566522 / 1000000000000) (2455568534 / 1000000000000))) = true
  rfl'

theorem compactCertificate445_chunkChecks1 :
    compactCertificate445.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate445.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate445_chunkChecks1_0
    compactCertificate445_chunkChecks1_1 compactCertificate445_chunkChecks1_2

theorem compactCertificate445_chunkChecks2_0 :
    compactCertificate445.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (633 / 2) 2 (IntervalRat.scale (633 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (711042044 / 1000000000000) (711042046 / 1000000000000), orderedInterval (-44844559902 / 1000000000000) (-44844559900 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (932529870021333 / 4000000000000) 2 (IntervalRat.scale (633 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (51806290248 / 1000000000000) (51806290260 / 1000000000000), orderedInterval (6731656126 / 1000000000000) (6731656139 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (301560999929589 / 800000000000) 2 (IntervalRat.scale (633 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (27867765485 / 1000000000000) (27867765486 / 1000000000000), orderedInterval (30166557783 / 1000000000000) (30166557784 / 1000000000000)))) (orderedInterval (-2814053695 / 1000000000000) (-2814053665 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (272109890309631 / 4000000000000) 2 (IntervalRat.scale (633 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-28957589922 / 1000000000000) (-28957589296 / 1000000000000), orderedInterval (92516347041 / 1000000000000) (92516347667 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (730925440793907 / 4000000000000) 2 (IntervalRat.scale (633 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (56931627058 / 1000000000000) (56931627060 / 1000000000000), orderedInterval (15422715977 / 1000000000000) (15422715979 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1984604757002919 / 4000000000000) 2 (IntervalRat.scale (633 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (19169727465 / 1000000000000) (19169727466 / 1000000000000), orderedInterval (30240197726 / 1000000000000) (30240197727 / 1000000000000)))) (orderedInterval (2651802770 / 1000000000000) (2651802830 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1461850881588447 / 4000000000000) 2 (IntervalRat.scale (633 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (40416072304 / 1000000000000) (40416076690 / 1000000000000), orderedInterval (-10471386146 / 1000000000000) (-10471381759 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2504906402051931 / 4000000000000) 2 (IntervalRat.scale (633 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-30778917295 / 1000000000000) (-30778898669 / 1000000000000), orderedInterval (8346526210 / 1000000000000) (8346544835 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1845102718419729 / 4000000000000) 2 (IntervalRat.scale (633 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-9071761921 / 1000000000000) (-9071761920 / 1000000000000), orderedInterval (-36015608807 / 1000000000000) (-36015608806 / 1000000000000)))) (orderedInterval (-3245229272 / 1000000000000) (-3245226964 / 1000000000000))) = true
  rfl'

theorem compactCertificate445_chunkChecks2_1 :
    compactCertificate445.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2830862059514367 / 4000000000000) 2 (IntervalRat.scale (633 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-29915531549 / 1000000000000) (-29915527487 / 1000000000000), orderedInterval (2166543970 / 1000000000000) (2166548032 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1634398972099143 / 4000000000000) 2 (IntervalRat.scale (633 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (32732857789 / 1000000000000) (32732857790 / 1000000000000), orderedInterval (22019226417 / 1000000000000) (22019226418 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2900269656951987 / 4000000000000) 2 (IntervalRat.scale (633 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-4273788942 / 1000000000000) (-4273788941 / 1000000000000), orderedInterval (-29318538534 / 1000000000000) (-29318538533 / 1000000000000)))) (orderedInterval (-27405464139 / 1000000000000) (-27405459967 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2709808126609503 / 4000000000000) 2 (IntervalRat.scale (633 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-10418389517 / 1000000000000) (-10418389502 / 1000000000000), orderedInterval (28837952508 / 1000000000000) (28837952523 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1933846943270799 / 4000000000000) 2 (IntervalRat.scale (633 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (15509076552 / 1000000000000) (15509076553 / 1000000000000), orderedInterval (32790415990 / 1000000000000) (32790415991 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2192776322381721 / 4000000000000) 2 (IntervalRat.scale (633 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (24433244542 / 1000000000000) (24433254862 / 1000000000000), orderedInterval (-23777708859 / 1000000000000) (-23777698538 / 1000000000000)))) (orderedInterval (-3924901538 / 1000000000000) (-3924901278 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1828108289178249 / 4000000000000) 2 (IntervalRat.scale (633 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-28292524038 / 1000000000000) (-28292495309 / 1000000000000), orderedInterval (24372102949 / 1000000000000) (24372131678 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1615189114451229 / 4000000000000) 2 (IntervalRat.scale (633 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (25062102666 / 1000000000000) (25062109332 / 1000000000000), orderedInterval (-30828336538 / 1000000000000) (-30828329873 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (468144760387671 / 800000000000) 2 (IntervalRat.scale (633 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (32925763313 / 1000000000000) (32925765097 / 1000000000000), orderedInterval (-1976485932 / 1000000000000) (-1976484148 / 1000000000000)))) (orderedInterval (125771809 / 1000000000000) (125773347 / 1000000000000))) = true
  rfl'

theorem compactCertificate445_chunkChecks2_2 :
    compactCertificate445.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1294913044341237 / 4000000000000) 2 (IntervalRat.scale (633 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-35527802740 / 1000000000000) (-35527802739 / 1000000000000), orderedInterval (-26483773283 / 1000000000000) (-26483773282 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1097712128457357 / 4000000000000) 2 (IntervalRat.scale (633 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-45664175716 / 1000000000000) (-45664169991 / 1000000000000), orderedInterval (15399401138 / 1000000000000) (15399406862 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (686897281580271 / 4000000000000) 2 (IntervalRat.scale (633 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (16744785590 / 1000000000000) (16744785825 / 1000000000000), orderedInterval (-58588015926 / 1000000000000) (-58588015692 / 1000000000000)))) (orderedInterval (-8054692718 / 1000000000000) (-8054692400 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (369415642551057 / 4000000000000) 2 (IntervalRat.scale (633 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-74358956862 / 1000000000000) (-74358947709 / 1000000000000), orderedInterval (37334224698 / 1000000000000) (37334233851 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1003035331104171 / 4000000000000) 2 (IntervalRat.scale (633 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (10814741240 / 1000000000000) (10814741241 / 1000000000000), orderedInterval (49190416572 / 1000000000000) (49190416573 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1369558992494667 / 4000000000000) 2 (IntervalRat.scale (633 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-29112958534 / 1000000000000) (-29112958533 / 1000000000000), orderedInterval (-31765947030 / 1000000000000) (-31765947029 / 1000000000000)))) (orderedInterval (-2578924899 / 1000000000000) (-2578924850 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (579102718419729 / 4000000000000) 2 (IntervalRat.scale (633 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (57419589776 / 1000000000000) (57419589777 / 1000000000000), orderedInterval (32971887838 / 1000000000000) (32971887839 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2354020399554609 / 4000000000000) 2 (IntervalRat.scale (633 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-31934338800 / 1000000000000) (-31934326326 / 1000000000000), orderedInterval (7898306394 / 1000000000000) (7898318868 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1572376532031231 / 4000000000000) 2 (IntervalRat.scale (633 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-37211042653 / 1000000000000) (-37211042652 / 1000000000000), orderedInterval (-15277391057 / 1000000000000) (-15277391056 / 1000000000000)))) (orderedInterval (-19837711204 / 1000000000000) (-19837707505 / 1000000000000))) = true
  rfl'

theorem compactCertificate445_chunkChecks2 :
    compactCertificate445.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate445.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate445_chunkChecks2_0
    compactCertificate445_chunkChecks2_1 compactCertificate445_chunkChecks2_2

theorem compactCertificate445_chunkChecks3_0 :
    compactCertificate445.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (633 / 2) 3 (IntervalRat.scale (633 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (711042044 / 1000000000000) (711042046 / 1000000000000), orderedInterval (-44844559902 / 1000000000000) (-44844559900 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (932529870021333 / 4000000000000) 3 (IntervalRat.scale (633 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (51806290248 / 1000000000000) (51806290260 / 1000000000000), orderedInterval (6731656126 / 1000000000000) (6731656139 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (301560999929589 / 800000000000) 3 (IntervalRat.scale (633 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (27867765485 / 1000000000000) (27867765486 / 1000000000000), orderedInterval (30166557783 / 1000000000000) (30166557784 / 1000000000000)))) (orderedInterval (14767877338 / 1000000000000) (14767877372 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (272109890309631 / 4000000000000) 3 (IntervalRat.scale (633 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-28957589922 / 1000000000000) (-28957589296 / 1000000000000), orderedInterval (92516347041 / 1000000000000) (92516347667 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (730925440793907 / 4000000000000) 3 (IntervalRat.scale (633 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (56931627058 / 1000000000000) (56931627060 / 1000000000000), orderedInterval (15422715977 / 1000000000000) (15422715979 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1984604757002919 / 4000000000000) 3 (IntervalRat.scale (633 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (19169727465 / 1000000000000) (19169727466 / 1000000000000), orderedInterval (30240197726 / 1000000000000) (30240197727 / 1000000000000)))) (orderedInterval (8174740421 / 1000000000000) (8174740511 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1461850881588447 / 4000000000000) 3 (IntervalRat.scale (633 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (40416072304 / 1000000000000) (40416076690 / 1000000000000), orderedInterval (-10471386146 / 1000000000000) (-10471381759 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2504906402051931 / 4000000000000) 3 (IntervalRat.scale (633 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-30778917295 / 1000000000000) (-30778898669 / 1000000000000), orderedInterval (8346526210 / 1000000000000) (8346544835 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1845102718419729 / 4000000000000) 3 (IntervalRat.scale (633 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-9071761921 / 1000000000000) (-9071761920 / 1000000000000), orderedInterval (-36015608807 / 1000000000000) (-36015608806 / 1000000000000)))) (orderedInterval (4698937843 / 1000000000000) (4698942400 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate445_chunkChecks3_1 :
    compactCertificate445.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2830862059514367 / 4000000000000) 3 (IntervalRat.scale (633 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-29915531549 / 1000000000000) (-29915527487 / 1000000000000), orderedInterval (2166543970 / 1000000000000) (2166548032 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1634398972099143 / 4000000000000) 3 (IntervalRat.scale (633 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (32732857789 / 1000000000000) (32732857790 / 1000000000000), orderedInterval (22019226417 / 1000000000000) (22019226418 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2900269656951987 / 4000000000000) 3 (IntervalRat.scale (633 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-4273788942 / 1000000000000) (-4273788941 / 1000000000000), orderedInterval (-29318538534 / 1000000000000) (-29318538533 / 1000000000000)))) (orderedInterval (50989909887 / 1000000000000) (50989919191 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2709808126609503 / 4000000000000) 3 (IntervalRat.scale (633 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-10418389517 / 1000000000000) (-10418389502 / 1000000000000), orderedInterval (28837952508 / 1000000000000) (28837952523 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1933846943270799 / 4000000000000) 3 (IntervalRat.scale (633 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (15509076552 / 1000000000000) (15509076553 / 1000000000000), orderedInterval (32790415990 / 1000000000000) (32790415991 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2192776322381721 / 4000000000000) 3 (IntervalRat.scale (633 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (24433244542 / 1000000000000) (24433254862 / 1000000000000), orderedInterval (-23777708859 / 1000000000000) (-23777698538 / 1000000000000)))) (orderedInterval (-6559193813 / 1000000000000) (-6559193366 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1828108289178249 / 4000000000000) 3 (IntervalRat.scale (633 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-28292524038 / 1000000000000) (-28292495309 / 1000000000000), orderedInterval (24372102949 / 1000000000000) (24372131678 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1615189114451229 / 4000000000000) 3 (IntervalRat.scale (633 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (25062102666 / 1000000000000) (25062109332 / 1000000000000), orderedInterval (-30828336538 / 1000000000000) (-30828329873 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (468144760387671 / 800000000000) 3 (IntervalRat.scale (633 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (32925763313 / 1000000000000) (32925765097 / 1000000000000), orderedInterval (-1976485932 / 1000000000000) (-1976484148 / 1000000000000)))) (orderedInterval (-4191608191 / 1000000000000) (-4191606006 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate445_chunkChecks3_2 :
    compactCertificate445.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1294913044341237 / 4000000000000) 3 (IntervalRat.scale (633 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-35527802740 / 1000000000000) (-35527802739 / 1000000000000), orderedInterval (-26483773283 / 1000000000000) (-26483773282 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1097712128457357 / 4000000000000) 3 (IntervalRat.scale (633 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-45664175716 / 1000000000000) (-45664169991 / 1000000000000), orderedInterval (15399401138 / 1000000000000) (15399406862 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (686897281580271 / 4000000000000) 3 (IntervalRat.scale (633 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (16744785590 / 1000000000000) (16744785825 / 1000000000000), orderedInterval (-58588015926 / 1000000000000) (-58588015692 / 1000000000000)))) (orderedInterval (-3633054722 / 1000000000000) (-3633054440 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (369415642551057 / 4000000000000) 3 (IntervalRat.scale (633 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-74358956862 / 1000000000000) (-74358947709 / 1000000000000), orderedInterval (37334224698 / 1000000000000) (37334233851 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1003035331104171 / 4000000000000) 3 (IntervalRat.scale (633 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (10814741240 / 1000000000000) (10814741241 / 1000000000000), orderedInterval (49190416572 / 1000000000000) (49190416573 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1369558992494667 / 4000000000000) 3 (IntervalRat.scale (633 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-29112958534 / 1000000000000) (-29112958533 / 1000000000000), orderedInterval (-31765947030 / 1000000000000) (-31765947029 / 1000000000000)))) (orderedInterval (-2501833773 / 1000000000000) (-2501833733 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (579102718419729 / 4000000000000) 3 (IntervalRat.scale (633 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (57419589776 / 1000000000000) (57419589777 / 1000000000000), orderedInterval (32971887838 / 1000000000000) (32971887839 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2354020399554609 / 4000000000000) 3 (IntervalRat.scale (633 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-31934338800 / 1000000000000) (-31934326326 / 1000000000000), orderedInterval (7898306394 / 1000000000000) (7898318868 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1572376532031231 / 4000000000000) 3 (IntervalRat.scale (633 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-37211042653 / 1000000000000) (-37211042652 / 1000000000000), orderedInterval (-15277391057 / 1000000000000) (-15277391056 / 1000000000000)))) (orderedInterval (-1314782260 / 1000000000000) (-1314775440 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate445_chunkChecks3 :
    compactCertificate445.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate445.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate445_chunkChecks3_0
    compactCertificate445_chunkChecks3_1 compactCertificate445_chunkChecks3_2

theorem compactCertificate445_chunkChecks4_0 :
    compactCertificate445.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (633 / 2) 4 (IntervalRat.scale (633 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (711042044 / 1000000000000) (711042046 / 1000000000000), orderedInterval (-44844559902 / 1000000000000) (-44844559900 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (932529870021333 / 4000000000000) 4 (IntervalRat.scale (633 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (51806290248 / 1000000000000) (51806290260 / 1000000000000), orderedInterval (6731656126 / 1000000000000) (6731656139 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (301560999929589 / 800000000000) 4 (IntervalRat.scale (633 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (27867765485 / 1000000000000) (27867765486 / 1000000000000), orderedInterval (30166557783 / 1000000000000) (30166557784 / 1000000000000)))) (orderedInterval (3620978472 / 1000000000000) (3620978512 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (272109890309631 / 4000000000000) 4 (IntervalRat.scale (633 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-28957589922 / 1000000000000) (-28957589296 / 1000000000000), orderedInterval (92516347041 / 1000000000000) (92516347667 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (730925440793907 / 4000000000000) 4 (IntervalRat.scale (633 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (56931627058 / 1000000000000) (56931627060 / 1000000000000), orderedInterval (15422715977 / 1000000000000) (15422715979 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1984604757002919 / 4000000000000) 4 (IntervalRat.scale (633 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (19169727465 / 1000000000000) (19169727466 / 1000000000000), orderedInterval (30240197726 / 1000000000000) (30240197727 / 1000000000000)))) (orderedInterval (-8049687808 / 1000000000000) (-8049687670 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1461850881588447 / 4000000000000) 4 (IntervalRat.scale (633 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (40416072304 / 1000000000000) (40416076690 / 1000000000000), orderedInterval (-10471386146 / 1000000000000) (-10471381759 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2504906402051931 / 4000000000000) 4 (IntervalRat.scale (633 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-30778917295 / 1000000000000) (-30778898669 / 1000000000000), orderedInterval (8346526210 / 1000000000000) (8346544835 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1845102718419729 / 4000000000000) 4 (IntervalRat.scale (633 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-9071761921 / 1000000000000) (-9071761920 / 1000000000000), orderedInterval (-36015608807 / 1000000000000) (-36015608806 / 1000000000000)))) (orderedInterval (13530814564 / 1000000000000) (13530823582 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate445_chunkChecks4_1 :
    compactCertificate445.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2830862059514367 / 4000000000000) 4 (IntervalRat.scale (633 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-29915531549 / 1000000000000) (-29915527487 / 1000000000000), orderedInterval (2166543970 / 1000000000000) (2166548032 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1634398972099143 / 4000000000000) 4 (IntervalRat.scale (633 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (32732857789 / 1000000000000) (32732857790 / 1000000000000), orderedInterval (22019226417 / 1000000000000) (22019226418 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2900269656951987 / 4000000000000) 4 (IntervalRat.scale (633 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-4273788942 / 1000000000000) (-4273788941 / 1000000000000), orderedInterval (-29318538534 / 1000000000000) (-29318538533 / 1000000000000)))) (orderedInterval (122571100838 / 1000000000000) (122571121649 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2709808126609503 / 4000000000000) 4 (IntervalRat.scale (633 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-10418389517 / 1000000000000) (-10418389502 / 1000000000000), orderedInterval (28837952508 / 1000000000000) (28837952523 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1933846943270799 / 4000000000000) 4 (IntervalRat.scale (633 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (15509076552 / 1000000000000) (15509076553 / 1000000000000), orderedInterval (32790415990 / 1000000000000) (32790415991 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2192776322381721 / 4000000000000) 4 (IntervalRat.scale (633 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (24433244542 / 1000000000000) (24433254862 / 1000000000000), orderedInterval (-23777708859 / 1000000000000) (-23777698538 / 1000000000000)))) (orderedInterval (10861267562 / 1000000000000) (10861268339 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1828108289178249 / 4000000000000) 4 (IntervalRat.scale (633 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-28292524038 / 1000000000000) (-28292495309 / 1000000000000), orderedInterval (24372102949 / 1000000000000) (24372131678 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1615189114451229 / 4000000000000) 4 (IntervalRat.scale (633 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (25062102666 / 1000000000000) (25062109332 / 1000000000000), orderedInterval (-30828336538 / 1000000000000) (-30828329873 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (468144760387671 / 800000000000) 4 (IntervalRat.scale (633 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (32925763313 / 1000000000000) (32925765097 / 1000000000000), orderedInterval (-1976485932 / 1000000000000) (-1976484148 / 1000000000000)))) (orderedInterval (4657716001 / 1000000000000) (4657719161 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate445_chunkChecks4_2 :
    compactCertificate445.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1294913044341237 / 4000000000000) 4 (IntervalRat.scale (633 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-35527802740 / 1000000000000) (-35527802739 / 1000000000000), orderedInterval (-26483773283 / 1000000000000) (-26483773282 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1097712128457357 / 4000000000000) 4 (IntervalRat.scale (633 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-45664175716 / 1000000000000) (-45664169991 / 1000000000000), orderedInterval (15399401138 / 1000000000000) (15399406862 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (686897281580271 / 4000000000000) 4 (IntervalRat.scale (633 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (16744785590 / 1000000000000) (16744785825 / 1000000000000), orderedInterval (-58588015926 / 1000000000000) (-58588015692 / 1000000000000)))) (orderedInterval (7748602579 / 1000000000000) (7748602831 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (369415642551057 / 4000000000000) 4 (IntervalRat.scale (633 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-74358956862 / 1000000000000) (-74358947709 / 1000000000000), orderedInterval (37334224698 / 1000000000000) (37334233851 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1003035331104171 / 4000000000000) 4 (IntervalRat.scale (633 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (10814741240 / 1000000000000) (10814741241 / 1000000000000), orderedInterval (49190416572 / 1000000000000) (49190416573 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1369558992494667 / 4000000000000) 4 (IntervalRat.scale (633 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-29112958534 / 1000000000000) (-29112958533 / 1000000000000), orderedInterval (-31765947030 / 1000000000000) (-31765947029 / 1000000000000)))) (orderedInterval (2984852016 / 1000000000000) (2984852054 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (579102718419729 / 4000000000000) 4 (IntervalRat.scale (633 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (57419589776 / 1000000000000) (57419589777 / 1000000000000), orderedInterval (32971887838 / 1000000000000) (32971887839 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2354020399554609 / 4000000000000) 4 (IntervalRat.scale (633 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-31934338800 / 1000000000000) (-31934326326 / 1000000000000), orderedInterval (7898306394 / 1000000000000) (7898318868 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1572376532031231 / 4000000000000) 4 (IntervalRat.scale (633 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-37211042653 / 1000000000000) (-37211042652 / 1000000000000), orderedInterval (-15277391057 / 1000000000000) (-15277391056 / 1000000000000)))) (orderedInterval (47710663476 / 1000000000000) (47710676106 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate445_chunkChecks4 :
    compactCertificate445.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate445.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate445_chunkChecks4_0
    compactCertificate445_chunkChecks4_1 compactCertificate445_chunkChecks4_2

theorem compactCertificate445_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate445.chunkCheck r b = true :=
  compactCertificate445.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate445_chunkChecks0
    · exact compactCertificate445_chunkChecks1
    · exact compactCertificate445_chunkChecks2
    · exact compactCertificate445_chunkChecks3
    · exact compactCertificate445_chunkChecks4)

theorem compactCertificate445_coefficient0 :
    compactCertificate445.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate445_coefficient1 :
    compactCertificate445.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate445_coefficient2 :
    compactCertificate445.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate445_coefficient3 :
    compactCertificate445.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate445_coefficient4 :
    compactCertificate445.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate445_coefficients : ∀ r : Fin 5,
    compactCertificate445.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate445_coefficient0
  · exact compactCertificate445_coefficient1
  · exact compactCertificate445_coefficient2
  · exact compactCertificate445_coefficient3
  · exact compactCertificate445_coefficient4

theorem compactCertificate445_lower : (1 : ℚ) ≤ compactCertificate445.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate445, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate445_proves {t : ℝ} (ht : t ∈ compactCertificate445.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate445.proves compactCertificate445_states compactCertificate445_chunks
    compactCertificate445_coefficients compactCertificate445_lower ht

end Erdos232
