/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate305 : CompactCertificate where
  left := 178
  right := 179
  center := 357 / 2
  grid := fun i =>
    match i.val with
    | 0 => 57
    | 1 => 42
    | 2 => 68
    | 3 => 12
    | 4 => 33
    | 5 => 89
    | 6 => 66
    | 7 => 112
    | 8 => 83
    | 9 => 127
    | 10 => 73
    | 11 => 130
    | 12 => 122
    | 13 => 87
    | 14 => 98
    | 15 => 82
    | 16 => 73
    | 17 => 105
    | 18 => 58
    | 19 => 49
    | 20 => 31
    | 21 => 17
    | 22 => 45
    | 23 => 61
    | 24 => 26
    | 25 => 106
    | _ => 71
  point := fun i =>
    match i.val with
    | 0 => 357 / 2
    | 1 => 525929168400657 / 4000000000000
    | 2 => 170074687164081 / 800000000000
    | 3 => 153464819653299 / 4000000000000
    | 4 => 412228092201303 / 4000000000000
    | 5 => 1119279460110651 / 4000000000000
    | 6 => 824456184402963 / 4000000000000
    | 7 => 1412719724379999 / 4000000000000
    | 8 => 1040602954938141 / 4000000000000
    | 9 => 1596552535934643 / 4000000000000
    | 10 => 921770036397147 / 4000000000000
    | 11 => 1635697105105623 / 4000000000000
    | 12 => 1528280412637587 / 4000000000000
    | 13 => 1090653015399171 / 4000000000000
    | 14 => 1236684276603909 / 4000000000000
    | 15 => 1031018419015221 / 4000000000000
    | 16 => 910936040851641 / 4000000000000
    | 17 => 264024770076459 / 800000000000
    | 18 => 730306408893873 / 4000000000000
    | 19 => 619088830741353 / 4000000000000
    | 20 => 387397045061859 / 4000000000000
    | 21 => 208343419258653 / 4000000000000
    | 22 => 565692911854959 / 4000000000000
    | 23 => 772405308563343 / 4000000000000
    | 24 => 326602954938141 / 4000000000000
    | 25 => 1327622879369661 / 4000000000000
    | _ => 886790555979699 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-12677901057 / 1000000000000) (-12677901056 / 1000000000000), orderedInterval (-58323556476 / 1000000000000) (-58323556475 / 1000000000000))
    | 1 => (orderedInterval (21878540597 / 1000000000000) (21878540598 / 1000000000000), orderedInterval (65971510435 / 1000000000000) (65971510436 / 1000000000000))
    | 2 => (orderedInterval (-13545483534 / 1000000000000) (-13545483414 / 1000000000000), orderedInterval (53051375461 / 1000000000000) (53051375581 / 1000000000000))
    | 3 => (orderedInterval (127858743137 / 1000000000000) (127858743140 / 1000000000000), orderedInterval (13955095899 / 1000000000000) (13955095902 / 1000000000000))
    | 4 => (orderedInterval (-13192476806 / 1000000000000) (-13192476804 / 1000000000000), orderedInterval (-77417488571 / 1000000000000) (-77417488570 / 1000000000000))
    | 5 => (orderedInterval (-40215445085 / 1000000000000) (-40215445084 / 1000000000000), orderedInterval (-25576184563 / 1000000000000) (-25576184562 / 1000000000000))
    | 6 => (orderedInterval (-23987091900 / 1000000000000) (-23987090397 / 1000000000000), orderedInterval (50191035714 / 1000000000000) (50191037216 / 1000000000000))
    | 7 => (orderedInterval (36506397319 / 1000000000000) (36506459791 / 1000000000000), orderedInterval (-21726961164 / 1000000000000) (-21726898692 / 1000000000000))
    | 8 => (orderedInterval (-9024933024 / 1000000000000) (-9024933023 / 1000000000000), orderedInterval (-48620845611 / 1000000000000) (-48620845610 / 1000000000000))
    | 9 => (orderedInterval (-32274067388 / 1000000000000) (-32274067387 / 1000000000000), orderedInterval (-23483394096 / 1000000000000) (-23483394095 / 1000000000000))
    | 10 => (orderedInterval (-49887106689 / 1000000000000) (-49887102313 / 1000000000000), orderedInterval (16657212917 / 1000000000000) (16657217294 / 1000000000000))
    | 11 => (orderedInterval (38043048213 / 1000000000000) (38043048219 / 1000000000000), orderedInterval (10419680968 / 1000000000000) (10419680974 / 1000000000000))
    | 12 => (orderedInterval (-16612155019 / 1000000000000) (-16612154653 / 1000000000000), orderedInterval (37308136305 / 1000000000000) (37308136671 / 1000000000000))
    | 13 => (orderedInterval (-6246316097 / 1000000000000) (-6246316096 / 1000000000000), orderedInterval (-47903135349 / 1000000000000) (-47903135348 / 1000000000000))
    | 14 => (orderedInterval (39620928452 / 1000000000000) (39620969068 / 1000000000000), orderedInterval (-22184157619 / 1000000000000) (-22184117002 / 1000000000000))
    | 15 => (orderedInterval (39806580669 / 1000000000000) (39806580670 / 1000000000000), orderedInterval (29676815952 / 1000000000000) (29676815953 / 1000000000000))
    | 16 => (orderedInterval (38563339240 / 1000000000000) (38563394570 / 1000000000000), orderedInterval (-36255392512 / 1000000000000) (-36255337182 / 1000000000000))
    | 17 => (orderedInterval (-35693344532 / 1000000000000) (-35693344531 / 1000000000000), orderedInterval (-25537998995 / 1000000000000) (-25537998994 / 1000000000000))
    | 18 => (orderedInterval (53872757748 / 1000000000000) (53872757749 / 1000000000000), orderedInterval (24030581160 / 1000000000000) (24030581161 / 1000000000000))
    | 19 => (orderedInterval (-64060855714 / 1000000000000) (-64060855616 / 1000000000000), orderedInterval (3281802739 / 1000000000000) (3281802838 / 1000000000000))
    | 20 => (orderedInterval (-19586413434 / 1000000000000) (-19586413433 / 1000000000000), orderedInterval (-78573881794 / 1000000000000) (-78573881793 / 1000000000000))
    | 21 => (orderedInterval (56670497499 / 1000000000000) (56670506674 / 1000000000000), orderedInterval (-95471458627 / 1000000000000) (-95471449453 / 1000000000000))
    | 22 => (orderedInterval (-49784219256 / 1000000000000) (-49784219255 / 1000000000000), orderedInterval (-44802326293 / 1000000000000) (-44802326292 / 1000000000000))
    | 23 => (orderedInterval (-44714025327 / 1000000000000) (-44713920089 / 1000000000000), orderedInterval (36136207186 / 1000000000000) (36136312425 / 1000000000000))
    | 24 => (orderedInterval (60394290482 / 1000000000000) (60394290483 / 1000000000000), orderedInterval (64046047637 / 1000000000000) (64046047638 / 1000000000000))
    | 25 => (orderedInterval (-13696844361 / 1000000000000) (-13696844228 / 1000000000000), orderedInterval (41619579777 / 1000000000000) (41619579911 / 1000000000000))
    | _ => (orderedInterval (28944520994 / 1000000000000) (28944526390 / 1000000000000), orderedInterval (-45162789827 / 1000000000000) (-45162784431 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-5616075032 / 1000000000000) (-5616075011 / 1000000000000)
      | 1 => orderedInterval (990044469 / 1000000000000) (990044491 / 1000000000000)
      | 2 => orderedInterval (-1344120113 / 1000000000000) (-1344118175 / 1000000000000)
      | 3 => orderedInterval (7446531430 / 1000000000000) (7446531827 / 1000000000000)
      | 4 => orderedInterval (-491273832 / 1000000000000) (-491273597 / 1000000000000)
      | 5 => orderedInterval (-2661072285 / 1000000000000) (-2661069101 / 1000000000000)
      | 6 => orderedInterval (-5625646205 / 1000000000000) (-5625646153 / 1000000000000)
      | 7 => orderedInterval (3509844474 / 1000000000000) (3509852730 / 1000000000000)
      | _ => orderedInterval (-3951736935 / 1000000000000) (-3951735862 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-18956893577 / 1000000000000) (-18956893554 / 1000000000000)
      | 1 => orderedInterval (1185738513 / 1000000000000) (1185738538 / 1000000000000)
      | 2 => orderedInterval (-386631505 / 1000000000000) (-386627674 / 1000000000000)
      | 3 => orderedInterval (14317085760 / 1000000000000) (14317086328 / 1000000000000)
      | 4 => orderedInterval (-8166674423 / 1000000000000) (-8166674018 / 1000000000000)
      | 5 => orderedInterval (1932939553 / 1000000000000) (1932943618 / 1000000000000)
      | 6 => orderedInterval (-5479015972 / 1000000000000) (-5479015924 / 1000000000000)
      | 7 => orderedInterval (-1676280271 / 1000000000000) (-1676271477 / 1000000000000)
      | _ => orderedInterval (4401489983 / 1000000000000) (4401491331 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (6148163881 / 1000000000000) (6148163908 / 1000000000000)
      | 1 => orderedInterval (-6807540361 / 1000000000000) (-6807540327 / 1000000000000)
      | 2 => orderedInterval (4873601290 / 1000000000000) (4873608887 / 1000000000000)
      | 3 => orderedInterval (-50975821797 / 1000000000000) (-50975820934 / 1000000000000)
      | 4 => orderedInterval (651493609 / 1000000000000) (651494316 / 1000000000000)
      | 5 => orderedInterval (5746935197 / 1000000000000) (5746940411 / 1000000000000)
      | 6 => orderedInterval (6504241557 / 1000000000000) (6504241602 / 1000000000000)
      | 7 => orderedInterval (-4620878713 / 1000000000000) (-4620869191 / 1000000000000)
      | _ => orderedInterval (4421655984 / 1000000000000) (4421657693 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (17577377811 / 1000000000000) (17577377843 / 1000000000000)
      | 1 => orderedInterval (-6420606044 / 1000000000000) (-6420605992 / 1000000000000)
      | 2 => orderedInterval (-1580542537 / 1000000000000) (-1580527513 / 1000000000000)
      | 3 => orderedInterval (-66830590781 / 1000000000000) (-66830589379 / 1000000000000)
      | 4 => orderedInterval (22163134163 / 1000000000000) (22163135397 / 1000000000000)
      | 5 => orderedInterval (-1239834990 / 1000000000000) (-1239828329 / 1000000000000)
      | 6 => orderedInterval (4604671709 / 1000000000000) (4604671752 / 1000000000000)
      | 7 => orderedInterval (2982701769 / 1000000000000) (2982712057 / 1000000000000)
      | _ => orderedInterval (5483903477 / 1000000000000) (5483905654 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-6761143444 / 1000000000000) (-6761143407 / 1000000000000)
      | 1 => orderedInterval (17280002848 / 1000000000000) (17280002927 / 1000000000000)
      | 2 => orderedInterval (-18223473919 / 1000000000000) (-18223444116 / 1000000000000)
      | 3 => orderedInterval (282804008666 / 1000000000000) (282804011133 / 1000000000000)
      | 4 => orderedInterval (1026298292 / 1000000000000) (1026300462 / 1000000000000)
      | 5 => orderedInterval (-14514062733 / 1000000000000) (-14514054180 / 1000000000000)
      | 6 => orderedInterval (-7485354509 / 1000000000000) (-7485354468 / 1000000000000)
      | 7 => orderedInterval (5097204347 / 1000000000000) (5097215529 / 1000000000000)
      | _ => orderedInterval (359829903 / 1000000000000) (359832718 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-7743504029 / 1000000000000) (-7743488851 / 1000000000000)
    | 1 => orderedInterval (-12828241939 / 1000000000000) (-12828222832 / 1000000000000)
    | 2 => orderedInterval (-34058149353 / 1000000000000) (-34058123635 / 1000000000000)
    | 3 => orderedInterval (-23259785423 / 1000000000000) (-23259748510 / 1000000000000)
    | _ => orderedInterval (259583309451 / 1000000000000) (259583366598 / 1000000000000)

theorem compactCertificate305_stateChecks0 :
    compactCertificate305.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 57 12 (357 / 2)) (orderedInterval (-12677901057 / 1000000000000) (-12677901056 / 1000000000000), orderedInterval (-58323556476 / 1000000000000) (-58323556475 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 42 12 (525929168400657 / 4000000000000)) (orderedInterval (21878540597 / 1000000000000) (21878540598 / 1000000000000), orderedInterval (65971510435 / 1000000000000) (65971510436 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (170074687164081 / 800000000000)) (orderedInterval (-13545483534 / 1000000000000) (-13545483414 / 1000000000000), orderedInterval (53051375461 / 1000000000000) (53051375581 / 1000000000000))) = true
  rfl'

theorem compactCertificate305_stateChecks1 :
    compactCertificate305.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 12 12 (153464819653299 / 4000000000000)) (orderedInterval (127858743137 / 1000000000000) (127858743140 / 1000000000000), orderedInterval (13955095899 / 1000000000000) (13955095902 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 33 12 (412228092201303 / 4000000000000)) (orderedInterval (-13192476806 / 1000000000000) (-13192476804 / 1000000000000), orderedInterval (-77417488571 / 1000000000000) (-77417488570 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 89 12 (1119279460110651 / 4000000000000)) (orderedInterval (-40215445085 / 1000000000000) (-40215445084 / 1000000000000), orderedInterval (-25576184563 / 1000000000000) (-25576184562 / 1000000000000))) = true
  rfl'

theorem compactCertificate305_stateChecks2 :
    compactCertificate305.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (824456184402963 / 4000000000000)) (orderedInterval (-23987091900 / 1000000000000) (-23987090397 / 1000000000000), orderedInterval (50191035714 / 1000000000000) (50191037216 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 112 12 (1412719724379999 / 4000000000000)) (orderedInterval (36506397319 / 1000000000000) (36506459791 / 1000000000000), orderedInterval (-21726961164 / 1000000000000) (-21726898692 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 83 12 (1040602954938141 / 4000000000000)) (orderedInterval (-9024933024 / 1000000000000) (-9024933023 / 1000000000000), orderedInterval (-48620845611 / 1000000000000) (-48620845610 / 1000000000000))) = true
  rfl'

theorem compactCertificate305_stateChecks3 :
    compactCertificate305.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 127 12 (1596552535934643 / 4000000000000)) (orderedInterval (-32274067388 / 1000000000000) (-32274067387 / 1000000000000), orderedInterval (-23483394096 / 1000000000000) (-23483394095 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 73 12 (921770036397147 / 4000000000000)) (orderedInterval (-49887106689 / 1000000000000) (-49887102313 / 1000000000000), orderedInterval (16657212917 / 1000000000000) (16657217294 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 130 12 (1635697105105623 / 4000000000000)) (orderedInterval (38043048213 / 1000000000000) (38043048219 / 1000000000000), orderedInterval (10419680968 / 1000000000000) (10419680974 / 1000000000000))) = true
  rfl'

theorem compactCertificate305_stateChecks4 :
    compactCertificate305.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 122 12 (1528280412637587 / 4000000000000)) (orderedInterval (-16612155019 / 1000000000000) (-16612154653 / 1000000000000), orderedInterval (37308136305 / 1000000000000) (37308136671 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 87 12 (1090653015399171 / 4000000000000)) (orderedInterval (-6246316097 / 1000000000000) (-6246316096 / 1000000000000), orderedInterval (-47903135349 / 1000000000000) (-47903135348 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 98 12 (1236684276603909 / 4000000000000)) (orderedInterval (39620928452 / 1000000000000) (39620969068 / 1000000000000), orderedInterval (-22184157619 / 1000000000000) (-22184117002 / 1000000000000))) = true
  rfl'

theorem compactCertificate305_stateChecks5 :
    compactCertificate305.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 82 12 (1031018419015221 / 4000000000000)) (orderedInterval (39806580669 / 1000000000000) (39806580670 / 1000000000000), orderedInterval (29676815952 / 1000000000000) (29676815953 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 73 12 (910936040851641 / 4000000000000)) (orderedInterval (38563339240 / 1000000000000) (38563394570 / 1000000000000), orderedInterval (-36255392512 / 1000000000000) (-36255337182 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 105 12 (264024770076459 / 800000000000)) (orderedInterval (-35693344532 / 1000000000000) (-35693344531 / 1000000000000), orderedInterval (-25537998995 / 1000000000000) (-25537998994 / 1000000000000))) = true
  rfl'

theorem compactCertificate305_stateChecks6 :
    compactCertificate305.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (730306408893873 / 4000000000000)) (orderedInterval (53872757748 / 1000000000000) (53872757749 / 1000000000000), orderedInterval (24030581160 / 1000000000000) (24030581161 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 49 12 (619088830741353 / 4000000000000)) (orderedInterval (-64060855714 / 1000000000000) (-64060855616 / 1000000000000), orderedInterval (3281802739 / 1000000000000) (3281802838 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 31 12 (387397045061859 / 4000000000000)) (orderedInterval (-19586413434 / 1000000000000) (-19586413433 / 1000000000000), orderedInterval (-78573881794 / 1000000000000) (-78573881793 / 1000000000000))) = true
  rfl'

theorem compactCertificate305_stateChecks7 :
    compactCertificate305.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 17 12 (208343419258653 / 4000000000000)) (orderedInterval (56670497499 / 1000000000000) (56670506674 / 1000000000000), orderedInterval (-95471458627 / 1000000000000) (-95471449453 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (565692911854959 / 4000000000000)) (orderedInterval (-49784219256 / 1000000000000) (-49784219255 / 1000000000000), orderedInterval (-44802326293 / 1000000000000) (-44802326292 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 61 12 (772405308563343 / 4000000000000)) (orderedInterval (-44714025327 / 1000000000000) (-44713920089 / 1000000000000), orderedInterval (36136207186 / 1000000000000) (36136312425 / 1000000000000))) = true
  rfl'

theorem compactCertificate305_stateChecks8 :
    compactCertificate305.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 26 12 (326602954938141 / 4000000000000)) (orderedInterval (60394290482 / 1000000000000) (60394290483 / 1000000000000), orderedInterval (64046047637 / 1000000000000) (64046047638 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 106 12 (1327622879369661 / 4000000000000)) (orderedInterval (-13696844361 / 1000000000000) (-13696844228 / 1000000000000), orderedInterval (41619579777 / 1000000000000) (41619579911 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (886790555979699 / 4000000000000)) (orderedInterval (28944520994 / 1000000000000) (28944526390 / 1000000000000), orderedInterval (-45162789827 / 1000000000000) (-45162784431 / 1000000000000))) = true
  rfl'

theorem compactCertificate305_states : ∀ j,
    BesselStateValid (compactCertificate305.point j) (compactCertificate305.state j) :=
  compactCertificate305.statesValid_of_checks3 compactCertificate305_stateChecks0
    compactCertificate305_stateChecks1 compactCertificate305_stateChecks2
    compactCertificate305_stateChecks3 compactCertificate305_stateChecks4
    compactCertificate305_stateChecks5 compactCertificate305_stateChecks6
    compactCertificate305_stateChecks7 compactCertificate305_stateChecks8

theorem compactCertificate305_chunkChecks0_0 :
    compactCertificate305.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (357 / 2) 0 (IntervalRat.scale (357 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-12677901057 / 1000000000000) (-12677901056 / 1000000000000), orderedInterval (-58323556476 / 1000000000000) (-58323556475 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (525929168400657 / 4000000000000) 0 (IntervalRat.scale (357 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (21878540597 / 1000000000000) (21878540598 / 1000000000000), orderedInterval (65971510435 / 1000000000000) (65971510436 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (170074687164081 / 800000000000) 0 (IntervalRat.scale (357 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-13545483534 / 1000000000000) (-13545483414 / 1000000000000), orderedInterval (53051375461 / 1000000000000) (53051375581 / 1000000000000)))) (orderedInterval (-5616075032 / 1000000000000) (-5616075011 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (153464819653299 / 4000000000000) 0 (IntervalRat.scale (357 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (127858743137 / 1000000000000) (127858743140 / 1000000000000), orderedInterval (13955095899 / 1000000000000) (13955095902 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (412228092201303 / 4000000000000) 0 (IntervalRat.scale (357 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-13192476806 / 1000000000000) (-13192476804 / 1000000000000), orderedInterval (-77417488571 / 1000000000000) (-77417488570 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1119279460110651 / 4000000000000) 0 (IntervalRat.scale (357 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-40215445085 / 1000000000000) (-40215445084 / 1000000000000), orderedInterval (-25576184563 / 1000000000000) (-25576184562 / 1000000000000)))) (orderedInterval (990044469 / 1000000000000) (990044491 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (824456184402963 / 4000000000000) 0 (IntervalRat.scale (357 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-23987091900 / 1000000000000) (-23987090397 / 1000000000000), orderedInterval (50191035714 / 1000000000000) (50191037216 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1412719724379999 / 4000000000000) 0 (IntervalRat.scale (357 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (36506397319 / 1000000000000) (36506459791 / 1000000000000), orderedInterval (-21726961164 / 1000000000000) (-21726898692 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1040602954938141 / 4000000000000) 0 (IntervalRat.scale (357 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-9024933024 / 1000000000000) (-9024933023 / 1000000000000), orderedInterval (-48620845611 / 1000000000000) (-48620845610 / 1000000000000)))) (orderedInterval (-1344120113 / 1000000000000) (-1344118175 / 1000000000000))) = true
  rfl'

theorem compactCertificate305_chunkChecks0_1 :
    compactCertificate305.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1596552535934643 / 4000000000000) 0 (IntervalRat.scale (357 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-32274067388 / 1000000000000) (-32274067387 / 1000000000000), orderedInterval (-23483394096 / 1000000000000) (-23483394095 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (921770036397147 / 4000000000000) 0 (IntervalRat.scale (357 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-49887106689 / 1000000000000) (-49887102313 / 1000000000000), orderedInterval (16657212917 / 1000000000000) (16657217294 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1635697105105623 / 4000000000000) 0 (IntervalRat.scale (357 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (38043048213 / 1000000000000) (38043048219 / 1000000000000), orderedInterval (10419680968 / 1000000000000) (10419680974 / 1000000000000)))) (orderedInterval (7446531430 / 1000000000000) (7446531827 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1528280412637587 / 4000000000000) 0 (IntervalRat.scale (357 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-16612155019 / 1000000000000) (-16612154653 / 1000000000000), orderedInterval (37308136305 / 1000000000000) (37308136671 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1090653015399171 / 4000000000000) 0 (IntervalRat.scale (357 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-6246316097 / 1000000000000) (-6246316096 / 1000000000000), orderedInterval (-47903135349 / 1000000000000) (-47903135348 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1236684276603909 / 4000000000000) 0 (IntervalRat.scale (357 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (39620928452 / 1000000000000) (39620969068 / 1000000000000), orderedInterval (-22184157619 / 1000000000000) (-22184117002 / 1000000000000)))) (orderedInterval (-491273832 / 1000000000000) (-491273597 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1031018419015221 / 4000000000000) 0 (IntervalRat.scale (357 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (39806580669 / 1000000000000) (39806580670 / 1000000000000), orderedInterval (29676815952 / 1000000000000) (29676815953 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (910936040851641 / 4000000000000) 0 (IntervalRat.scale (357 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (38563339240 / 1000000000000) (38563394570 / 1000000000000), orderedInterval (-36255392512 / 1000000000000) (-36255337182 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (264024770076459 / 800000000000) 0 (IntervalRat.scale (357 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-35693344532 / 1000000000000) (-35693344531 / 1000000000000), orderedInterval (-25537998995 / 1000000000000) (-25537998994 / 1000000000000)))) (orderedInterval (-2661072285 / 1000000000000) (-2661069101 / 1000000000000))) = true
  rfl'

theorem compactCertificate305_chunkChecks0_2 :
    compactCertificate305.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (730306408893873 / 4000000000000) 0 (IntervalRat.scale (357 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (53872757748 / 1000000000000) (53872757749 / 1000000000000), orderedInterval (24030581160 / 1000000000000) (24030581161 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (619088830741353 / 4000000000000) 0 (IntervalRat.scale (357 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-64060855714 / 1000000000000) (-64060855616 / 1000000000000), orderedInterval (3281802739 / 1000000000000) (3281802838 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (387397045061859 / 4000000000000) 0 (IntervalRat.scale (357 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-19586413434 / 1000000000000) (-19586413433 / 1000000000000), orderedInterval (-78573881794 / 1000000000000) (-78573881793 / 1000000000000)))) (orderedInterval (-5625646205 / 1000000000000) (-5625646153 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (208343419258653 / 4000000000000) 0 (IntervalRat.scale (357 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (56670497499 / 1000000000000) (56670506674 / 1000000000000), orderedInterval (-95471458627 / 1000000000000) (-95471449453 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (565692911854959 / 4000000000000) 0 (IntervalRat.scale (357 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-49784219256 / 1000000000000) (-49784219255 / 1000000000000), orderedInterval (-44802326293 / 1000000000000) (-44802326292 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (772405308563343 / 4000000000000) 0 (IntervalRat.scale (357 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-44714025327 / 1000000000000) (-44713920089 / 1000000000000), orderedInterval (36136207186 / 1000000000000) (36136312425 / 1000000000000)))) (orderedInterval (3509844474 / 1000000000000) (3509852730 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (326602954938141 / 4000000000000) 0 (IntervalRat.scale (357 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (60394290482 / 1000000000000) (60394290483 / 1000000000000), orderedInterval (64046047637 / 1000000000000) (64046047638 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1327622879369661 / 4000000000000) 0 (IntervalRat.scale (357 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-13696844361 / 1000000000000) (-13696844228 / 1000000000000), orderedInterval (41619579777 / 1000000000000) (41619579911 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (886790555979699 / 4000000000000) 0 (IntervalRat.scale (357 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (28944520994 / 1000000000000) (28944526390 / 1000000000000), orderedInterval (-45162789827 / 1000000000000) (-45162784431 / 1000000000000)))) (orderedInterval (-3951736935 / 1000000000000) (-3951735862 / 1000000000000))) = true
  rfl'

theorem compactCertificate305_chunkChecks0 :
    compactCertificate305.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate305.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate305_chunkChecks0_0
    compactCertificate305_chunkChecks0_1 compactCertificate305_chunkChecks0_2

theorem compactCertificate305_chunkChecks1_0 :
    compactCertificate305.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (357 / 2) 1 (IntervalRat.scale (357 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-12677901057 / 1000000000000) (-12677901056 / 1000000000000), orderedInterval (-58323556476 / 1000000000000) (-58323556475 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (525929168400657 / 4000000000000) 1 (IntervalRat.scale (357 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (21878540597 / 1000000000000) (21878540598 / 1000000000000), orderedInterval (65971510435 / 1000000000000) (65971510436 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (170074687164081 / 800000000000) 1 (IntervalRat.scale (357 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-13545483534 / 1000000000000) (-13545483414 / 1000000000000), orderedInterval (53051375461 / 1000000000000) (53051375581 / 1000000000000)))) (orderedInterval (-18956893577 / 1000000000000) (-18956893554 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (153464819653299 / 4000000000000) 1 (IntervalRat.scale (357 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (127858743137 / 1000000000000) (127858743140 / 1000000000000), orderedInterval (13955095899 / 1000000000000) (13955095902 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (412228092201303 / 4000000000000) 1 (IntervalRat.scale (357 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-13192476806 / 1000000000000) (-13192476804 / 1000000000000), orderedInterval (-77417488571 / 1000000000000) (-77417488570 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1119279460110651 / 4000000000000) 1 (IntervalRat.scale (357 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-40215445085 / 1000000000000) (-40215445084 / 1000000000000), orderedInterval (-25576184563 / 1000000000000) (-25576184562 / 1000000000000)))) (orderedInterval (1185738513 / 1000000000000) (1185738538 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (824456184402963 / 4000000000000) 1 (IntervalRat.scale (357 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-23987091900 / 1000000000000) (-23987090397 / 1000000000000), orderedInterval (50191035714 / 1000000000000) (50191037216 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1412719724379999 / 4000000000000) 1 (IntervalRat.scale (357 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (36506397319 / 1000000000000) (36506459791 / 1000000000000), orderedInterval (-21726961164 / 1000000000000) (-21726898692 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1040602954938141 / 4000000000000) 1 (IntervalRat.scale (357 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-9024933024 / 1000000000000) (-9024933023 / 1000000000000), orderedInterval (-48620845611 / 1000000000000) (-48620845610 / 1000000000000)))) (orderedInterval (-386631505 / 1000000000000) (-386627674 / 1000000000000))) = true
  rfl'

theorem compactCertificate305_chunkChecks1_1 :
    compactCertificate305.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1596552535934643 / 4000000000000) 1 (IntervalRat.scale (357 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-32274067388 / 1000000000000) (-32274067387 / 1000000000000), orderedInterval (-23483394096 / 1000000000000) (-23483394095 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (921770036397147 / 4000000000000) 1 (IntervalRat.scale (357 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-49887106689 / 1000000000000) (-49887102313 / 1000000000000), orderedInterval (16657212917 / 1000000000000) (16657217294 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1635697105105623 / 4000000000000) 1 (IntervalRat.scale (357 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (38043048213 / 1000000000000) (38043048219 / 1000000000000), orderedInterval (10419680968 / 1000000000000) (10419680974 / 1000000000000)))) (orderedInterval (14317085760 / 1000000000000) (14317086328 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1528280412637587 / 4000000000000) 1 (IntervalRat.scale (357 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-16612155019 / 1000000000000) (-16612154653 / 1000000000000), orderedInterval (37308136305 / 1000000000000) (37308136671 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1090653015399171 / 4000000000000) 1 (IntervalRat.scale (357 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-6246316097 / 1000000000000) (-6246316096 / 1000000000000), orderedInterval (-47903135349 / 1000000000000) (-47903135348 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1236684276603909 / 4000000000000) 1 (IntervalRat.scale (357 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (39620928452 / 1000000000000) (39620969068 / 1000000000000), orderedInterval (-22184157619 / 1000000000000) (-22184117002 / 1000000000000)))) (orderedInterval (-8166674423 / 1000000000000) (-8166674018 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1031018419015221 / 4000000000000) 1 (IntervalRat.scale (357 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (39806580669 / 1000000000000) (39806580670 / 1000000000000), orderedInterval (29676815952 / 1000000000000) (29676815953 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (910936040851641 / 4000000000000) 1 (IntervalRat.scale (357 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (38563339240 / 1000000000000) (38563394570 / 1000000000000), orderedInterval (-36255392512 / 1000000000000) (-36255337182 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (264024770076459 / 800000000000) 1 (IntervalRat.scale (357 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-35693344532 / 1000000000000) (-35693344531 / 1000000000000), orderedInterval (-25537998995 / 1000000000000) (-25537998994 / 1000000000000)))) (orderedInterval (1932939553 / 1000000000000) (1932943618 / 1000000000000))) = true
  rfl'

theorem compactCertificate305_chunkChecks1_2 :
    compactCertificate305.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (730306408893873 / 4000000000000) 1 (IntervalRat.scale (357 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (53872757748 / 1000000000000) (53872757749 / 1000000000000), orderedInterval (24030581160 / 1000000000000) (24030581161 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (619088830741353 / 4000000000000) 1 (IntervalRat.scale (357 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-64060855714 / 1000000000000) (-64060855616 / 1000000000000), orderedInterval (3281802739 / 1000000000000) (3281802838 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (387397045061859 / 4000000000000) 1 (IntervalRat.scale (357 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-19586413434 / 1000000000000) (-19586413433 / 1000000000000), orderedInterval (-78573881794 / 1000000000000) (-78573881793 / 1000000000000)))) (orderedInterval (-5479015972 / 1000000000000) (-5479015924 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (208343419258653 / 4000000000000) 1 (IntervalRat.scale (357 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (56670497499 / 1000000000000) (56670506674 / 1000000000000), orderedInterval (-95471458627 / 1000000000000) (-95471449453 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (565692911854959 / 4000000000000) 1 (IntervalRat.scale (357 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-49784219256 / 1000000000000) (-49784219255 / 1000000000000), orderedInterval (-44802326293 / 1000000000000) (-44802326292 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (772405308563343 / 4000000000000) 1 (IntervalRat.scale (357 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-44714025327 / 1000000000000) (-44713920089 / 1000000000000), orderedInterval (36136207186 / 1000000000000) (36136312425 / 1000000000000)))) (orderedInterval (-1676280271 / 1000000000000) (-1676271477 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (326602954938141 / 4000000000000) 1 (IntervalRat.scale (357 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (60394290482 / 1000000000000) (60394290483 / 1000000000000), orderedInterval (64046047637 / 1000000000000) (64046047638 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1327622879369661 / 4000000000000) 1 (IntervalRat.scale (357 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-13696844361 / 1000000000000) (-13696844228 / 1000000000000), orderedInterval (41619579777 / 1000000000000) (41619579911 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (886790555979699 / 4000000000000) 1 (IntervalRat.scale (357 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (28944520994 / 1000000000000) (28944526390 / 1000000000000), orderedInterval (-45162789827 / 1000000000000) (-45162784431 / 1000000000000)))) (orderedInterval (4401489983 / 1000000000000) (4401491331 / 1000000000000))) = true
  rfl'

theorem compactCertificate305_chunkChecks1 :
    compactCertificate305.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate305.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate305_chunkChecks1_0
    compactCertificate305_chunkChecks1_1 compactCertificate305_chunkChecks1_2

theorem compactCertificate305_chunkChecks2_0 :
    compactCertificate305.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (357 / 2) 2 (IntervalRat.scale (357 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-12677901057 / 1000000000000) (-12677901056 / 1000000000000), orderedInterval (-58323556476 / 1000000000000) (-58323556475 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (525929168400657 / 4000000000000) 2 (IntervalRat.scale (357 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (21878540597 / 1000000000000) (21878540598 / 1000000000000), orderedInterval (65971510435 / 1000000000000) (65971510436 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (170074687164081 / 800000000000) 2 (IntervalRat.scale (357 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-13545483534 / 1000000000000) (-13545483414 / 1000000000000), orderedInterval (53051375461 / 1000000000000) (53051375581 / 1000000000000)))) (orderedInterval (6148163881 / 1000000000000) (6148163908 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (153464819653299 / 4000000000000) 2 (IntervalRat.scale (357 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (127858743137 / 1000000000000) (127858743140 / 1000000000000), orderedInterval (13955095899 / 1000000000000) (13955095902 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (412228092201303 / 4000000000000) 2 (IntervalRat.scale (357 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-13192476806 / 1000000000000) (-13192476804 / 1000000000000), orderedInterval (-77417488571 / 1000000000000) (-77417488570 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1119279460110651 / 4000000000000) 2 (IntervalRat.scale (357 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-40215445085 / 1000000000000) (-40215445084 / 1000000000000), orderedInterval (-25576184563 / 1000000000000) (-25576184562 / 1000000000000)))) (orderedInterval (-6807540361 / 1000000000000) (-6807540327 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (824456184402963 / 4000000000000) 2 (IntervalRat.scale (357 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-23987091900 / 1000000000000) (-23987090397 / 1000000000000), orderedInterval (50191035714 / 1000000000000) (50191037216 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1412719724379999 / 4000000000000) 2 (IntervalRat.scale (357 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (36506397319 / 1000000000000) (36506459791 / 1000000000000), orderedInterval (-21726961164 / 1000000000000) (-21726898692 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1040602954938141 / 4000000000000) 2 (IntervalRat.scale (357 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-9024933024 / 1000000000000) (-9024933023 / 1000000000000), orderedInterval (-48620845611 / 1000000000000) (-48620845610 / 1000000000000)))) (orderedInterval (4873601290 / 1000000000000) (4873608887 / 1000000000000))) = true
  rfl'

theorem compactCertificate305_chunkChecks2_1 :
    compactCertificate305.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1596552535934643 / 4000000000000) 2 (IntervalRat.scale (357 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-32274067388 / 1000000000000) (-32274067387 / 1000000000000), orderedInterval (-23483394096 / 1000000000000) (-23483394095 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (921770036397147 / 4000000000000) 2 (IntervalRat.scale (357 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-49887106689 / 1000000000000) (-49887102313 / 1000000000000), orderedInterval (16657212917 / 1000000000000) (16657217294 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1635697105105623 / 4000000000000) 2 (IntervalRat.scale (357 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (38043048213 / 1000000000000) (38043048219 / 1000000000000), orderedInterval (10419680968 / 1000000000000) (10419680974 / 1000000000000)))) (orderedInterval (-50975821797 / 1000000000000) (-50975820934 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1528280412637587 / 4000000000000) 2 (IntervalRat.scale (357 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-16612155019 / 1000000000000) (-16612154653 / 1000000000000), orderedInterval (37308136305 / 1000000000000) (37308136671 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1090653015399171 / 4000000000000) 2 (IntervalRat.scale (357 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-6246316097 / 1000000000000) (-6246316096 / 1000000000000), orderedInterval (-47903135349 / 1000000000000) (-47903135348 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1236684276603909 / 4000000000000) 2 (IntervalRat.scale (357 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (39620928452 / 1000000000000) (39620969068 / 1000000000000), orderedInterval (-22184157619 / 1000000000000) (-22184117002 / 1000000000000)))) (orderedInterval (651493609 / 1000000000000) (651494316 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1031018419015221 / 4000000000000) 2 (IntervalRat.scale (357 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (39806580669 / 1000000000000) (39806580670 / 1000000000000), orderedInterval (29676815952 / 1000000000000) (29676815953 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (910936040851641 / 4000000000000) 2 (IntervalRat.scale (357 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (38563339240 / 1000000000000) (38563394570 / 1000000000000), orderedInterval (-36255392512 / 1000000000000) (-36255337182 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (264024770076459 / 800000000000) 2 (IntervalRat.scale (357 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-35693344532 / 1000000000000) (-35693344531 / 1000000000000), orderedInterval (-25537998995 / 1000000000000) (-25537998994 / 1000000000000)))) (orderedInterval (5746935197 / 1000000000000) (5746940411 / 1000000000000))) = true
  rfl'

theorem compactCertificate305_chunkChecks2_2 :
    compactCertificate305.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (730306408893873 / 4000000000000) 2 (IntervalRat.scale (357 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (53872757748 / 1000000000000) (53872757749 / 1000000000000), orderedInterval (24030581160 / 1000000000000) (24030581161 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (619088830741353 / 4000000000000) 2 (IntervalRat.scale (357 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-64060855714 / 1000000000000) (-64060855616 / 1000000000000), orderedInterval (3281802739 / 1000000000000) (3281802838 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (387397045061859 / 4000000000000) 2 (IntervalRat.scale (357 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-19586413434 / 1000000000000) (-19586413433 / 1000000000000), orderedInterval (-78573881794 / 1000000000000) (-78573881793 / 1000000000000)))) (orderedInterval (6504241557 / 1000000000000) (6504241602 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (208343419258653 / 4000000000000) 2 (IntervalRat.scale (357 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (56670497499 / 1000000000000) (56670506674 / 1000000000000), orderedInterval (-95471458627 / 1000000000000) (-95471449453 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (565692911854959 / 4000000000000) 2 (IntervalRat.scale (357 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-49784219256 / 1000000000000) (-49784219255 / 1000000000000), orderedInterval (-44802326293 / 1000000000000) (-44802326292 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (772405308563343 / 4000000000000) 2 (IntervalRat.scale (357 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-44714025327 / 1000000000000) (-44713920089 / 1000000000000), orderedInterval (36136207186 / 1000000000000) (36136312425 / 1000000000000)))) (orderedInterval (-4620878713 / 1000000000000) (-4620869191 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (326602954938141 / 4000000000000) 2 (IntervalRat.scale (357 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (60394290482 / 1000000000000) (60394290483 / 1000000000000), orderedInterval (64046047637 / 1000000000000) (64046047638 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1327622879369661 / 4000000000000) 2 (IntervalRat.scale (357 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-13696844361 / 1000000000000) (-13696844228 / 1000000000000), orderedInterval (41619579777 / 1000000000000) (41619579911 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (886790555979699 / 4000000000000) 2 (IntervalRat.scale (357 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (28944520994 / 1000000000000) (28944526390 / 1000000000000), orderedInterval (-45162789827 / 1000000000000) (-45162784431 / 1000000000000)))) (orderedInterval (4421655984 / 1000000000000) (4421657693 / 1000000000000))) = true
  rfl'

theorem compactCertificate305_chunkChecks2 :
    compactCertificate305.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate305.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate305_chunkChecks2_0
    compactCertificate305_chunkChecks2_1 compactCertificate305_chunkChecks2_2

theorem compactCertificate305_chunkChecks3_0 :
    compactCertificate305.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (357 / 2) 3 (IntervalRat.scale (357 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-12677901057 / 1000000000000) (-12677901056 / 1000000000000), orderedInterval (-58323556476 / 1000000000000) (-58323556475 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (525929168400657 / 4000000000000) 3 (IntervalRat.scale (357 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (21878540597 / 1000000000000) (21878540598 / 1000000000000), orderedInterval (65971510435 / 1000000000000) (65971510436 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (170074687164081 / 800000000000) 3 (IntervalRat.scale (357 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-13545483534 / 1000000000000) (-13545483414 / 1000000000000), orderedInterval (53051375461 / 1000000000000) (53051375581 / 1000000000000)))) (orderedInterval (17577377811 / 1000000000000) (17577377843 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (153464819653299 / 4000000000000) 3 (IntervalRat.scale (357 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (127858743137 / 1000000000000) (127858743140 / 1000000000000), orderedInterval (13955095899 / 1000000000000) (13955095902 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (412228092201303 / 4000000000000) 3 (IntervalRat.scale (357 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-13192476806 / 1000000000000) (-13192476804 / 1000000000000), orderedInterval (-77417488571 / 1000000000000) (-77417488570 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1119279460110651 / 4000000000000) 3 (IntervalRat.scale (357 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-40215445085 / 1000000000000) (-40215445084 / 1000000000000), orderedInterval (-25576184563 / 1000000000000) (-25576184562 / 1000000000000)))) (orderedInterval (-6420606044 / 1000000000000) (-6420605992 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (824456184402963 / 4000000000000) 3 (IntervalRat.scale (357 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-23987091900 / 1000000000000) (-23987090397 / 1000000000000), orderedInterval (50191035714 / 1000000000000) (50191037216 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1412719724379999 / 4000000000000) 3 (IntervalRat.scale (357 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (36506397319 / 1000000000000) (36506459791 / 1000000000000), orderedInterval (-21726961164 / 1000000000000) (-21726898692 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1040602954938141 / 4000000000000) 3 (IntervalRat.scale (357 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-9024933024 / 1000000000000) (-9024933023 / 1000000000000), orderedInterval (-48620845611 / 1000000000000) (-48620845610 / 1000000000000)))) (orderedInterval (-1580542537 / 1000000000000) (-1580527513 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate305_chunkChecks3_1 :
    compactCertificate305.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1596552535934643 / 4000000000000) 3 (IntervalRat.scale (357 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-32274067388 / 1000000000000) (-32274067387 / 1000000000000), orderedInterval (-23483394096 / 1000000000000) (-23483394095 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (921770036397147 / 4000000000000) 3 (IntervalRat.scale (357 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-49887106689 / 1000000000000) (-49887102313 / 1000000000000), orderedInterval (16657212917 / 1000000000000) (16657217294 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1635697105105623 / 4000000000000) 3 (IntervalRat.scale (357 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (38043048213 / 1000000000000) (38043048219 / 1000000000000), orderedInterval (10419680968 / 1000000000000) (10419680974 / 1000000000000)))) (orderedInterval (-66830590781 / 1000000000000) (-66830589379 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1528280412637587 / 4000000000000) 3 (IntervalRat.scale (357 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-16612155019 / 1000000000000) (-16612154653 / 1000000000000), orderedInterval (37308136305 / 1000000000000) (37308136671 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1090653015399171 / 4000000000000) 3 (IntervalRat.scale (357 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-6246316097 / 1000000000000) (-6246316096 / 1000000000000), orderedInterval (-47903135349 / 1000000000000) (-47903135348 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1236684276603909 / 4000000000000) 3 (IntervalRat.scale (357 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (39620928452 / 1000000000000) (39620969068 / 1000000000000), orderedInterval (-22184157619 / 1000000000000) (-22184117002 / 1000000000000)))) (orderedInterval (22163134163 / 1000000000000) (22163135397 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1031018419015221 / 4000000000000) 3 (IntervalRat.scale (357 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (39806580669 / 1000000000000) (39806580670 / 1000000000000), orderedInterval (29676815952 / 1000000000000) (29676815953 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (910936040851641 / 4000000000000) 3 (IntervalRat.scale (357 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (38563339240 / 1000000000000) (38563394570 / 1000000000000), orderedInterval (-36255392512 / 1000000000000) (-36255337182 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (264024770076459 / 800000000000) 3 (IntervalRat.scale (357 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-35693344532 / 1000000000000) (-35693344531 / 1000000000000), orderedInterval (-25537998995 / 1000000000000) (-25537998994 / 1000000000000)))) (orderedInterval (-1239834990 / 1000000000000) (-1239828329 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate305_chunkChecks3_2 :
    compactCertificate305.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (730306408893873 / 4000000000000) 3 (IntervalRat.scale (357 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (53872757748 / 1000000000000) (53872757749 / 1000000000000), orderedInterval (24030581160 / 1000000000000) (24030581161 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (619088830741353 / 4000000000000) 3 (IntervalRat.scale (357 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-64060855714 / 1000000000000) (-64060855616 / 1000000000000), orderedInterval (3281802739 / 1000000000000) (3281802838 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (387397045061859 / 4000000000000) 3 (IntervalRat.scale (357 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-19586413434 / 1000000000000) (-19586413433 / 1000000000000), orderedInterval (-78573881794 / 1000000000000) (-78573881793 / 1000000000000)))) (orderedInterval (4604671709 / 1000000000000) (4604671752 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (208343419258653 / 4000000000000) 3 (IntervalRat.scale (357 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (56670497499 / 1000000000000) (56670506674 / 1000000000000), orderedInterval (-95471458627 / 1000000000000) (-95471449453 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (565692911854959 / 4000000000000) 3 (IntervalRat.scale (357 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-49784219256 / 1000000000000) (-49784219255 / 1000000000000), orderedInterval (-44802326293 / 1000000000000) (-44802326292 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (772405308563343 / 4000000000000) 3 (IntervalRat.scale (357 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-44714025327 / 1000000000000) (-44713920089 / 1000000000000), orderedInterval (36136207186 / 1000000000000) (36136312425 / 1000000000000)))) (orderedInterval (2982701769 / 1000000000000) (2982712057 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (326602954938141 / 4000000000000) 3 (IntervalRat.scale (357 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (60394290482 / 1000000000000) (60394290483 / 1000000000000), orderedInterval (64046047637 / 1000000000000) (64046047638 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1327622879369661 / 4000000000000) 3 (IntervalRat.scale (357 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-13696844361 / 1000000000000) (-13696844228 / 1000000000000), orderedInterval (41619579777 / 1000000000000) (41619579911 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (886790555979699 / 4000000000000) 3 (IntervalRat.scale (357 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (28944520994 / 1000000000000) (28944526390 / 1000000000000), orderedInterval (-45162789827 / 1000000000000) (-45162784431 / 1000000000000)))) (orderedInterval (5483903477 / 1000000000000) (5483905654 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate305_chunkChecks3 :
    compactCertificate305.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate305.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate305_chunkChecks3_0
    compactCertificate305_chunkChecks3_1 compactCertificate305_chunkChecks3_2

theorem compactCertificate305_chunkChecks4_0 :
    compactCertificate305.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (357 / 2) 4 (IntervalRat.scale (357 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-12677901057 / 1000000000000) (-12677901056 / 1000000000000), orderedInterval (-58323556476 / 1000000000000) (-58323556475 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (525929168400657 / 4000000000000) 4 (IntervalRat.scale (357 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (21878540597 / 1000000000000) (21878540598 / 1000000000000), orderedInterval (65971510435 / 1000000000000) (65971510436 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (170074687164081 / 800000000000) 4 (IntervalRat.scale (357 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-13545483534 / 1000000000000) (-13545483414 / 1000000000000), orderedInterval (53051375461 / 1000000000000) (53051375581 / 1000000000000)))) (orderedInterval (-6761143444 / 1000000000000) (-6761143407 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (153464819653299 / 4000000000000) 4 (IntervalRat.scale (357 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (127858743137 / 1000000000000) (127858743140 / 1000000000000), orderedInterval (13955095899 / 1000000000000) (13955095902 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (412228092201303 / 4000000000000) 4 (IntervalRat.scale (357 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-13192476806 / 1000000000000) (-13192476804 / 1000000000000), orderedInterval (-77417488571 / 1000000000000) (-77417488570 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1119279460110651 / 4000000000000) 4 (IntervalRat.scale (357 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-40215445085 / 1000000000000) (-40215445084 / 1000000000000), orderedInterval (-25576184563 / 1000000000000) (-25576184562 / 1000000000000)))) (orderedInterval (17280002848 / 1000000000000) (17280002927 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (824456184402963 / 4000000000000) 4 (IntervalRat.scale (357 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-23987091900 / 1000000000000) (-23987090397 / 1000000000000), orderedInterval (50191035714 / 1000000000000) (50191037216 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1412719724379999 / 4000000000000) 4 (IntervalRat.scale (357 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (36506397319 / 1000000000000) (36506459791 / 1000000000000), orderedInterval (-21726961164 / 1000000000000) (-21726898692 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1040602954938141 / 4000000000000) 4 (IntervalRat.scale (357 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-9024933024 / 1000000000000) (-9024933023 / 1000000000000), orderedInterval (-48620845611 / 1000000000000) (-48620845610 / 1000000000000)))) (orderedInterval (-18223473919 / 1000000000000) (-18223444116 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate305_chunkChecks4_1 :
    compactCertificate305.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1596552535934643 / 4000000000000) 4 (IntervalRat.scale (357 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-32274067388 / 1000000000000) (-32274067387 / 1000000000000), orderedInterval (-23483394096 / 1000000000000) (-23483394095 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (921770036397147 / 4000000000000) 4 (IntervalRat.scale (357 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-49887106689 / 1000000000000) (-49887102313 / 1000000000000), orderedInterval (16657212917 / 1000000000000) (16657217294 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1635697105105623 / 4000000000000) 4 (IntervalRat.scale (357 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (38043048213 / 1000000000000) (38043048219 / 1000000000000), orderedInterval (10419680968 / 1000000000000) (10419680974 / 1000000000000)))) (orderedInterval (282804008666 / 1000000000000) (282804011133 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1528280412637587 / 4000000000000) 4 (IntervalRat.scale (357 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-16612155019 / 1000000000000) (-16612154653 / 1000000000000), orderedInterval (37308136305 / 1000000000000) (37308136671 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1090653015399171 / 4000000000000) 4 (IntervalRat.scale (357 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-6246316097 / 1000000000000) (-6246316096 / 1000000000000), orderedInterval (-47903135349 / 1000000000000) (-47903135348 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1236684276603909 / 4000000000000) 4 (IntervalRat.scale (357 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (39620928452 / 1000000000000) (39620969068 / 1000000000000), orderedInterval (-22184157619 / 1000000000000) (-22184117002 / 1000000000000)))) (orderedInterval (1026298292 / 1000000000000) (1026300462 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1031018419015221 / 4000000000000) 4 (IntervalRat.scale (357 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (39806580669 / 1000000000000) (39806580670 / 1000000000000), orderedInterval (29676815952 / 1000000000000) (29676815953 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (910936040851641 / 4000000000000) 4 (IntervalRat.scale (357 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (38563339240 / 1000000000000) (38563394570 / 1000000000000), orderedInterval (-36255392512 / 1000000000000) (-36255337182 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (264024770076459 / 800000000000) 4 (IntervalRat.scale (357 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-35693344532 / 1000000000000) (-35693344531 / 1000000000000), orderedInterval (-25537998995 / 1000000000000) (-25537998994 / 1000000000000)))) (orderedInterval (-14514062733 / 1000000000000) (-14514054180 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate305_chunkChecks4_2 :
    compactCertificate305.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (730306408893873 / 4000000000000) 4 (IntervalRat.scale (357 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (53872757748 / 1000000000000) (53872757749 / 1000000000000), orderedInterval (24030581160 / 1000000000000) (24030581161 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (619088830741353 / 4000000000000) 4 (IntervalRat.scale (357 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-64060855714 / 1000000000000) (-64060855616 / 1000000000000), orderedInterval (3281802739 / 1000000000000) (3281802838 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (387397045061859 / 4000000000000) 4 (IntervalRat.scale (357 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-19586413434 / 1000000000000) (-19586413433 / 1000000000000), orderedInterval (-78573881794 / 1000000000000) (-78573881793 / 1000000000000)))) (orderedInterval (-7485354509 / 1000000000000) (-7485354468 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (208343419258653 / 4000000000000) 4 (IntervalRat.scale (357 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (56670497499 / 1000000000000) (56670506674 / 1000000000000), orderedInterval (-95471458627 / 1000000000000) (-95471449453 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (565692911854959 / 4000000000000) 4 (IntervalRat.scale (357 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-49784219256 / 1000000000000) (-49784219255 / 1000000000000), orderedInterval (-44802326293 / 1000000000000) (-44802326292 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (772405308563343 / 4000000000000) 4 (IntervalRat.scale (357 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-44714025327 / 1000000000000) (-44713920089 / 1000000000000), orderedInterval (36136207186 / 1000000000000) (36136312425 / 1000000000000)))) (orderedInterval (5097204347 / 1000000000000) (5097215529 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (326602954938141 / 4000000000000) 4 (IntervalRat.scale (357 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (60394290482 / 1000000000000) (60394290483 / 1000000000000), orderedInterval (64046047637 / 1000000000000) (64046047638 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1327622879369661 / 4000000000000) 4 (IntervalRat.scale (357 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-13696844361 / 1000000000000) (-13696844228 / 1000000000000), orderedInterval (41619579777 / 1000000000000) (41619579911 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (886790555979699 / 4000000000000) 4 (IntervalRat.scale (357 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (28944520994 / 1000000000000) (28944526390 / 1000000000000), orderedInterval (-45162789827 / 1000000000000) (-45162784431 / 1000000000000)))) (orderedInterval (359829903 / 1000000000000) (359832718 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate305_chunkChecks4 :
    compactCertificate305.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate305.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate305_chunkChecks4_0
    compactCertificate305_chunkChecks4_1 compactCertificate305_chunkChecks4_2

theorem compactCertificate305_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate305.chunkCheck r b = true :=
  compactCertificate305.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate305_chunkChecks0
    · exact compactCertificate305_chunkChecks1
    · exact compactCertificate305_chunkChecks2
    · exact compactCertificate305_chunkChecks3
    · exact compactCertificate305_chunkChecks4)

theorem compactCertificate305_coefficient0 :
    compactCertificate305.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate305_coefficient1 :
    compactCertificate305.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate305_coefficient2 :
    compactCertificate305.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate305_coefficient3 :
    compactCertificate305.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate305_coefficient4 :
    compactCertificate305.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate305_coefficients : ∀ r : Fin 5,
    compactCertificate305.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate305_coefficient0
  · exact compactCertificate305_coefficient1
  · exact compactCertificate305_coefficient2
  · exact compactCertificate305_coefficient3
  · exact compactCertificate305_coefficient4

theorem compactCertificate305_lower : (1 : ℚ) ≤ compactCertificate305.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate305, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate305_proves {t : ℝ} (ht : t ∈ compactCertificate305.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate305.proves compactCertificate305_states compactCertificate305_chunks
    compactCertificate305_coefficients compactCertificate305_lower ht

end Erdos232
