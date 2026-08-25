/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate279 : CompactCertificate where
  left := 153
  right := 154
  center := 307 / 2
  grid := fun i =>
    match i.val with
    | 0 => 49
    | 1 => 36
    | 2 => 58
    | 3 => 11
    | 4 => 28
    | 5 => 77
    | 6 => 56
    | 7 => 97
    | 8 => 71
    | 9 => 109
    | 10 => 63
    | 11 => 112
    | 12 => 105
    | 13 => 75
    | 14 => 85
    | 15 => 71
    | 16 => 62
    | 17 => 90
    | 18 => 50
    | 19 => 42
    | 20 => 27
    | 21 => 14
    | 22 => 39
    | 23 => 53
    | 24 => 22
    | 25 => 91
    | _ => 61
  point := fun i =>
    match i.val with
    | 0 => 307 / 2
    | 1 => 452269621005607 / 4000000000000
    | 2 => 146254702967431 / 800000000000
    | 3 => 131971147432949 / 4000000000000
    | 4 => 354493065282353 / 4000000000000
    | 5 => 962517630963501 / 4000000000000
    | 6 => 708986130565013 / 4000000000000
    | 7 => 1214859819004649 / 4000000000000
    | 8 => 894860244162491 / 4000000000000
    | 9 => 1372945738184693 / 4000000000000
    | 10 => 792670591523597 / 4000000000000
    | 11 => 1406607874698673 / 4000000000000
    | 12 => 1314235536918037 / 4000000000000
    | 13 => 937900492234021 / 4000000000000
    | 14 => 1063479195847059 / 4000000000000
    | 15 => 886618080217571 / 4000000000000
    | 16 => 783353962300991 / 4000000000000
    | 17 => 227046510962109 / 800000000000
    | 18 => 628022598124423 / 4000000000000
    | 19 => 532381711589903 / 4000000000000
    | 20 => 333139755837509 / 4000000000000
    | 21 => 179163668662203 / 4000000000000
    | 22 => 486464212715609 / 4000000000000
    | 23 => 664225293358393 / 4000000000000
    | 24 => 280860244162491 / 4000000000000
    | 25 => 1141681299626011 / 4000000000000
    | _ => 762590197999349 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-21873346027 / 1000000000000) (-21873346026 / 1000000000000), orderedInterval (-60500475993 / 1000000000000) (-60500475992 / 1000000000000))
    | 1 => (orderedInterval (51386414042 / 1000000000000) (51386414043 / 1000000000000), orderedInterval (54452603386 / 1000000000000) (54452603387 / 1000000000000))
    | 2 => (orderedInterval (58056297418 / 1000000000000) (58056297422 / 1000000000000), orderedInterval (10410360308 / 1000000000000) (10410360312 / 1000000000000))
    | 3 => (orderedInterval (97993947552 / 1000000000000) (97994041072 / 1000000000000), orderedInterval (-99937373817 / 1000000000000) (-99937280297 / 1000000000000))
    | 4 => (orderedInterval (84059653853 / 1000000000000) (84059653857 / 1000000000000), orderedInterval (10356385671 / 1000000000000) (10356385676 / 1000000000000))
    | 5 => (orderedInterval (24131992124 / 1000000000000) (24131994115 / 1000000000000), orderedInterval (-45473642567 / 1000000000000) (-45473640576 / 1000000000000))
    | 6 => (orderedInterval (51671105490 / 1000000000000) (51671132574 / 1000000000000), orderedInterval (-30507057509 / 1000000000000) (-30507030425 / 1000000000000))
    | 7 => (orderedInterval (10640096970 / 1000000000000) (10640097020 / 1000000000000), orderedInterval (-44547284943 / 1000000000000) (-44547284893 / 1000000000000))
    | 8 => (orderedInterval (-52935357801 / 1000000000000) (-52935357788 / 1000000000000), orderedInterval (-6478159209 / 1000000000000) (-6478159196 / 1000000000000))
    | 9 => (orderedInterval (-43060576785 / 1000000000000) (-43060576549 / 1000000000000), orderedInterval (797970863 / 1000000000000) (797971099 / 1000000000000))
    | 10 => (orderedInterval (-48651473275 / 1000000000000) (-48651473274 / 1000000000000), orderedInterval (-28955772360 / 1000000000000) (-28955772359 / 1000000000000))
    | 11 => (orderedInterval (23268914327 / 1000000000000) (23268914328 / 1000000000000), orderedInterval (35588919604 / 1000000000000) (35588919605 / 1000000000000))
    | 12 => (orderedInterval (21998772556 / 1000000000000) (21998774344 / 1000000000000), orderedInterval (-38160470229 / 1000000000000) (-38160468441 / 1000000000000))
    | 13 => (orderedInterval (18329453990 / 1000000000000) (18329454433 / 1000000000000), orderedInterval (-48815312492 / 1000000000000) (-48815312049 / 1000000000000))
    | 14 => (orderedInterval (18179859784 / 1000000000000) (18179860258 / 1000000000000), orderedInterval (-45465183489 / 1000000000000) (-45465183015 / 1000000000000))
    | 15 => (orderedInterval (30864571890 / 1000000000000) (30864580297 / 1000000000000), orderedInterval (-43881801812 / 1000000000000) (-43881793405 / 1000000000000))
    | 16 => (orderedInterval (54892755345 / 1000000000000) (54892757521 / 1000000000000), orderedInterval (-15551669887 / 1000000000000) (-15551667712 / 1000000000000))
    | 17 => (orderedInterval (45530790327 / 1000000000000) (45530794080 / 1000000000000), orderedInterval (-13121623068 / 1000000000000) (-13121619315 / 1000000000000))
    | 18 => (orderedInterval (41536575196 / 1000000000000) (41536575197 / 1000000000000), orderedInterval (48132339269 / 1000000000000) (48132339270 / 1000000000000))
    | 19 => (orderedInterval (64673181880 / 1000000000000) (64673185938 / 1000000000000), orderedInterval (-24748810407 / 1000000000000) (-24748806349 / 1000000000000))
    | 20 => (orderedInterval (59860544064 / 1000000000000) (59860603949 / 1000000000000), orderedInterval (-64082196256 / 1000000000000) (-64082136371 / 1000000000000))
    | 21 => (orderedInterval (119190298806 / 1000000000000) (119190298836 / 1000000000000), orderedInterval (-3766119700 / 1000000000000) (-3766119670 / 1000000000000))
    | 22 => (orderedInterval (8782639096 / 1000000000000) (8782639132 / 1000000000000), orderedInterval (-71852380627 / 1000000000000) (-71852380590 / 1000000000000))
    | 23 => (orderedInterval (-20447555968 / 1000000000000) (-20447555967 / 1000000000000), orderedInterval (-58382158595 / 1000000000000) (-58382158594 / 1000000000000))
    | 24 => (orderedInterval (90596383428 / 1000000000000) (90596385096 / 1000000000000), orderedInterval (-29950757705 / 1000000000000) (-29950756036 / 1000000000000))
    | 25 => (orderedInterval (-14872124810 / 1000000000000) (-14872124809 / 1000000000000), orderedInterval (-44799014732 / 1000000000000) (-44799014731 / 1000000000000))
    | _ => (orderedInterval (11755431889 / 1000000000000) (11755431963 / 1000000000000), orderedInterval (-56608829821 / 1000000000000) (-56608829746 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-4784197245 / 1000000000000) (-4784197233 / 1000000000000)
      | 1 => orderedInterval (290464055 / 1000000000000) (290465230 / 1000000000000)
      | 2 => orderedInterval (-1607526324 / 1000000000000) (-1607526313 / 1000000000000)
      | 3 => orderedInterval (7354483964 / 1000000000000) (7354484068 / 1000000000000)
      | 4 => orderedInterval (1244139362 / 1000000000000) (1244139458 / 1000000000000)
      | 5 => orderedInterval (-1619148142 / 1000000000000) (-1619147809 / 1000000000000)
      | 6 => orderedInterval (-8353107704 / 1000000000000) (-8353105486 / 1000000000000)
      | 7 => orderedInterval (-833035761 / 1000000000000) (-833035741 / 1000000000000)
      | _ => orderedInterval (-448868792 / 1000000000000) (-448868725 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-22878955975 / 1000000000000) (-22878955961 / 1000000000000)
      | 1 => orderedInterval (5519005284 / 1000000000000) (5519005746 / 1000000000000)
      | 2 => orderedInterval (2490446645 / 1000000000000) (2490446664 / 1000000000000)
      | 3 => orderedInterval (8503293000 / 1000000000000) (8503293221 / 1000000000000)
      | 4 => orderedInterval (-5178137597 / 1000000000000) (-5178137430 / 1000000000000)
      | 5 => orderedInterval (-217451737 / 1000000000000) (-217451238 / 1000000000000)
      | 6 => orderedInterval (-7789104908 / 1000000000000) (-7789103615 / 1000000000000)
      | 7 => orderedInterval (6152147720 / 1000000000000) (6152147738 / 1000000000000)
      | _ => orderedInterval (19889892942 / 1000000000000) (19889893025 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (3726593100 / 1000000000000) (3726593115 / 1000000000000)
      | 1 => orderedInterval (3205907881 / 1000000000000) (3205908309 / 1000000000000)
      | 2 => orderedInterval (3986009645 / 1000000000000) (3986009679 / 1000000000000)
      | 3 => orderedInterval (-49664353823 / 1000000000000) (-49664353341 / 1000000000000)
      | 4 => orderedInterval (-1915066477 / 1000000000000) (-1915066174 / 1000000000000)
      | 5 => orderedInterval (386288795 / 1000000000000) (386289564 / 1000000000000)
      | 6 => orderedInterval (9177262261 / 1000000000000) (9177263051 / 1000000000000)
      | 7 => orderedInterval (-1561549367 / 1000000000000) (-1561549349 / 1000000000000)
      | _ => orderedInterval (-1027125975 / 1000000000000) (-1027125862 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (22720194161 / 1000000000000) (22720194179 / 1000000000000)
      | 1 => orderedInterval (-12557562478 / 1000000000000) (-12557561876 / 1000000000000)
      | 2 => orderedInterval (-10184215083 / 1000000000000) (-10184215021 / 1000000000000)
      | 3 => orderedInterval (-54301323354 / 1000000000000) (-54301322289 / 1000000000000)
      | 4 => orderedInterval (8513758278 / 1000000000000) (8513758842 / 1000000000000)
      | 5 => orderedInterval (1798501461 / 1000000000000) (1798502673 / 1000000000000)
      | 6 => orderedInterval (7595386658 / 1000000000000) (7595387158 / 1000000000000)
      | 7 => orderedInterval (-6466613770 / 1000000000000) (-6466613752 / 1000000000000)
      | _ => orderedInterval (-43768375651 / 1000000000000) (-43768375486 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-1969950729 / 1000000000000) (-1969950709 / 1000000000000)
      | 1 => orderedInterval (-9857525222 / 1000000000000) (-9857524290 / 1000000000000)
      | 2 => orderedInterval (-10669008434 / 1000000000000) (-10669008319 / 1000000000000)
      | 3 => orderedInterval (273084692998 / 1000000000000) (273084695372 / 1000000000000)
      | 4 => orderedInterval (161542161 / 1000000000000) (161543240 / 1000000000000)
      | 5 => orderedInterval (6826522503 / 1000000000000) (6826524471 / 1000000000000)
      | 6 => orderedInterval (-9267872850 / 1000000000000) (-9267872512 / 1000000000000)
      | 7 => orderedInterval (2135962724 / 1000000000000) (2135962743 / 1000000000000)
      | _ => orderedInterval (9817247136 / 1000000000000) (9817247390 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-8756796587 / 1000000000000) (-8756792551 / 1000000000000)
    | 1 => orderedInterval (6491135374 / 1000000000000) (6491138150 / 1000000000000)
    | 2 => orderedInterval (-33686033960 / 1000000000000) (-33686031008 / 1000000000000)
    | 3 => orderedInterval (-86650249778 / 1000000000000) (-86650245572 / 1000000000000)
    | _ => orderedInterval (260261610287 / 1000000000000) (260261617386 / 1000000000000)

theorem compactCertificate279_stateChecks0 :
    compactCertificate279.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 49 12 (307 / 2)) (orderedInterval (-21873346027 / 1000000000000) (-21873346026 / 1000000000000), orderedInterval (-60500475993 / 1000000000000) (-60500475992 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 36 12 (452269621005607 / 4000000000000)) (orderedInterval (51386414042 / 1000000000000) (51386414043 / 1000000000000), orderedInterval (54452603386 / 1000000000000) (54452603387 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (146254702967431 / 800000000000)) (orderedInterval (58056297418 / 1000000000000) (58056297422 / 1000000000000), orderedInterval (10410360308 / 1000000000000) (10410360312 / 1000000000000))) = true
  rfl'

theorem compactCertificate279_stateChecks1 :
    compactCertificate279.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 11 12 (131971147432949 / 4000000000000)) (orderedInterval (97993947552 / 1000000000000) (97994041072 / 1000000000000), orderedInterval (-99937373817 / 1000000000000) (-99937280297 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 28 12 (354493065282353 / 4000000000000)) (orderedInterval (84059653853 / 1000000000000) (84059653857 / 1000000000000), orderedInterval (10356385671 / 1000000000000) (10356385676 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 77 12 (962517630963501 / 4000000000000)) (orderedInterval (24131992124 / 1000000000000) (24131994115 / 1000000000000), orderedInterval (-45473642567 / 1000000000000) (-45473640576 / 1000000000000))) = true
  rfl'

theorem compactCertificate279_stateChecks2 :
    compactCertificate279.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 56 12 (708986130565013 / 4000000000000)) (orderedInterval (51671105490 / 1000000000000) (51671132574 / 1000000000000), orderedInterval (-30507057509 / 1000000000000) (-30507030425 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 97 12 (1214859819004649 / 4000000000000)) (orderedInterval (10640096970 / 1000000000000) (10640097020 / 1000000000000), orderedInterval (-44547284943 / 1000000000000) (-44547284893 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (894860244162491 / 4000000000000)) (orderedInterval (-52935357801 / 1000000000000) (-52935357788 / 1000000000000), orderedInterval (-6478159209 / 1000000000000) (-6478159196 / 1000000000000))) = true
  rfl'

theorem compactCertificate279_stateChecks3 :
    compactCertificate279.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 109 12 (1372945738184693 / 4000000000000)) (orderedInterval (-43060576785 / 1000000000000) (-43060576549 / 1000000000000), orderedInterval (797970863 / 1000000000000) (797971099 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (792670591523597 / 4000000000000)) (orderedInterval (-48651473275 / 1000000000000) (-48651473274 / 1000000000000), orderedInterval (-28955772360 / 1000000000000) (-28955772359 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 112 12 (1406607874698673 / 4000000000000)) (orderedInterval (23268914327 / 1000000000000) (23268914328 / 1000000000000), orderedInterval (35588919604 / 1000000000000) (35588919605 / 1000000000000))) = true
  rfl'

theorem compactCertificate279_stateChecks4 :
    compactCertificate279.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 105 12 (1314235536918037 / 4000000000000)) (orderedInterval (21998772556 / 1000000000000) (21998774344 / 1000000000000), orderedInterval (-38160470229 / 1000000000000) (-38160468441 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 75 12 (937900492234021 / 4000000000000)) (orderedInterval (18329453990 / 1000000000000) (18329454433 / 1000000000000), orderedInterval (-48815312492 / 1000000000000) (-48815312049 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 85 12 (1063479195847059 / 4000000000000)) (orderedInterval (18179859784 / 1000000000000) (18179860258 / 1000000000000), orderedInterval (-45465183489 / 1000000000000) (-45465183015 / 1000000000000))) = true
  rfl'

theorem compactCertificate279_stateChecks5 :
    compactCertificate279.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (886618080217571 / 4000000000000)) (orderedInterval (30864571890 / 1000000000000) (30864580297 / 1000000000000), orderedInterval (-43881801812 / 1000000000000) (-43881793405 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (783353962300991 / 4000000000000)) (orderedInterval (54892755345 / 1000000000000) (54892757521 / 1000000000000), orderedInterval (-15551669887 / 1000000000000) (-15551667712 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 90 12 (227046510962109 / 800000000000)) (orderedInterval (45530790327 / 1000000000000) (45530794080 / 1000000000000), orderedInterval (-13121623068 / 1000000000000) (-13121619315 / 1000000000000))) = true
  rfl'

theorem compactCertificate279_stateChecks6 :
    compactCertificate279.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 50 12 (628022598124423 / 4000000000000)) (orderedInterval (41536575196 / 1000000000000) (41536575197 / 1000000000000), orderedInterval (48132339269 / 1000000000000) (48132339270 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 42 12 (532381711589903 / 4000000000000)) (orderedInterval (64673181880 / 1000000000000) (64673185938 / 1000000000000), orderedInterval (-24748810407 / 1000000000000) (-24748806349 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 27 12 (333139755837509 / 4000000000000)) (orderedInterval (59860544064 / 1000000000000) (59860603949 / 1000000000000), orderedInterval (-64082196256 / 1000000000000) (-64082136371 / 1000000000000))) = true
  rfl'

theorem compactCertificate279_stateChecks7 :
    compactCertificate279.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 14 12 (179163668662203 / 4000000000000)) (orderedInterval (119190298806 / 1000000000000) (119190298836 / 1000000000000), orderedInterval (-3766119700 / 1000000000000) (-3766119670 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 39 12 (486464212715609 / 4000000000000)) (orderedInterval (8782639096 / 1000000000000) (8782639132 / 1000000000000), orderedInterval (-71852380627 / 1000000000000) (-71852380590 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 53 12 (664225293358393 / 4000000000000)) (orderedInterval (-20447555968 / 1000000000000) (-20447555967 / 1000000000000), orderedInterval (-58382158595 / 1000000000000) (-58382158594 / 1000000000000))) = true
  rfl'

theorem compactCertificate279_stateChecks8 :
    compactCertificate279.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 22 12 (280860244162491 / 4000000000000)) (orderedInterval (90596383428 / 1000000000000) (90596385096 / 1000000000000), orderedInterval (-29950757705 / 1000000000000) (-29950756036 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 91 12 (1141681299626011 / 4000000000000)) (orderedInterval (-14872124810 / 1000000000000) (-14872124809 / 1000000000000), orderedInterval (-44799014732 / 1000000000000) (-44799014731 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 61 12 (762590197999349 / 4000000000000)) (orderedInterval (11755431889 / 1000000000000) (11755431963 / 1000000000000), orderedInterval (-56608829821 / 1000000000000) (-56608829746 / 1000000000000))) = true
  rfl'

theorem compactCertificate279_states : ∀ j,
    BesselStateValid (compactCertificate279.point j) (compactCertificate279.state j) :=
  compactCertificate279.statesValid_of_checks3 compactCertificate279_stateChecks0
    compactCertificate279_stateChecks1 compactCertificate279_stateChecks2
    compactCertificate279_stateChecks3 compactCertificate279_stateChecks4
    compactCertificate279_stateChecks5 compactCertificate279_stateChecks6
    compactCertificate279_stateChecks7 compactCertificate279_stateChecks8

theorem compactCertificate279_chunkChecks0_0 :
    compactCertificate279.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (307 / 2) 0 (IntervalRat.scale (307 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-21873346027 / 1000000000000) (-21873346026 / 1000000000000), orderedInterval (-60500475993 / 1000000000000) (-60500475992 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (452269621005607 / 4000000000000) 0 (IntervalRat.scale (307 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (51386414042 / 1000000000000) (51386414043 / 1000000000000), orderedInterval (54452603386 / 1000000000000) (54452603387 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (146254702967431 / 800000000000) 0 (IntervalRat.scale (307 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (58056297418 / 1000000000000) (58056297422 / 1000000000000), orderedInterval (10410360308 / 1000000000000) (10410360312 / 1000000000000)))) (orderedInterval (-4784197245 / 1000000000000) (-4784197233 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (131971147432949 / 4000000000000) 0 (IntervalRat.scale (307 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (97993947552 / 1000000000000) (97994041072 / 1000000000000), orderedInterval (-99937373817 / 1000000000000) (-99937280297 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (354493065282353 / 4000000000000) 0 (IntervalRat.scale (307 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (84059653853 / 1000000000000) (84059653857 / 1000000000000), orderedInterval (10356385671 / 1000000000000) (10356385676 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (962517630963501 / 4000000000000) 0 (IntervalRat.scale (307 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (24131992124 / 1000000000000) (24131994115 / 1000000000000), orderedInterval (-45473642567 / 1000000000000) (-45473640576 / 1000000000000)))) (orderedInterval (290464055 / 1000000000000) (290465230 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (708986130565013 / 4000000000000) 0 (IntervalRat.scale (307 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (51671105490 / 1000000000000) (51671132574 / 1000000000000), orderedInterval (-30507057509 / 1000000000000) (-30507030425 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1214859819004649 / 4000000000000) 0 (IntervalRat.scale (307 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (10640096970 / 1000000000000) (10640097020 / 1000000000000), orderedInterval (-44547284943 / 1000000000000) (-44547284893 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (894860244162491 / 4000000000000) 0 (IntervalRat.scale (307 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-52935357801 / 1000000000000) (-52935357788 / 1000000000000), orderedInterval (-6478159209 / 1000000000000) (-6478159196 / 1000000000000)))) (orderedInterval (-1607526324 / 1000000000000) (-1607526313 / 1000000000000))) = true
  rfl'

theorem compactCertificate279_chunkChecks0_1 :
    compactCertificate279.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1372945738184693 / 4000000000000) 0 (IntervalRat.scale (307 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-43060576785 / 1000000000000) (-43060576549 / 1000000000000), orderedInterval (797970863 / 1000000000000) (797971099 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (792670591523597 / 4000000000000) 0 (IntervalRat.scale (307 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-48651473275 / 1000000000000) (-48651473274 / 1000000000000), orderedInterval (-28955772360 / 1000000000000) (-28955772359 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1406607874698673 / 4000000000000) 0 (IntervalRat.scale (307 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (23268914327 / 1000000000000) (23268914328 / 1000000000000), orderedInterval (35588919604 / 1000000000000) (35588919605 / 1000000000000)))) (orderedInterval (7354483964 / 1000000000000) (7354484068 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1314235536918037 / 4000000000000) 0 (IntervalRat.scale (307 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (21998772556 / 1000000000000) (21998774344 / 1000000000000), orderedInterval (-38160470229 / 1000000000000) (-38160468441 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (937900492234021 / 4000000000000) 0 (IntervalRat.scale (307 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (18329453990 / 1000000000000) (18329454433 / 1000000000000), orderedInterval (-48815312492 / 1000000000000) (-48815312049 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1063479195847059 / 4000000000000) 0 (IntervalRat.scale (307 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (18179859784 / 1000000000000) (18179860258 / 1000000000000), orderedInterval (-45465183489 / 1000000000000) (-45465183015 / 1000000000000)))) (orderedInterval (1244139362 / 1000000000000) (1244139458 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (886618080217571 / 4000000000000) 0 (IntervalRat.scale (307 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (30864571890 / 1000000000000) (30864580297 / 1000000000000), orderedInterval (-43881801812 / 1000000000000) (-43881793405 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (783353962300991 / 4000000000000) 0 (IntervalRat.scale (307 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (54892755345 / 1000000000000) (54892757521 / 1000000000000), orderedInterval (-15551669887 / 1000000000000) (-15551667712 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (227046510962109 / 800000000000) 0 (IntervalRat.scale (307 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (45530790327 / 1000000000000) (45530794080 / 1000000000000), orderedInterval (-13121623068 / 1000000000000) (-13121619315 / 1000000000000)))) (orderedInterval (-1619148142 / 1000000000000) (-1619147809 / 1000000000000))) = true
  rfl'

theorem compactCertificate279_chunkChecks0_2 :
    compactCertificate279.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (628022598124423 / 4000000000000) 0 (IntervalRat.scale (307 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (41536575196 / 1000000000000) (41536575197 / 1000000000000), orderedInterval (48132339269 / 1000000000000) (48132339270 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (532381711589903 / 4000000000000) 0 (IntervalRat.scale (307 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (64673181880 / 1000000000000) (64673185938 / 1000000000000), orderedInterval (-24748810407 / 1000000000000) (-24748806349 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (333139755837509 / 4000000000000) 0 (IntervalRat.scale (307 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (59860544064 / 1000000000000) (59860603949 / 1000000000000), orderedInterval (-64082196256 / 1000000000000) (-64082136371 / 1000000000000)))) (orderedInterval (-8353107704 / 1000000000000) (-8353105486 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (179163668662203 / 4000000000000) 0 (IntervalRat.scale (307 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (119190298806 / 1000000000000) (119190298836 / 1000000000000), orderedInterval (-3766119700 / 1000000000000) (-3766119670 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (486464212715609 / 4000000000000) 0 (IntervalRat.scale (307 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (8782639096 / 1000000000000) (8782639132 / 1000000000000), orderedInterval (-71852380627 / 1000000000000) (-71852380590 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (664225293358393 / 4000000000000) 0 (IntervalRat.scale (307 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-20447555968 / 1000000000000) (-20447555967 / 1000000000000), orderedInterval (-58382158595 / 1000000000000) (-58382158594 / 1000000000000)))) (orderedInterval (-833035761 / 1000000000000) (-833035741 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (280860244162491 / 4000000000000) 0 (IntervalRat.scale (307 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (90596383428 / 1000000000000) (90596385096 / 1000000000000), orderedInterval (-29950757705 / 1000000000000) (-29950756036 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1141681299626011 / 4000000000000) 0 (IntervalRat.scale (307 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-14872124810 / 1000000000000) (-14872124809 / 1000000000000), orderedInterval (-44799014732 / 1000000000000) (-44799014731 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (762590197999349 / 4000000000000) 0 (IntervalRat.scale (307 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (11755431889 / 1000000000000) (11755431963 / 1000000000000), orderedInterval (-56608829821 / 1000000000000) (-56608829746 / 1000000000000)))) (orderedInterval (-448868792 / 1000000000000) (-448868725 / 1000000000000))) = true
  rfl'

theorem compactCertificate279_chunkChecks0 :
    compactCertificate279.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate279.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate279_chunkChecks0_0
    compactCertificate279_chunkChecks0_1 compactCertificate279_chunkChecks0_2

theorem compactCertificate279_chunkChecks1_0 :
    compactCertificate279.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (307 / 2) 1 (IntervalRat.scale (307 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-21873346027 / 1000000000000) (-21873346026 / 1000000000000), orderedInterval (-60500475993 / 1000000000000) (-60500475992 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (452269621005607 / 4000000000000) 1 (IntervalRat.scale (307 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (51386414042 / 1000000000000) (51386414043 / 1000000000000), orderedInterval (54452603386 / 1000000000000) (54452603387 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (146254702967431 / 800000000000) 1 (IntervalRat.scale (307 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (58056297418 / 1000000000000) (58056297422 / 1000000000000), orderedInterval (10410360308 / 1000000000000) (10410360312 / 1000000000000)))) (orderedInterval (-22878955975 / 1000000000000) (-22878955961 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (131971147432949 / 4000000000000) 1 (IntervalRat.scale (307 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (97993947552 / 1000000000000) (97994041072 / 1000000000000), orderedInterval (-99937373817 / 1000000000000) (-99937280297 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (354493065282353 / 4000000000000) 1 (IntervalRat.scale (307 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (84059653853 / 1000000000000) (84059653857 / 1000000000000), orderedInterval (10356385671 / 1000000000000) (10356385676 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (962517630963501 / 4000000000000) 1 (IntervalRat.scale (307 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (24131992124 / 1000000000000) (24131994115 / 1000000000000), orderedInterval (-45473642567 / 1000000000000) (-45473640576 / 1000000000000)))) (orderedInterval (5519005284 / 1000000000000) (5519005746 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (708986130565013 / 4000000000000) 1 (IntervalRat.scale (307 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (51671105490 / 1000000000000) (51671132574 / 1000000000000), orderedInterval (-30507057509 / 1000000000000) (-30507030425 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1214859819004649 / 4000000000000) 1 (IntervalRat.scale (307 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (10640096970 / 1000000000000) (10640097020 / 1000000000000), orderedInterval (-44547284943 / 1000000000000) (-44547284893 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (894860244162491 / 4000000000000) 1 (IntervalRat.scale (307 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-52935357801 / 1000000000000) (-52935357788 / 1000000000000), orderedInterval (-6478159209 / 1000000000000) (-6478159196 / 1000000000000)))) (orderedInterval (2490446645 / 1000000000000) (2490446664 / 1000000000000))) = true
  rfl'

theorem compactCertificate279_chunkChecks1_1 :
    compactCertificate279.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1372945738184693 / 4000000000000) 1 (IntervalRat.scale (307 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-43060576785 / 1000000000000) (-43060576549 / 1000000000000), orderedInterval (797970863 / 1000000000000) (797971099 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (792670591523597 / 4000000000000) 1 (IntervalRat.scale (307 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-48651473275 / 1000000000000) (-48651473274 / 1000000000000), orderedInterval (-28955772360 / 1000000000000) (-28955772359 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1406607874698673 / 4000000000000) 1 (IntervalRat.scale (307 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (23268914327 / 1000000000000) (23268914328 / 1000000000000), orderedInterval (35588919604 / 1000000000000) (35588919605 / 1000000000000)))) (orderedInterval (8503293000 / 1000000000000) (8503293221 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1314235536918037 / 4000000000000) 1 (IntervalRat.scale (307 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (21998772556 / 1000000000000) (21998774344 / 1000000000000), orderedInterval (-38160470229 / 1000000000000) (-38160468441 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (937900492234021 / 4000000000000) 1 (IntervalRat.scale (307 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (18329453990 / 1000000000000) (18329454433 / 1000000000000), orderedInterval (-48815312492 / 1000000000000) (-48815312049 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1063479195847059 / 4000000000000) 1 (IntervalRat.scale (307 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (18179859784 / 1000000000000) (18179860258 / 1000000000000), orderedInterval (-45465183489 / 1000000000000) (-45465183015 / 1000000000000)))) (orderedInterval (-5178137597 / 1000000000000) (-5178137430 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (886618080217571 / 4000000000000) 1 (IntervalRat.scale (307 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (30864571890 / 1000000000000) (30864580297 / 1000000000000), orderedInterval (-43881801812 / 1000000000000) (-43881793405 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (783353962300991 / 4000000000000) 1 (IntervalRat.scale (307 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (54892755345 / 1000000000000) (54892757521 / 1000000000000), orderedInterval (-15551669887 / 1000000000000) (-15551667712 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (227046510962109 / 800000000000) 1 (IntervalRat.scale (307 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (45530790327 / 1000000000000) (45530794080 / 1000000000000), orderedInterval (-13121623068 / 1000000000000) (-13121619315 / 1000000000000)))) (orderedInterval (-217451737 / 1000000000000) (-217451238 / 1000000000000))) = true
  rfl'

theorem compactCertificate279_chunkChecks1_2 :
    compactCertificate279.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (628022598124423 / 4000000000000) 1 (IntervalRat.scale (307 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (41536575196 / 1000000000000) (41536575197 / 1000000000000), orderedInterval (48132339269 / 1000000000000) (48132339270 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (532381711589903 / 4000000000000) 1 (IntervalRat.scale (307 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (64673181880 / 1000000000000) (64673185938 / 1000000000000), orderedInterval (-24748810407 / 1000000000000) (-24748806349 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (333139755837509 / 4000000000000) 1 (IntervalRat.scale (307 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (59860544064 / 1000000000000) (59860603949 / 1000000000000), orderedInterval (-64082196256 / 1000000000000) (-64082136371 / 1000000000000)))) (orderedInterval (-7789104908 / 1000000000000) (-7789103615 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (179163668662203 / 4000000000000) 1 (IntervalRat.scale (307 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (119190298806 / 1000000000000) (119190298836 / 1000000000000), orderedInterval (-3766119700 / 1000000000000) (-3766119670 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (486464212715609 / 4000000000000) 1 (IntervalRat.scale (307 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (8782639096 / 1000000000000) (8782639132 / 1000000000000), orderedInterval (-71852380627 / 1000000000000) (-71852380590 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (664225293358393 / 4000000000000) 1 (IntervalRat.scale (307 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-20447555968 / 1000000000000) (-20447555967 / 1000000000000), orderedInterval (-58382158595 / 1000000000000) (-58382158594 / 1000000000000)))) (orderedInterval (6152147720 / 1000000000000) (6152147738 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (280860244162491 / 4000000000000) 1 (IntervalRat.scale (307 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (90596383428 / 1000000000000) (90596385096 / 1000000000000), orderedInterval (-29950757705 / 1000000000000) (-29950756036 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1141681299626011 / 4000000000000) 1 (IntervalRat.scale (307 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-14872124810 / 1000000000000) (-14872124809 / 1000000000000), orderedInterval (-44799014732 / 1000000000000) (-44799014731 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (762590197999349 / 4000000000000) 1 (IntervalRat.scale (307 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (11755431889 / 1000000000000) (11755431963 / 1000000000000), orderedInterval (-56608829821 / 1000000000000) (-56608829746 / 1000000000000)))) (orderedInterval (19889892942 / 1000000000000) (19889893025 / 1000000000000))) = true
  rfl'

theorem compactCertificate279_chunkChecks1 :
    compactCertificate279.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate279.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate279_chunkChecks1_0
    compactCertificate279_chunkChecks1_1 compactCertificate279_chunkChecks1_2

theorem compactCertificate279_chunkChecks2_0 :
    compactCertificate279.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (307 / 2) 2 (IntervalRat.scale (307 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-21873346027 / 1000000000000) (-21873346026 / 1000000000000), orderedInterval (-60500475993 / 1000000000000) (-60500475992 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (452269621005607 / 4000000000000) 2 (IntervalRat.scale (307 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (51386414042 / 1000000000000) (51386414043 / 1000000000000), orderedInterval (54452603386 / 1000000000000) (54452603387 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (146254702967431 / 800000000000) 2 (IntervalRat.scale (307 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (58056297418 / 1000000000000) (58056297422 / 1000000000000), orderedInterval (10410360308 / 1000000000000) (10410360312 / 1000000000000)))) (orderedInterval (3726593100 / 1000000000000) (3726593115 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (131971147432949 / 4000000000000) 2 (IntervalRat.scale (307 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (97993947552 / 1000000000000) (97994041072 / 1000000000000), orderedInterval (-99937373817 / 1000000000000) (-99937280297 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (354493065282353 / 4000000000000) 2 (IntervalRat.scale (307 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (84059653853 / 1000000000000) (84059653857 / 1000000000000), orderedInterval (10356385671 / 1000000000000) (10356385676 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (962517630963501 / 4000000000000) 2 (IntervalRat.scale (307 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (24131992124 / 1000000000000) (24131994115 / 1000000000000), orderedInterval (-45473642567 / 1000000000000) (-45473640576 / 1000000000000)))) (orderedInterval (3205907881 / 1000000000000) (3205908309 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (708986130565013 / 4000000000000) 2 (IntervalRat.scale (307 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (51671105490 / 1000000000000) (51671132574 / 1000000000000), orderedInterval (-30507057509 / 1000000000000) (-30507030425 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1214859819004649 / 4000000000000) 2 (IntervalRat.scale (307 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (10640096970 / 1000000000000) (10640097020 / 1000000000000), orderedInterval (-44547284943 / 1000000000000) (-44547284893 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (894860244162491 / 4000000000000) 2 (IntervalRat.scale (307 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-52935357801 / 1000000000000) (-52935357788 / 1000000000000), orderedInterval (-6478159209 / 1000000000000) (-6478159196 / 1000000000000)))) (orderedInterval (3986009645 / 1000000000000) (3986009679 / 1000000000000))) = true
  rfl'

theorem compactCertificate279_chunkChecks2_1 :
    compactCertificate279.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1372945738184693 / 4000000000000) 2 (IntervalRat.scale (307 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-43060576785 / 1000000000000) (-43060576549 / 1000000000000), orderedInterval (797970863 / 1000000000000) (797971099 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (792670591523597 / 4000000000000) 2 (IntervalRat.scale (307 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-48651473275 / 1000000000000) (-48651473274 / 1000000000000), orderedInterval (-28955772360 / 1000000000000) (-28955772359 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1406607874698673 / 4000000000000) 2 (IntervalRat.scale (307 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (23268914327 / 1000000000000) (23268914328 / 1000000000000), orderedInterval (35588919604 / 1000000000000) (35588919605 / 1000000000000)))) (orderedInterval (-49664353823 / 1000000000000) (-49664353341 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1314235536918037 / 4000000000000) 2 (IntervalRat.scale (307 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (21998772556 / 1000000000000) (21998774344 / 1000000000000), orderedInterval (-38160470229 / 1000000000000) (-38160468441 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (937900492234021 / 4000000000000) 2 (IntervalRat.scale (307 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (18329453990 / 1000000000000) (18329454433 / 1000000000000), orderedInterval (-48815312492 / 1000000000000) (-48815312049 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1063479195847059 / 4000000000000) 2 (IntervalRat.scale (307 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (18179859784 / 1000000000000) (18179860258 / 1000000000000), orderedInterval (-45465183489 / 1000000000000) (-45465183015 / 1000000000000)))) (orderedInterval (-1915066477 / 1000000000000) (-1915066174 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (886618080217571 / 4000000000000) 2 (IntervalRat.scale (307 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (30864571890 / 1000000000000) (30864580297 / 1000000000000), orderedInterval (-43881801812 / 1000000000000) (-43881793405 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (783353962300991 / 4000000000000) 2 (IntervalRat.scale (307 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (54892755345 / 1000000000000) (54892757521 / 1000000000000), orderedInterval (-15551669887 / 1000000000000) (-15551667712 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (227046510962109 / 800000000000) 2 (IntervalRat.scale (307 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (45530790327 / 1000000000000) (45530794080 / 1000000000000), orderedInterval (-13121623068 / 1000000000000) (-13121619315 / 1000000000000)))) (orderedInterval (386288795 / 1000000000000) (386289564 / 1000000000000))) = true
  rfl'

theorem compactCertificate279_chunkChecks2_2 :
    compactCertificate279.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (628022598124423 / 4000000000000) 2 (IntervalRat.scale (307 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (41536575196 / 1000000000000) (41536575197 / 1000000000000), orderedInterval (48132339269 / 1000000000000) (48132339270 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (532381711589903 / 4000000000000) 2 (IntervalRat.scale (307 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (64673181880 / 1000000000000) (64673185938 / 1000000000000), orderedInterval (-24748810407 / 1000000000000) (-24748806349 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (333139755837509 / 4000000000000) 2 (IntervalRat.scale (307 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (59860544064 / 1000000000000) (59860603949 / 1000000000000), orderedInterval (-64082196256 / 1000000000000) (-64082136371 / 1000000000000)))) (orderedInterval (9177262261 / 1000000000000) (9177263051 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (179163668662203 / 4000000000000) 2 (IntervalRat.scale (307 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (119190298806 / 1000000000000) (119190298836 / 1000000000000), orderedInterval (-3766119700 / 1000000000000) (-3766119670 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (486464212715609 / 4000000000000) 2 (IntervalRat.scale (307 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (8782639096 / 1000000000000) (8782639132 / 1000000000000), orderedInterval (-71852380627 / 1000000000000) (-71852380590 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (664225293358393 / 4000000000000) 2 (IntervalRat.scale (307 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-20447555968 / 1000000000000) (-20447555967 / 1000000000000), orderedInterval (-58382158595 / 1000000000000) (-58382158594 / 1000000000000)))) (orderedInterval (-1561549367 / 1000000000000) (-1561549349 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (280860244162491 / 4000000000000) 2 (IntervalRat.scale (307 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (90596383428 / 1000000000000) (90596385096 / 1000000000000), orderedInterval (-29950757705 / 1000000000000) (-29950756036 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1141681299626011 / 4000000000000) 2 (IntervalRat.scale (307 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-14872124810 / 1000000000000) (-14872124809 / 1000000000000), orderedInterval (-44799014732 / 1000000000000) (-44799014731 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (762590197999349 / 4000000000000) 2 (IntervalRat.scale (307 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (11755431889 / 1000000000000) (11755431963 / 1000000000000), orderedInterval (-56608829821 / 1000000000000) (-56608829746 / 1000000000000)))) (orderedInterval (-1027125975 / 1000000000000) (-1027125862 / 1000000000000))) = true
  rfl'

theorem compactCertificate279_chunkChecks2 :
    compactCertificate279.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate279.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate279_chunkChecks2_0
    compactCertificate279_chunkChecks2_1 compactCertificate279_chunkChecks2_2

theorem compactCertificate279_chunkChecks3_0 :
    compactCertificate279.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (307 / 2) 3 (IntervalRat.scale (307 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-21873346027 / 1000000000000) (-21873346026 / 1000000000000), orderedInterval (-60500475993 / 1000000000000) (-60500475992 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (452269621005607 / 4000000000000) 3 (IntervalRat.scale (307 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (51386414042 / 1000000000000) (51386414043 / 1000000000000), orderedInterval (54452603386 / 1000000000000) (54452603387 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (146254702967431 / 800000000000) 3 (IntervalRat.scale (307 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (58056297418 / 1000000000000) (58056297422 / 1000000000000), orderedInterval (10410360308 / 1000000000000) (10410360312 / 1000000000000)))) (orderedInterval (22720194161 / 1000000000000) (22720194179 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (131971147432949 / 4000000000000) 3 (IntervalRat.scale (307 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (97993947552 / 1000000000000) (97994041072 / 1000000000000), orderedInterval (-99937373817 / 1000000000000) (-99937280297 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (354493065282353 / 4000000000000) 3 (IntervalRat.scale (307 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (84059653853 / 1000000000000) (84059653857 / 1000000000000), orderedInterval (10356385671 / 1000000000000) (10356385676 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (962517630963501 / 4000000000000) 3 (IntervalRat.scale (307 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (24131992124 / 1000000000000) (24131994115 / 1000000000000), orderedInterval (-45473642567 / 1000000000000) (-45473640576 / 1000000000000)))) (orderedInterval (-12557562478 / 1000000000000) (-12557561876 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (708986130565013 / 4000000000000) 3 (IntervalRat.scale (307 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (51671105490 / 1000000000000) (51671132574 / 1000000000000), orderedInterval (-30507057509 / 1000000000000) (-30507030425 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1214859819004649 / 4000000000000) 3 (IntervalRat.scale (307 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (10640096970 / 1000000000000) (10640097020 / 1000000000000), orderedInterval (-44547284943 / 1000000000000) (-44547284893 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (894860244162491 / 4000000000000) 3 (IntervalRat.scale (307 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-52935357801 / 1000000000000) (-52935357788 / 1000000000000), orderedInterval (-6478159209 / 1000000000000) (-6478159196 / 1000000000000)))) (orderedInterval (-10184215083 / 1000000000000) (-10184215021 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate279_chunkChecks3_1 :
    compactCertificate279.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1372945738184693 / 4000000000000) 3 (IntervalRat.scale (307 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-43060576785 / 1000000000000) (-43060576549 / 1000000000000), orderedInterval (797970863 / 1000000000000) (797971099 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (792670591523597 / 4000000000000) 3 (IntervalRat.scale (307 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-48651473275 / 1000000000000) (-48651473274 / 1000000000000), orderedInterval (-28955772360 / 1000000000000) (-28955772359 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1406607874698673 / 4000000000000) 3 (IntervalRat.scale (307 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (23268914327 / 1000000000000) (23268914328 / 1000000000000), orderedInterval (35588919604 / 1000000000000) (35588919605 / 1000000000000)))) (orderedInterval (-54301323354 / 1000000000000) (-54301322289 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1314235536918037 / 4000000000000) 3 (IntervalRat.scale (307 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (21998772556 / 1000000000000) (21998774344 / 1000000000000), orderedInterval (-38160470229 / 1000000000000) (-38160468441 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (937900492234021 / 4000000000000) 3 (IntervalRat.scale (307 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (18329453990 / 1000000000000) (18329454433 / 1000000000000), orderedInterval (-48815312492 / 1000000000000) (-48815312049 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1063479195847059 / 4000000000000) 3 (IntervalRat.scale (307 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (18179859784 / 1000000000000) (18179860258 / 1000000000000), orderedInterval (-45465183489 / 1000000000000) (-45465183015 / 1000000000000)))) (orderedInterval (8513758278 / 1000000000000) (8513758842 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (886618080217571 / 4000000000000) 3 (IntervalRat.scale (307 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (30864571890 / 1000000000000) (30864580297 / 1000000000000), orderedInterval (-43881801812 / 1000000000000) (-43881793405 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (783353962300991 / 4000000000000) 3 (IntervalRat.scale (307 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (54892755345 / 1000000000000) (54892757521 / 1000000000000), orderedInterval (-15551669887 / 1000000000000) (-15551667712 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (227046510962109 / 800000000000) 3 (IntervalRat.scale (307 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (45530790327 / 1000000000000) (45530794080 / 1000000000000), orderedInterval (-13121623068 / 1000000000000) (-13121619315 / 1000000000000)))) (orderedInterval (1798501461 / 1000000000000) (1798502673 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate279_chunkChecks3_2 :
    compactCertificate279.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (628022598124423 / 4000000000000) 3 (IntervalRat.scale (307 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (41536575196 / 1000000000000) (41536575197 / 1000000000000), orderedInterval (48132339269 / 1000000000000) (48132339270 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (532381711589903 / 4000000000000) 3 (IntervalRat.scale (307 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (64673181880 / 1000000000000) (64673185938 / 1000000000000), orderedInterval (-24748810407 / 1000000000000) (-24748806349 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (333139755837509 / 4000000000000) 3 (IntervalRat.scale (307 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (59860544064 / 1000000000000) (59860603949 / 1000000000000), orderedInterval (-64082196256 / 1000000000000) (-64082136371 / 1000000000000)))) (orderedInterval (7595386658 / 1000000000000) (7595387158 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (179163668662203 / 4000000000000) 3 (IntervalRat.scale (307 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (119190298806 / 1000000000000) (119190298836 / 1000000000000), orderedInterval (-3766119700 / 1000000000000) (-3766119670 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (486464212715609 / 4000000000000) 3 (IntervalRat.scale (307 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (8782639096 / 1000000000000) (8782639132 / 1000000000000), orderedInterval (-71852380627 / 1000000000000) (-71852380590 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (664225293358393 / 4000000000000) 3 (IntervalRat.scale (307 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-20447555968 / 1000000000000) (-20447555967 / 1000000000000), orderedInterval (-58382158595 / 1000000000000) (-58382158594 / 1000000000000)))) (orderedInterval (-6466613770 / 1000000000000) (-6466613752 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (280860244162491 / 4000000000000) 3 (IntervalRat.scale (307 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (90596383428 / 1000000000000) (90596385096 / 1000000000000), orderedInterval (-29950757705 / 1000000000000) (-29950756036 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1141681299626011 / 4000000000000) 3 (IntervalRat.scale (307 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-14872124810 / 1000000000000) (-14872124809 / 1000000000000), orderedInterval (-44799014732 / 1000000000000) (-44799014731 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (762590197999349 / 4000000000000) 3 (IntervalRat.scale (307 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (11755431889 / 1000000000000) (11755431963 / 1000000000000), orderedInterval (-56608829821 / 1000000000000) (-56608829746 / 1000000000000)))) (orderedInterval (-43768375651 / 1000000000000) (-43768375486 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate279_chunkChecks3 :
    compactCertificate279.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate279.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate279_chunkChecks3_0
    compactCertificate279_chunkChecks3_1 compactCertificate279_chunkChecks3_2

theorem compactCertificate279_chunkChecks4_0 :
    compactCertificate279.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (307 / 2) 4 (IntervalRat.scale (307 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-21873346027 / 1000000000000) (-21873346026 / 1000000000000), orderedInterval (-60500475993 / 1000000000000) (-60500475992 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (452269621005607 / 4000000000000) 4 (IntervalRat.scale (307 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (51386414042 / 1000000000000) (51386414043 / 1000000000000), orderedInterval (54452603386 / 1000000000000) (54452603387 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (146254702967431 / 800000000000) 4 (IntervalRat.scale (307 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (58056297418 / 1000000000000) (58056297422 / 1000000000000), orderedInterval (10410360308 / 1000000000000) (10410360312 / 1000000000000)))) (orderedInterval (-1969950729 / 1000000000000) (-1969950709 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (131971147432949 / 4000000000000) 4 (IntervalRat.scale (307 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (97993947552 / 1000000000000) (97994041072 / 1000000000000), orderedInterval (-99937373817 / 1000000000000) (-99937280297 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (354493065282353 / 4000000000000) 4 (IntervalRat.scale (307 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (84059653853 / 1000000000000) (84059653857 / 1000000000000), orderedInterval (10356385671 / 1000000000000) (10356385676 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (962517630963501 / 4000000000000) 4 (IntervalRat.scale (307 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (24131992124 / 1000000000000) (24131994115 / 1000000000000), orderedInterval (-45473642567 / 1000000000000) (-45473640576 / 1000000000000)))) (orderedInterval (-9857525222 / 1000000000000) (-9857524290 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (708986130565013 / 4000000000000) 4 (IntervalRat.scale (307 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (51671105490 / 1000000000000) (51671132574 / 1000000000000), orderedInterval (-30507057509 / 1000000000000) (-30507030425 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1214859819004649 / 4000000000000) 4 (IntervalRat.scale (307 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (10640096970 / 1000000000000) (10640097020 / 1000000000000), orderedInterval (-44547284943 / 1000000000000) (-44547284893 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (894860244162491 / 4000000000000) 4 (IntervalRat.scale (307 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-52935357801 / 1000000000000) (-52935357788 / 1000000000000), orderedInterval (-6478159209 / 1000000000000) (-6478159196 / 1000000000000)))) (orderedInterval (-10669008434 / 1000000000000) (-10669008319 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate279_chunkChecks4_1 :
    compactCertificate279.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1372945738184693 / 4000000000000) 4 (IntervalRat.scale (307 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-43060576785 / 1000000000000) (-43060576549 / 1000000000000), orderedInterval (797970863 / 1000000000000) (797971099 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (792670591523597 / 4000000000000) 4 (IntervalRat.scale (307 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-48651473275 / 1000000000000) (-48651473274 / 1000000000000), orderedInterval (-28955772360 / 1000000000000) (-28955772359 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1406607874698673 / 4000000000000) 4 (IntervalRat.scale (307 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (23268914327 / 1000000000000) (23268914328 / 1000000000000), orderedInterval (35588919604 / 1000000000000) (35588919605 / 1000000000000)))) (orderedInterval (273084692998 / 1000000000000) (273084695372 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1314235536918037 / 4000000000000) 4 (IntervalRat.scale (307 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (21998772556 / 1000000000000) (21998774344 / 1000000000000), orderedInterval (-38160470229 / 1000000000000) (-38160468441 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (937900492234021 / 4000000000000) 4 (IntervalRat.scale (307 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (18329453990 / 1000000000000) (18329454433 / 1000000000000), orderedInterval (-48815312492 / 1000000000000) (-48815312049 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1063479195847059 / 4000000000000) 4 (IntervalRat.scale (307 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (18179859784 / 1000000000000) (18179860258 / 1000000000000), orderedInterval (-45465183489 / 1000000000000) (-45465183015 / 1000000000000)))) (orderedInterval (161542161 / 1000000000000) (161543240 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (886618080217571 / 4000000000000) 4 (IntervalRat.scale (307 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (30864571890 / 1000000000000) (30864580297 / 1000000000000), orderedInterval (-43881801812 / 1000000000000) (-43881793405 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (783353962300991 / 4000000000000) 4 (IntervalRat.scale (307 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (54892755345 / 1000000000000) (54892757521 / 1000000000000), orderedInterval (-15551669887 / 1000000000000) (-15551667712 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (227046510962109 / 800000000000) 4 (IntervalRat.scale (307 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (45530790327 / 1000000000000) (45530794080 / 1000000000000), orderedInterval (-13121623068 / 1000000000000) (-13121619315 / 1000000000000)))) (orderedInterval (6826522503 / 1000000000000) (6826524471 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate279_chunkChecks4_2 :
    compactCertificate279.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (628022598124423 / 4000000000000) 4 (IntervalRat.scale (307 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (41536575196 / 1000000000000) (41536575197 / 1000000000000), orderedInterval (48132339269 / 1000000000000) (48132339270 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (532381711589903 / 4000000000000) 4 (IntervalRat.scale (307 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (64673181880 / 1000000000000) (64673185938 / 1000000000000), orderedInterval (-24748810407 / 1000000000000) (-24748806349 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (333139755837509 / 4000000000000) 4 (IntervalRat.scale (307 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (59860544064 / 1000000000000) (59860603949 / 1000000000000), orderedInterval (-64082196256 / 1000000000000) (-64082136371 / 1000000000000)))) (orderedInterval (-9267872850 / 1000000000000) (-9267872512 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (179163668662203 / 4000000000000) 4 (IntervalRat.scale (307 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (119190298806 / 1000000000000) (119190298836 / 1000000000000), orderedInterval (-3766119700 / 1000000000000) (-3766119670 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (486464212715609 / 4000000000000) 4 (IntervalRat.scale (307 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (8782639096 / 1000000000000) (8782639132 / 1000000000000), orderedInterval (-71852380627 / 1000000000000) (-71852380590 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (664225293358393 / 4000000000000) 4 (IntervalRat.scale (307 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-20447555968 / 1000000000000) (-20447555967 / 1000000000000), orderedInterval (-58382158595 / 1000000000000) (-58382158594 / 1000000000000)))) (orderedInterval (2135962724 / 1000000000000) (2135962743 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (280860244162491 / 4000000000000) 4 (IntervalRat.scale (307 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (90596383428 / 1000000000000) (90596385096 / 1000000000000), orderedInterval (-29950757705 / 1000000000000) (-29950756036 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1141681299626011 / 4000000000000) 4 (IntervalRat.scale (307 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-14872124810 / 1000000000000) (-14872124809 / 1000000000000), orderedInterval (-44799014732 / 1000000000000) (-44799014731 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (762590197999349 / 4000000000000) 4 (IntervalRat.scale (307 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (11755431889 / 1000000000000) (11755431963 / 1000000000000), orderedInterval (-56608829821 / 1000000000000) (-56608829746 / 1000000000000)))) (orderedInterval (9817247136 / 1000000000000) (9817247390 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate279_chunkChecks4 :
    compactCertificate279.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate279.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate279_chunkChecks4_0
    compactCertificate279_chunkChecks4_1 compactCertificate279_chunkChecks4_2

theorem compactCertificate279_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate279.chunkCheck r b = true :=
  compactCertificate279.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate279_chunkChecks0
    · exact compactCertificate279_chunkChecks1
    · exact compactCertificate279_chunkChecks2
    · exact compactCertificate279_chunkChecks3
    · exact compactCertificate279_chunkChecks4)

theorem compactCertificate279_coefficient0 :
    compactCertificate279.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate279_coefficient1 :
    compactCertificate279.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate279_coefficient2 :
    compactCertificate279.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate279_coefficient3 :
    compactCertificate279.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate279_coefficient4 :
    compactCertificate279.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate279_coefficients : ∀ r : Fin 5,
    compactCertificate279.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate279_coefficient0
  · exact compactCertificate279_coefficient1
  · exact compactCertificate279_coefficient2
  · exact compactCertificate279_coefficient3
  · exact compactCertificate279_coefficient4

theorem compactCertificate279_lower : (1 : ℚ) ≤ compactCertificate279.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate279, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate279_proves {t : ℝ} (ht : t ∈ compactCertificate279.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate279.proves compactCertificate279_states compactCertificate279_chunks
    compactCertificate279_coefficients compactCertificate279_lower ht

end Erdos232
