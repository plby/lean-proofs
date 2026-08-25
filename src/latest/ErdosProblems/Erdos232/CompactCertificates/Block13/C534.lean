/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate534 : CompactCertificate where
  left := 405
  right := 406
  center := 811 / 2
  grid := fun i =>
    match i.val with
    | 0 => 129
    | 1 => 95
    | 2 => 154
    | 3 => 28
    | 4 => 75
    | 5 => 202
    | 6 => 149
    | 7 => 256
    | 8 => 188
    | 9 => 289
    | 10 => 167
    | 11 => 296
    | 12 => 276
    | 13 => 197
    | 14 => 224
    | 15 => 186
    | 16 => 165
    | 17 => 239
    | 18 => 132
    | 19 => 112
    | 20 => 70
    | 21 => 38
    | 22 => 102
    | 23 => 140
    | 24 => 59
    | 25 => 240
    | _ => 160
  point := fun i =>
    match i.val with
    | 0 => 811 / 2
    | 1 => 1194757858747711 / 4000000000000
    | 2 => 386360143669663 / 800000000000
    | 3 => 348627363414077 / 4000000000000
    | 4 => 936462136625369 / 4000000000000
    | 5 => 2542676868766773 / 4000000000000
    | 6 => 1872924273251549 / 4000000000000
    | 7 => 3209287665188177 / 4000000000000
    | 8 => 2363946768781043 / 4000000000000
    | 9 => 3626902259504189 / 4000000000000
    | 10 => 2093992995848981 / 4000000000000
    | 11 => 3715827317200729 / 4000000000000
    | 12 => 3471807884171101 / 4000000000000
    | 13 => 2477645925738733 / 4000000000000
    | 14 => 2809386409876107 / 4000000000000
    | 15 => 2342173495297883 / 4000000000000
    | 16 => 2069381314091543 / 4000000000000
    | 17 => 599787362834757 / 800000000000
    | 18 => 1659043410680479 / 4000000000000
    | 19 => 1406389472636519 / 4000000000000
    | 20 => 880053231218957 / 4000000000000
    | 21 => 473295554674419 / 4000000000000
    | 22 => 1285089500040257 / 4000000000000
    | 23 => 1754679846624289 / 4000000000000
    | 24 => 741946768781043 / 4000000000000
    | 25 => 3015972423442003 / 4000000000000
    | _ => 2014529806441277 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-33755334104 / 1000000000000) (-33755334103 / 1000000000000), orderedInterval (-20707819827 / 1000000000000) (-20707819826 / 1000000000000))
    | 1 => (orderedInterval (-39414833061 / 1000000000000) (-39414833060 / 1000000000000), orderedInterval (-23972454182 / 1000000000000) (-23972454181 / 1000000000000))
    | 2 => (orderedInterval (-2537584920 / 1000000000000) (-2537584919 / 1000000000000), orderedInterval (36220726091 / 1000000000000) (36220726092 / 1000000000000))
    | 3 => (orderedInterval (-2032955791 / 1000000000000) (-2032955780 / 1000000000000), orderedInterval (85453383957 / 1000000000000) (85453383968 / 1000000000000))
    | 4 => (orderedInterval (34347299779 / 1000000000000) (34347321830 / 1000000000000), orderedInterval (-39310054709 / 1000000000000) (-39310032657 / 1000000000000))
    | 5 => (orderedInterval (30397211705 / 1000000000000) (30397234761 / 1000000000000), orderedInterval (-8827550908 / 1000000000000) (-8827527852 / 1000000000000))
    | 6 => (orderedInterval (-29311588398 / 1000000000000) (-29311588397 / 1000000000000), orderedInterval (-22339617048 / 1000000000000) (-22339617047 / 1000000000000))
    | 7 => (orderedInterval (-25601585319 / 1000000000000) (-25601512272 / 1000000000000), orderedInterval (11764632469 / 1000000000000) (11764705516 / 1000000000000))
    | 8 => (orderedInterval (29990668693 / 1000000000000) (29990668695 / 1000000000000), orderedInterval (13307840995 / 1000000000000) (13307840998 / 1000000000000))
    | 9 => (orderedInterval (10548756699 / 1000000000000) (10548756706 / 1000000000000), orderedInterval (-24312860290 / 1000000000000) (-24312860283 / 1000000000000))
    | 10 => (orderedInterval (12368329266 / 1000000000000) (12368329330 / 1000000000000), orderedInterval (-32617219595 / 1000000000000) (-32617219532 / 1000000000000))
    | 11 => (orderedInterval (-4411693057 / 1000000000000) (-4411693056 / 1000000000000), orderedInterval (25806311215 / 1000000000000) (25806311216 / 1000000000000))
    | 12 => (orderedInterval (26980615659 / 1000000000000) (26980626619 / 1000000000000), orderedInterval (-2364900904 / 1000000000000) (-2364889944 / 1000000000000))
    | 13 => (orderedInterval (-30915692088 / 1000000000000) (-30915692057 / 1000000000000), orderedInterval (-8460406712 / 1000000000000) (-8460406682 / 1000000000000))
    | 14 => (orderedInterval (-16623230530 / 1000000000000) (-16623230147 / 1000000000000), orderedInterval (25113358602 / 1000000000000) (25113358985 / 1000000000000))
    | 15 => (orderedInterval (30086798501 / 1000000000000) (30086862863 / 1000000000000), orderedInterval (-13516881685 / 1000000000000) (-13516817324 / 1000000000000))
    | 16 => (orderedInterval (8075900363 / 1000000000000) (8075900372 / 1000000000000), orderedInterval (-34144753907 / 1000000000000) (-34144753898 / 1000000000000))
    | 17 => (orderedInterval (9199843235 / 1000000000000) (9199843241 / 1000000000000), orderedInterval (-27655553579 / 1000000000000) (-27655553573 / 1000000000000))
    | 18 => (orderedInterval (29580977103 / 1000000000000) (29580977104 / 1000000000000), orderedInterval (25652346488 / 1000000000000) (25652346489 / 1000000000000))
    | 19 => (orderedInterval (21291877519 / 1000000000000) (21291877520 / 1000000000000), orderedInterval (36811367001 / 1000000000000) (36811367002 / 1000000000000))
    | 20 => (orderedInterval (41686401678 / 1000000000000) (41686401679 / 1000000000000), orderedInterval (33902229253 / 1000000000000) (33902229254 / 1000000000000))
    | 21 => (orderedInterval (-19726694204 / 1000000000000) (-19726693897 / 1000000000000), orderedInterval (70731877741 / 1000000000000) (70731878047 / 1000000000000))
    | 22 => (orderedInterval (44471312448 / 1000000000000) (44471312740 / 1000000000000), orderedInterval (-2033324138 / 1000000000000) (-2033323846 / 1000000000000))
    | 23 => (orderedInterval (-13701098733 / 1000000000000) (-13701098607 / 1000000000000), orderedInterval (35561791766 / 1000000000000) (35561791893 / 1000000000000))
    | 24 => (orderedInterval (-46519282348 / 1000000000000) (-46519282347 / 1000000000000), orderedInterval (-35485161255 / 1000000000000) (-35485161254 / 1000000000000))
    | 25 => (orderedInterval (20765398729 / 1000000000000) (20765398730 / 1000000000000), orderedInterval (20311810580 / 1000000000000) (20311810581 / 1000000000000))
    | _ => (orderedInterval (34900376698 / 1000000000000) (34900381560 / 1000000000000), orderedInterval (-6818400138 / 1000000000000) (-6818395276 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-13895610935 / 1000000000000) (-13895610906 / 1000000000000)
      | 1 => orderedInterval (-884792517 / 1000000000000) (-884790024 / 1000000000000)
      | 2 => orderedInterval (1514468349 / 1000000000000) (1514470626 / 1000000000000)
      | 3 => orderedInterval (-1585143523 / 1000000000000) (-1585143357 / 1000000000000)
      | 4 => orderedInterval (-3326436926 / 1000000000000) (-3326436674 / 1000000000000)
      | 5 => orderedInterval (120827785 / 1000000000000) (120828568 / 1000000000000)
      | 6 => orderedInterval (-4577781944 / 1000000000000) (-4577781842 / 1000000000000)
      | 7 => orderedInterval (405377866 / 1000000000000) (405377937 / 1000000000000)
      | _ => orderedInterval (-8519011288 / 1000000000000) (-8519010264 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-5840955935 / 1000000000000) (-5840955902 / 1000000000000)
      | 1 => orderedInterval (-44176028 / 1000000000000) (-44172938 / 1000000000000)
      | 2 => orderedInterval (-249231508 / 1000000000000) (-249227010 / 1000000000000)
      | 3 => orderedInterval (14944318915 / 1000000000000) (14944319258 / 1000000000000)
      | 4 => orderedInterval (-1350821393 / 1000000000000) (-1350820883 / 1000000000000)
      | 5 => orderedInterval (958350361 / 1000000000000) (958351492 / 1000000000000)
      | 6 => orderedInterval (-5403015542 / 1000000000000) (-5403015447 / 1000000000000)
      | 7 => orderedInterval (-3292915653 / 1000000000000) (-3292915592 / 1000000000000)
      | _ => orderedInterval (-1583331850 / 1000000000000) (-1583330559 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (13804331125 / 1000000000000) (13804331163 / 1000000000000)
      | 1 => orderedInterval (4891383317 / 1000000000000) (4891387698 / 1000000000000)
      | 2 => orderedInterval (-4630346536 / 1000000000000) (-4630337634 / 1000000000000)
      | 3 => orderedInterval (11099151220 / 1000000000000) (11099151948 / 1000000000000)
      | 4 => orderedInterval (8803989510 / 1000000000000) (8803990561 / 1000000000000)
      | 5 => orderedInterval (-779781444 / 1000000000000) (-779779806 / 1000000000000)
      | 6 => orderedInterval (5468113914 / 1000000000000) (5468114004 / 1000000000000)
      | 7 => orderedInterval (-618428863 / 1000000000000) (-618428804 / 1000000000000)
      | _ => orderedInterval (16007942944 / 1000000000000) (16007944587 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (4672259718 / 1000000000000) (4672259761 / 1000000000000)
      | 1 => orderedInterval (-2144143516 / 1000000000000) (-2144136921 / 1000000000000)
      | 2 => orderedInterval (1826512805 / 1000000000000) (1826530407 / 1000000000000)
      | 3 => orderedInterval (-87234371647 / 1000000000000) (-87234370057 / 1000000000000)
      | 4 => orderedInterval (3071496436 / 1000000000000) (3071498619 / 1000000000000)
      | 5 => orderedInterval (889564721 / 1000000000000) (889567094 / 1000000000000)
      | 6 => orderedInterval (5557491955 / 1000000000000) (5557492043 / 1000000000000)
      | 7 => orderedInterval (3461447920 / 1000000000000) (3461447981 / 1000000000000)
      | _ => orderedInterval (8159457725 / 1000000000000) (8159459836 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-13810128041 / 1000000000000) (-13810127991 / 1000000000000)
      | 1 => orderedInterval (-12899740644 / 1000000000000) (-12899730448 / 1000000000000)
      | 2 => orderedInterval (15363454902 / 1000000000000) (15363489756 / 1000000000000)
      | 3 => orderedInterval (-61157652603 / 1000000000000) (-61157649081 / 1000000000000)
      | 4 => orderedInterval (-25398739529 / 1000000000000) (-25398734951 / 1000000000000)
      | 5 => orderedInterval (3034380048 / 1000000000000) (3034383497 / 1000000000000)
      | 6 => orderedInterval (-5767805583 / 1000000000000) (-5767805496 / 1000000000000)
      | 7 => orderedInterval (1026132975 / 1000000000000) (1026133038 / 1000000000000)
      | _ => orderedInterval (-35840153538 / 1000000000000) (-35840150781 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-30748103133 / 1000000000000) (-30748095936 / 1000000000000)
    | 1 => orderedInterval (-1861778633 / 1000000000000) (-1861767581 / 1000000000000)
    | 2 => orderedInterval (54046355187 / 1000000000000) (54046373717 / 1000000000000)
    | 3 => orderedInterval (-61740283883 / 1000000000000) (-61740251237 / 1000000000000)
    | _ => orderedInterval (-135450252013 / 1000000000000) (-135450192457 / 1000000000000)

theorem compactCertificate534_stateChecks0 :
    compactCertificate534.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 129 12 (811 / 2)) (orderedInterval (-33755334104 / 1000000000000) (-33755334103 / 1000000000000), orderedInterval (-20707819827 / 1000000000000) (-20707819826 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 95 12 (1194757858747711 / 4000000000000)) (orderedInterval (-39414833061 / 1000000000000) (-39414833060 / 1000000000000), orderedInterval (-23972454182 / 1000000000000) (-23972454181 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 154 12 (386360143669663 / 800000000000)) (orderedInterval (-2537584920 / 1000000000000) (-2537584919 / 1000000000000), orderedInterval (36220726091 / 1000000000000) (36220726092 / 1000000000000))) = true
  rfl'

theorem compactCertificate534_stateChecks1 :
    compactCertificate534.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 28 12 (348627363414077 / 4000000000000)) (orderedInterval (-2032955791 / 1000000000000) (-2032955780 / 1000000000000), orderedInterval (85453383957 / 1000000000000) (85453383968 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 75 12 (936462136625369 / 4000000000000)) (orderedInterval (34347299779 / 1000000000000) (34347321830 / 1000000000000), orderedInterval (-39310054709 / 1000000000000) (-39310032657 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 202 12 (2542676868766773 / 4000000000000)) (orderedInterval (30397211705 / 1000000000000) (30397234761 / 1000000000000), orderedInterval (-8827550908 / 1000000000000) (-8827527852 / 1000000000000))) = true
  rfl'

theorem compactCertificate534_stateChecks2 :
    compactCertificate534.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 149 12 (1872924273251549 / 4000000000000)) (orderedInterval (-29311588398 / 1000000000000) (-29311588397 / 1000000000000), orderedInterval (-22339617048 / 1000000000000) (-22339617047 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 256 12 (3209287665188177 / 4000000000000)) (orderedInterval (-25601585319 / 1000000000000) (-25601512272 / 1000000000000), orderedInterval (11764632469 / 1000000000000) (11764705516 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 188 12 (2363946768781043 / 4000000000000)) (orderedInterval (29990668693 / 1000000000000) (29990668695 / 1000000000000), orderedInterval (13307840995 / 1000000000000) (13307840998 / 1000000000000))) = true
  rfl'

theorem compactCertificate534_stateChecks3 :
    compactCertificate534.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 289 12 (3626902259504189 / 4000000000000)) (orderedInterval (10548756699 / 1000000000000) (10548756706 / 1000000000000), orderedInterval (-24312860290 / 1000000000000) (-24312860283 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 167 12 (2093992995848981 / 4000000000000)) (orderedInterval (12368329266 / 1000000000000) (12368329330 / 1000000000000), orderedInterval (-32617219595 / 1000000000000) (-32617219532 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 296 12 (3715827317200729 / 4000000000000)) (orderedInterval (-4411693057 / 1000000000000) (-4411693056 / 1000000000000), orderedInterval (25806311215 / 1000000000000) (25806311216 / 1000000000000))) = true
  rfl'

theorem compactCertificate534_stateChecks4 :
    compactCertificate534.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 276 12 (3471807884171101 / 4000000000000)) (orderedInterval (26980615659 / 1000000000000) (26980626619 / 1000000000000), orderedInterval (-2364900904 / 1000000000000) (-2364889944 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 197 12 (2477645925738733 / 4000000000000)) (orderedInterval (-30915692088 / 1000000000000) (-30915692057 / 1000000000000), orderedInterval (-8460406712 / 1000000000000) (-8460406682 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 224 12 (2809386409876107 / 4000000000000)) (orderedInterval (-16623230530 / 1000000000000) (-16623230147 / 1000000000000), orderedInterval (25113358602 / 1000000000000) (25113358985 / 1000000000000))) = true
  rfl'

theorem compactCertificate534_stateChecks5 :
    compactCertificate534.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 186 12 (2342173495297883 / 4000000000000)) (orderedInterval (30086798501 / 1000000000000) (30086862863 / 1000000000000), orderedInterval (-13516881685 / 1000000000000) (-13516817324 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 165 12 (2069381314091543 / 4000000000000)) (orderedInterval (8075900363 / 1000000000000) (8075900372 / 1000000000000), orderedInterval (-34144753907 / 1000000000000) (-34144753898 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 239 12 (599787362834757 / 800000000000)) (orderedInterval (9199843235 / 1000000000000) (9199843241 / 1000000000000), orderedInterval (-27655553579 / 1000000000000) (-27655553573 / 1000000000000))) = true
  rfl'

theorem compactCertificate534_stateChecks6 :
    compactCertificate534.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 132 12 (1659043410680479 / 4000000000000)) (orderedInterval (29580977103 / 1000000000000) (29580977104 / 1000000000000), orderedInterval (25652346488 / 1000000000000) (25652346489 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 112 12 (1406389472636519 / 4000000000000)) (orderedInterval (21291877519 / 1000000000000) (21291877520 / 1000000000000), orderedInterval (36811367001 / 1000000000000) (36811367002 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (880053231218957 / 4000000000000)) (orderedInterval (41686401678 / 1000000000000) (41686401679 / 1000000000000), orderedInterval (33902229253 / 1000000000000) (33902229254 / 1000000000000))) = true
  rfl'

theorem compactCertificate534_stateChecks7 :
    compactCertificate534.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (473295554674419 / 4000000000000)) (orderedInterval (-19726694204 / 1000000000000) (-19726693897 / 1000000000000), orderedInterval (70731877741 / 1000000000000) (70731878047 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 102 12 (1285089500040257 / 4000000000000)) (orderedInterval (44471312448 / 1000000000000) (44471312740 / 1000000000000), orderedInterval (-2033324138 / 1000000000000) (-2033323846 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 140 12 (1754679846624289 / 4000000000000)) (orderedInterval (-13701098733 / 1000000000000) (-13701098607 / 1000000000000), orderedInterval (35561791766 / 1000000000000) (35561791893 / 1000000000000))) = true
  rfl'

theorem compactCertificate534_stateChecks8 :
    compactCertificate534.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 59 12 (741946768781043 / 4000000000000)) (orderedInterval (-46519282348 / 1000000000000) (-46519282347 / 1000000000000), orderedInterval (-35485161255 / 1000000000000) (-35485161254 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 240 12 (3015972423442003 / 4000000000000)) (orderedInterval (20765398729 / 1000000000000) (20765398730 / 1000000000000), orderedInterval (20311810580 / 1000000000000) (20311810581 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 160 12 (2014529806441277 / 4000000000000)) (orderedInterval (34900376698 / 1000000000000) (34900381560 / 1000000000000), orderedInterval (-6818400138 / 1000000000000) (-6818395276 / 1000000000000))) = true
  rfl'

theorem compactCertificate534_states : ∀ j,
    BesselStateValid (compactCertificate534.point j) (compactCertificate534.state j) :=
  compactCertificate534.statesValid_of_checks3 compactCertificate534_stateChecks0
    compactCertificate534_stateChecks1 compactCertificate534_stateChecks2
    compactCertificate534_stateChecks3 compactCertificate534_stateChecks4
    compactCertificate534_stateChecks5 compactCertificate534_stateChecks6
    compactCertificate534_stateChecks7 compactCertificate534_stateChecks8

theorem compactCertificate534_chunkChecks0_0 :
    compactCertificate534.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (811 / 2) 0 (IntervalRat.scale (811 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-33755334104 / 1000000000000) (-33755334103 / 1000000000000), orderedInterval (-20707819827 / 1000000000000) (-20707819826 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1194757858747711 / 4000000000000) 0 (IntervalRat.scale (811 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-39414833061 / 1000000000000) (-39414833060 / 1000000000000), orderedInterval (-23972454182 / 1000000000000) (-23972454181 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (386360143669663 / 800000000000) 0 (IntervalRat.scale (811 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-2537584920 / 1000000000000) (-2537584919 / 1000000000000), orderedInterval (36220726091 / 1000000000000) (36220726092 / 1000000000000)))) (orderedInterval (-13895610935 / 1000000000000) (-13895610906 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (348627363414077 / 4000000000000) 0 (IntervalRat.scale (811 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-2032955791 / 1000000000000) (-2032955780 / 1000000000000), orderedInterval (85453383957 / 1000000000000) (85453383968 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (936462136625369 / 4000000000000) 0 (IntervalRat.scale (811 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (34347299779 / 1000000000000) (34347321830 / 1000000000000), orderedInterval (-39310054709 / 1000000000000) (-39310032657 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2542676868766773 / 4000000000000) 0 (IntervalRat.scale (811 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30397211705 / 1000000000000) (30397234761 / 1000000000000), orderedInterval (-8827550908 / 1000000000000) (-8827527852 / 1000000000000)))) (orderedInterval (-884792517 / 1000000000000) (-884790024 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1872924273251549 / 4000000000000) 0 (IntervalRat.scale (811 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-29311588398 / 1000000000000) (-29311588397 / 1000000000000), orderedInterval (-22339617048 / 1000000000000) (-22339617047 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3209287665188177 / 4000000000000) 0 (IntervalRat.scale (811 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-25601585319 / 1000000000000) (-25601512272 / 1000000000000), orderedInterval (11764632469 / 1000000000000) (11764705516 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2363946768781043 / 4000000000000) 0 (IntervalRat.scale (811 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (29990668693 / 1000000000000) (29990668695 / 1000000000000), orderedInterval (13307840995 / 1000000000000) (13307840998 / 1000000000000)))) (orderedInterval (1514468349 / 1000000000000) (1514470626 / 1000000000000))) = true
  rfl'

theorem compactCertificate534_chunkChecks0_1 :
    compactCertificate534.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3626902259504189 / 4000000000000) 0 (IntervalRat.scale (811 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (10548756699 / 1000000000000) (10548756706 / 1000000000000), orderedInterval (-24312860290 / 1000000000000) (-24312860283 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2093992995848981 / 4000000000000) 0 (IntervalRat.scale (811 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (12368329266 / 1000000000000) (12368329330 / 1000000000000), orderedInterval (-32617219595 / 1000000000000) (-32617219532 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3715827317200729 / 4000000000000) 0 (IntervalRat.scale (811 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-4411693057 / 1000000000000) (-4411693056 / 1000000000000), orderedInterval (25806311215 / 1000000000000) (25806311216 / 1000000000000)))) (orderedInterval (-1585143523 / 1000000000000) (-1585143357 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3471807884171101 / 4000000000000) 0 (IntervalRat.scale (811 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (26980615659 / 1000000000000) (26980626619 / 1000000000000), orderedInterval (-2364900904 / 1000000000000) (-2364889944 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2477645925738733 / 4000000000000) 0 (IntervalRat.scale (811 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-30915692088 / 1000000000000) (-30915692057 / 1000000000000), orderedInterval (-8460406712 / 1000000000000) (-8460406682 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2809386409876107 / 4000000000000) 0 (IntervalRat.scale (811 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-16623230530 / 1000000000000) (-16623230147 / 1000000000000), orderedInterval (25113358602 / 1000000000000) (25113358985 / 1000000000000)))) (orderedInterval (-3326436926 / 1000000000000) (-3326436674 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2342173495297883 / 4000000000000) 0 (IntervalRat.scale (811 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (30086798501 / 1000000000000) (30086862863 / 1000000000000), orderedInterval (-13516881685 / 1000000000000) (-13516817324 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2069381314091543 / 4000000000000) 0 (IntervalRat.scale (811 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (8075900363 / 1000000000000) (8075900372 / 1000000000000), orderedInterval (-34144753907 / 1000000000000) (-34144753898 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (599787362834757 / 800000000000) 0 (IntervalRat.scale (811 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (9199843235 / 1000000000000) (9199843241 / 1000000000000), orderedInterval (-27655553579 / 1000000000000) (-27655553573 / 1000000000000)))) (orderedInterval (120827785 / 1000000000000) (120828568 / 1000000000000))) = true
  rfl'

theorem compactCertificate534_chunkChecks0_2 :
    compactCertificate534.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1659043410680479 / 4000000000000) 0 (IntervalRat.scale (811 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (29580977103 / 1000000000000) (29580977104 / 1000000000000), orderedInterval (25652346488 / 1000000000000) (25652346489 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1406389472636519 / 4000000000000) 0 (IntervalRat.scale (811 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (21291877519 / 1000000000000) (21291877520 / 1000000000000), orderedInterval (36811367001 / 1000000000000) (36811367002 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (880053231218957 / 4000000000000) 0 (IntervalRat.scale (811 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (41686401678 / 1000000000000) (41686401679 / 1000000000000), orderedInterval (33902229253 / 1000000000000) (33902229254 / 1000000000000)))) (orderedInterval (-4577781944 / 1000000000000) (-4577781842 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (473295554674419 / 4000000000000) 0 (IntervalRat.scale (811 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-19726694204 / 1000000000000) (-19726693897 / 1000000000000), orderedInterval (70731877741 / 1000000000000) (70731878047 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1285089500040257 / 4000000000000) 0 (IntervalRat.scale (811 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (44471312448 / 1000000000000) (44471312740 / 1000000000000), orderedInterval (-2033324138 / 1000000000000) (-2033323846 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1754679846624289 / 4000000000000) 0 (IntervalRat.scale (811 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-13701098733 / 1000000000000) (-13701098607 / 1000000000000), orderedInterval (35561791766 / 1000000000000) (35561791893 / 1000000000000)))) (orderedInterval (405377866 / 1000000000000) (405377937 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (741946768781043 / 4000000000000) 0 (IntervalRat.scale (811 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-46519282348 / 1000000000000) (-46519282347 / 1000000000000), orderedInterval (-35485161255 / 1000000000000) (-35485161254 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3015972423442003 / 4000000000000) 0 (IntervalRat.scale (811 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (20765398729 / 1000000000000) (20765398730 / 1000000000000), orderedInterval (20311810580 / 1000000000000) (20311810581 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2014529806441277 / 4000000000000) 0 (IntervalRat.scale (811 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (34900376698 / 1000000000000) (34900381560 / 1000000000000), orderedInterval (-6818400138 / 1000000000000) (-6818395276 / 1000000000000)))) (orderedInterval (-8519011288 / 1000000000000) (-8519010264 / 1000000000000))) = true
  rfl'

theorem compactCertificate534_chunkChecks0 :
    compactCertificate534.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate534.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate534_chunkChecks0_0
    compactCertificate534_chunkChecks0_1 compactCertificate534_chunkChecks0_2

theorem compactCertificate534_chunkChecks1_0 :
    compactCertificate534.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (811 / 2) 1 (IntervalRat.scale (811 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-33755334104 / 1000000000000) (-33755334103 / 1000000000000), orderedInterval (-20707819827 / 1000000000000) (-20707819826 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1194757858747711 / 4000000000000) 1 (IntervalRat.scale (811 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-39414833061 / 1000000000000) (-39414833060 / 1000000000000), orderedInterval (-23972454182 / 1000000000000) (-23972454181 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (386360143669663 / 800000000000) 1 (IntervalRat.scale (811 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-2537584920 / 1000000000000) (-2537584919 / 1000000000000), orderedInterval (36220726091 / 1000000000000) (36220726092 / 1000000000000)))) (orderedInterval (-5840955935 / 1000000000000) (-5840955902 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (348627363414077 / 4000000000000) 1 (IntervalRat.scale (811 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-2032955791 / 1000000000000) (-2032955780 / 1000000000000), orderedInterval (85453383957 / 1000000000000) (85453383968 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (936462136625369 / 4000000000000) 1 (IntervalRat.scale (811 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (34347299779 / 1000000000000) (34347321830 / 1000000000000), orderedInterval (-39310054709 / 1000000000000) (-39310032657 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2542676868766773 / 4000000000000) 1 (IntervalRat.scale (811 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30397211705 / 1000000000000) (30397234761 / 1000000000000), orderedInterval (-8827550908 / 1000000000000) (-8827527852 / 1000000000000)))) (orderedInterval (-44176028 / 1000000000000) (-44172938 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1872924273251549 / 4000000000000) 1 (IntervalRat.scale (811 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-29311588398 / 1000000000000) (-29311588397 / 1000000000000), orderedInterval (-22339617048 / 1000000000000) (-22339617047 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3209287665188177 / 4000000000000) 1 (IntervalRat.scale (811 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-25601585319 / 1000000000000) (-25601512272 / 1000000000000), orderedInterval (11764632469 / 1000000000000) (11764705516 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2363946768781043 / 4000000000000) 1 (IntervalRat.scale (811 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (29990668693 / 1000000000000) (29990668695 / 1000000000000), orderedInterval (13307840995 / 1000000000000) (13307840998 / 1000000000000)))) (orderedInterval (-249231508 / 1000000000000) (-249227010 / 1000000000000))) = true
  rfl'

theorem compactCertificate534_chunkChecks1_1 :
    compactCertificate534.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3626902259504189 / 4000000000000) 1 (IntervalRat.scale (811 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (10548756699 / 1000000000000) (10548756706 / 1000000000000), orderedInterval (-24312860290 / 1000000000000) (-24312860283 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2093992995848981 / 4000000000000) 1 (IntervalRat.scale (811 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (12368329266 / 1000000000000) (12368329330 / 1000000000000), orderedInterval (-32617219595 / 1000000000000) (-32617219532 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3715827317200729 / 4000000000000) 1 (IntervalRat.scale (811 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-4411693057 / 1000000000000) (-4411693056 / 1000000000000), orderedInterval (25806311215 / 1000000000000) (25806311216 / 1000000000000)))) (orderedInterval (14944318915 / 1000000000000) (14944319258 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3471807884171101 / 4000000000000) 1 (IntervalRat.scale (811 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (26980615659 / 1000000000000) (26980626619 / 1000000000000), orderedInterval (-2364900904 / 1000000000000) (-2364889944 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2477645925738733 / 4000000000000) 1 (IntervalRat.scale (811 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-30915692088 / 1000000000000) (-30915692057 / 1000000000000), orderedInterval (-8460406712 / 1000000000000) (-8460406682 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2809386409876107 / 4000000000000) 1 (IntervalRat.scale (811 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-16623230530 / 1000000000000) (-16623230147 / 1000000000000), orderedInterval (25113358602 / 1000000000000) (25113358985 / 1000000000000)))) (orderedInterval (-1350821393 / 1000000000000) (-1350820883 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2342173495297883 / 4000000000000) 1 (IntervalRat.scale (811 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (30086798501 / 1000000000000) (30086862863 / 1000000000000), orderedInterval (-13516881685 / 1000000000000) (-13516817324 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2069381314091543 / 4000000000000) 1 (IntervalRat.scale (811 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (8075900363 / 1000000000000) (8075900372 / 1000000000000), orderedInterval (-34144753907 / 1000000000000) (-34144753898 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (599787362834757 / 800000000000) 1 (IntervalRat.scale (811 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (9199843235 / 1000000000000) (9199843241 / 1000000000000), orderedInterval (-27655553579 / 1000000000000) (-27655553573 / 1000000000000)))) (orderedInterval (958350361 / 1000000000000) (958351492 / 1000000000000))) = true
  rfl'

theorem compactCertificate534_chunkChecks1_2 :
    compactCertificate534.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1659043410680479 / 4000000000000) 1 (IntervalRat.scale (811 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (29580977103 / 1000000000000) (29580977104 / 1000000000000), orderedInterval (25652346488 / 1000000000000) (25652346489 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1406389472636519 / 4000000000000) 1 (IntervalRat.scale (811 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (21291877519 / 1000000000000) (21291877520 / 1000000000000), orderedInterval (36811367001 / 1000000000000) (36811367002 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (880053231218957 / 4000000000000) 1 (IntervalRat.scale (811 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (41686401678 / 1000000000000) (41686401679 / 1000000000000), orderedInterval (33902229253 / 1000000000000) (33902229254 / 1000000000000)))) (orderedInterval (-5403015542 / 1000000000000) (-5403015447 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (473295554674419 / 4000000000000) 1 (IntervalRat.scale (811 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-19726694204 / 1000000000000) (-19726693897 / 1000000000000), orderedInterval (70731877741 / 1000000000000) (70731878047 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1285089500040257 / 4000000000000) 1 (IntervalRat.scale (811 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (44471312448 / 1000000000000) (44471312740 / 1000000000000), orderedInterval (-2033324138 / 1000000000000) (-2033323846 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1754679846624289 / 4000000000000) 1 (IntervalRat.scale (811 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-13701098733 / 1000000000000) (-13701098607 / 1000000000000), orderedInterval (35561791766 / 1000000000000) (35561791893 / 1000000000000)))) (orderedInterval (-3292915653 / 1000000000000) (-3292915592 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (741946768781043 / 4000000000000) 1 (IntervalRat.scale (811 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-46519282348 / 1000000000000) (-46519282347 / 1000000000000), orderedInterval (-35485161255 / 1000000000000) (-35485161254 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3015972423442003 / 4000000000000) 1 (IntervalRat.scale (811 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (20765398729 / 1000000000000) (20765398730 / 1000000000000), orderedInterval (20311810580 / 1000000000000) (20311810581 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2014529806441277 / 4000000000000) 1 (IntervalRat.scale (811 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (34900376698 / 1000000000000) (34900381560 / 1000000000000), orderedInterval (-6818400138 / 1000000000000) (-6818395276 / 1000000000000)))) (orderedInterval (-1583331850 / 1000000000000) (-1583330559 / 1000000000000))) = true
  rfl'

theorem compactCertificate534_chunkChecks1 :
    compactCertificate534.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate534.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate534_chunkChecks1_0
    compactCertificate534_chunkChecks1_1 compactCertificate534_chunkChecks1_2

theorem compactCertificate534_chunkChecks2_0 :
    compactCertificate534.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (811 / 2) 2 (IntervalRat.scale (811 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-33755334104 / 1000000000000) (-33755334103 / 1000000000000), orderedInterval (-20707819827 / 1000000000000) (-20707819826 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1194757858747711 / 4000000000000) 2 (IntervalRat.scale (811 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-39414833061 / 1000000000000) (-39414833060 / 1000000000000), orderedInterval (-23972454182 / 1000000000000) (-23972454181 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (386360143669663 / 800000000000) 2 (IntervalRat.scale (811 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-2537584920 / 1000000000000) (-2537584919 / 1000000000000), orderedInterval (36220726091 / 1000000000000) (36220726092 / 1000000000000)))) (orderedInterval (13804331125 / 1000000000000) (13804331163 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (348627363414077 / 4000000000000) 2 (IntervalRat.scale (811 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-2032955791 / 1000000000000) (-2032955780 / 1000000000000), orderedInterval (85453383957 / 1000000000000) (85453383968 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (936462136625369 / 4000000000000) 2 (IntervalRat.scale (811 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (34347299779 / 1000000000000) (34347321830 / 1000000000000), orderedInterval (-39310054709 / 1000000000000) (-39310032657 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2542676868766773 / 4000000000000) 2 (IntervalRat.scale (811 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30397211705 / 1000000000000) (30397234761 / 1000000000000), orderedInterval (-8827550908 / 1000000000000) (-8827527852 / 1000000000000)))) (orderedInterval (4891383317 / 1000000000000) (4891387698 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1872924273251549 / 4000000000000) 2 (IntervalRat.scale (811 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-29311588398 / 1000000000000) (-29311588397 / 1000000000000), orderedInterval (-22339617048 / 1000000000000) (-22339617047 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3209287665188177 / 4000000000000) 2 (IntervalRat.scale (811 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-25601585319 / 1000000000000) (-25601512272 / 1000000000000), orderedInterval (11764632469 / 1000000000000) (11764705516 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2363946768781043 / 4000000000000) 2 (IntervalRat.scale (811 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (29990668693 / 1000000000000) (29990668695 / 1000000000000), orderedInterval (13307840995 / 1000000000000) (13307840998 / 1000000000000)))) (orderedInterval (-4630346536 / 1000000000000) (-4630337634 / 1000000000000))) = true
  rfl'

theorem compactCertificate534_chunkChecks2_1 :
    compactCertificate534.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3626902259504189 / 4000000000000) 2 (IntervalRat.scale (811 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (10548756699 / 1000000000000) (10548756706 / 1000000000000), orderedInterval (-24312860290 / 1000000000000) (-24312860283 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2093992995848981 / 4000000000000) 2 (IntervalRat.scale (811 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (12368329266 / 1000000000000) (12368329330 / 1000000000000), orderedInterval (-32617219595 / 1000000000000) (-32617219532 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3715827317200729 / 4000000000000) 2 (IntervalRat.scale (811 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-4411693057 / 1000000000000) (-4411693056 / 1000000000000), orderedInterval (25806311215 / 1000000000000) (25806311216 / 1000000000000)))) (orderedInterval (11099151220 / 1000000000000) (11099151948 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3471807884171101 / 4000000000000) 2 (IntervalRat.scale (811 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (26980615659 / 1000000000000) (26980626619 / 1000000000000), orderedInterval (-2364900904 / 1000000000000) (-2364889944 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2477645925738733 / 4000000000000) 2 (IntervalRat.scale (811 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-30915692088 / 1000000000000) (-30915692057 / 1000000000000), orderedInterval (-8460406712 / 1000000000000) (-8460406682 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2809386409876107 / 4000000000000) 2 (IntervalRat.scale (811 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-16623230530 / 1000000000000) (-16623230147 / 1000000000000), orderedInterval (25113358602 / 1000000000000) (25113358985 / 1000000000000)))) (orderedInterval (8803989510 / 1000000000000) (8803990561 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2342173495297883 / 4000000000000) 2 (IntervalRat.scale (811 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (30086798501 / 1000000000000) (30086862863 / 1000000000000), orderedInterval (-13516881685 / 1000000000000) (-13516817324 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2069381314091543 / 4000000000000) 2 (IntervalRat.scale (811 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (8075900363 / 1000000000000) (8075900372 / 1000000000000), orderedInterval (-34144753907 / 1000000000000) (-34144753898 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (599787362834757 / 800000000000) 2 (IntervalRat.scale (811 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (9199843235 / 1000000000000) (9199843241 / 1000000000000), orderedInterval (-27655553579 / 1000000000000) (-27655553573 / 1000000000000)))) (orderedInterval (-779781444 / 1000000000000) (-779779806 / 1000000000000))) = true
  rfl'

theorem compactCertificate534_chunkChecks2_2 :
    compactCertificate534.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1659043410680479 / 4000000000000) 2 (IntervalRat.scale (811 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (29580977103 / 1000000000000) (29580977104 / 1000000000000), orderedInterval (25652346488 / 1000000000000) (25652346489 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1406389472636519 / 4000000000000) 2 (IntervalRat.scale (811 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (21291877519 / 1000000000000) (21291877520 / 1000000000000), orderedInterval (36811367001 / 1000000000000) (36811367002 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (880053231218957 / 4000000000000) 2 (IntervalRat.scale (811 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (41686401678 / 1000000000000) (41686401679 / 1000000000000), orderedInterval (33902229253 / 1000000000000) (33902229254 / 1000000000000)))) (orderedInterval (5468113914 / 1000000000000) (5468114004 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (473295554674419 / 4000000000000) 2 (IntervalRat.scale (811 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-19726694204 / 1000000000000) (-19726693897 / 1000000000000), orderedInterval (70731877741 / 1000000000000) (70731878047 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1285089500040257 / 4000000000000) 2 (IntervalRat.scale (811 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (44471312448 / 1000000000000) (44471312740 / 1000000000000), orderedInterval (-2033324138 / 1000000000000) (-2033323846 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1754679846624289 / 4000000000000) 2 (IntervalRat.scale (811 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-13701098733 / 1000000000000) (-13701098607 / 1000000000000), orderedInterval (35561791766 / 1000000000000) (35561791893 / 1000000000000)))) (orderedInterval (-618428863 / 1000000000000) (-618428804 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (741946768781043 / 4000000000000) 2 (IntervalRat.scale (811 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-46519282348 / 1000000000000) (-46519282347 / 1000000000000), orderedInterval (-35485161255 / 1000000000000) (-35485161254 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3015972423442003 / 4000000000000) 2 (IntervalRat.scale (811 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (20765398729 / 1000000000000) (20765398730 / 1000000000000), orderedInterval (20311810580 / 1000000000000) (20311810581 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2014529806441277 / 4000000000000) 2 (IntervalRat.scale (811 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (34900376698 / 1000000000000) (34900381560 / 1000000000000), orderedInterval (-6818400138 / 1000000000000) (-6818395276 / 1000000000000)))) (orderedInterval (16007942944 / 1000000000000) (16007944587 / 1000000000000))) = true
  rfl'

theorem compactCertificate534_chunkChecks2 :
    compactCertificate534.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate534.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate534_chunkChecks2_0
    compactCertificate534_chunkChecks2_1 compactCertificate534_chunkChecks2_2

theorem compactCertificate534_chunkChecks3_0 :
    compactCertificate534.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (811 / 2) 3 (IntervalRat.scale (811 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-33755334104 / 1000000000000) (-33755334103 / 1000000000000), orderedInterval (-20707819827 / 1000000000000) (-20707819826 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1194757858747711 / 4000000000000) 3 (IntervalRat.scale (811 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-39414833061 / 1000000000000) (-39414833060 / 1000000000000), orderedInterval (-23972454182 / 1000000000000) (-23972454181 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (386360143669663 / 800000000000) 3 (IntervalRat.scale (811 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-2537584920 / 1000000000000) (-2537584919 / 1000000000000), orderedInterval (36220726091 / 1000000000000) (36220726092 / 1000000000000)))) (orderedInterval (4672259718 / 1000000000000) (4672259761 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (348627363414077 / 4000000000000) 3 (IntervalRat.scale (811 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-2032955791 / 1000000000000) (-2032955780 / 1000000000000), orderedInterval (85453383957 / 1000000000000) (85453383968 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (936462136625369 / 4000000000000) 3 (IntervalRat.scale (811 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (34347299779 / 1000000000000) (34347321830 / 1000000000000), orderedInterval (-39310054709 / 1000000000000) (-39310032657 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2542676868766773 / 4000000000000) 3 (IntervalRat.scale (811 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30397211705 / 1000000000000) (30397234761 / 1000000000000), orderedInterval (-8827550908 / 1000000000000) (-8827527852 / 1000000000000)))) (orderedInterval (-2144143516 / 1000000000000) (-2144136921 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1872924273251549 / 4000000000000) 3 (IntervalRat.scale (811 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-29311588398 / 1000000000000) (-29311588397 / 1000000000000), orderedInterval (-22339617048 / 1000000000000) (-22339617047 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3209287665188177 / 4000000000000) 3 (IntervalRat.scale (811 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-25601585319 / 1000000000000) (-25601512272 / 1000000000000), orderedInterval (11764632469 / 1000000000000) (11764705516 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2363946768781043 / 4000000000000) 3 (IntervalRat.scale (811 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (29990668693 / 1000000000000) (29990668695 / 1000000000000), orderedInterval (13307840995 / 1000000000000) (13307840998 / 1000000000000)))) (orderedInterval (1826512805 / 1000000000000) (1826530407 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate534_chunkChecks3_1 :
    compactCertificate534.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3626902259504189 / 4000000000000) 3 (IntervalRat.scale (811 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (10548756699 / 1000000000000) (10548756706 / 1000000000000), orderedInterval (-24312860290 / 1000000000000) (-24312860283 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2093992995848981 / 4000000000000) 3 (IntervalRat.scale (811 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (12368329266 / 1000000000000) (12368329330 / 1000000000000), orderedInterval (-32617219595 / 1000000000000) (-32617219532 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3715827317200729 / 4000000000000) 3 (IntervalRat.scale (811 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-4411693057 / 1000000000000) (-4411693056 / 1000000000000), orderedInterval (25806311215 / 1000000000000) (25806311216 / 1000000000000)))) (orderedInterval (-87234371647 / 1000000000000) (-87234370057 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3471807884171101 / 4000000000000) 3 (IntervalRat.scale (811 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (26980615659 / 1000000000000) (26980626619 / 1000000000000), orderedInterval (-2364900904 / 1000000000000) (-2364889944 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2477645925738733 / 4000000000000) 3 (IntervalRat.scale (811 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-30915692088 / 1000000000000) (-30915692057 / 1000000000000), orderedInterval (-8460406712 / 1000000000000) (-8460406682 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2809386409876107 / 4000000000000) 3 (IntervalRat.scale (811 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-16623230530 / 1000000000000) (-16623230147 / 1000000000000), orderedInterval (25113358602 / 1000000000000) (25113358985 / 1000000000000)))) (orderedInterval (3071496436 / 1000000000000) (3071498619 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2342173495297883 / 4000000000000) 3 (IntervalRat.scale (811 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (30086798501 / 1000000000000) (30086862863 / 1000000000000), orderedInterval (-13516881685 / 1000000000000) (-13516817324 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2069381314091543 / 4000000000000) 3 (IntervalRat.scale (811 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (8075900363 / 1000000000000) (8075900372 / 1000000000000), orderedInterval (-34144753907 / 1000000000000) (-34144753898 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (599787362834757 / 800000000000) 3 (IntervalRat.scale (811 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (9199843235 / 1000000000000) (9199843241 / 1000000000000), orderedInterval (-27655553579 / 1000000000000) (-27655553573 / 1000000000000)))) (orderedInterval (889564721 / 1000000000000) (889567094 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate534_chunkChecks3_2 :
    compactCertificate534.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1659043410680479 / 4000000000000) 3 (IntervalRat.scale (811 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (29580977103 / 1000000000000) (29580977104 / 1000000000000), orderedInterval (25652346488 / 1000000000000) (25652346489 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1406389472636519 / 4000000000000) 3 (IntervalRat.scale (811 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (21291877519 / 1000000000000) (21291877520 / 1000000000000), orderedInterval (36811367001 / 1000000000000) (36811367002 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (880053231218957 / 4000000000000) 3 (IntervalRat.scale (811 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (41686401678 / 1000000000000) (41686401679 / 1000000000000), orderedInterval (33902229253 / 1000000000000) (33902229254 / 1000000000000)))) (orderedInterval (5557491955 / 1000000000000) (5557492043 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (473295554674419 / 4000000000000) 3 (IntervalRat.scale (811 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-19726694204 / 1000000000000) (-19726693897 / 1000000000000), orderedInterval (70731877741 / 1000000000000) (70731878047 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1285089500040257 / 4000000000000) 3 (IntervalRat.scale (811 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (44471312448 / 1000000000000) (44471312740 / 1000000000000), orderedInterval (-2033324138 / 1000000000000) (-2033323846 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1754679846624289 / 4000000000000) 3 (IntervalRat.scale (811 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-13701098733 / 1000000000000) (-13701098607 / 1000000000000), orderedInterval (35561791766 / 1000000000000) (35561791893 / 1000000000000)))) (orderedInterval (3461447920 / 1000000000000) (3461447981 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (741946768781043 / 4000000000000) 3 (IntervalRat.scale (811 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-46519282348 / 1000000000000) (-46519282347 / 1000000000000), orderedInterval (-35485161255 / 1000000000000) (-35485161254 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3015972423442003 / 4000000000000) 3 (IntervalRat.scale (811 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (20765398729 / 1000000000000) (20765398730 / 1000000000000), orderedInterval (20311810580 / 1000000000000) (20311810581 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2014529806441277 / 4000000000000) 3 (IntervalRat.scale (811 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (34900376698 / 1000000000000) (34900381560 / 1000000000000), orderedInterval (-6818400138 / 1000000000000) (-6818395276 / 1000000000000)))) (orderedInterval (8159457725 / 1000000000000) (8159459836 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate534_chunkChecks3 :
    compactCertificate534.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate534.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate534_chunkChecks3_0
    compactCertificate534_chunkChecks3_1 compactCertificate534_chunkChecks3_2

theorem compactCertificate534_chunkChecks4_0 :
    compactCertificate534.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (811 / 2) 4 (IntervalRat.scale (811 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-33755334104 / 1000000000000) (-33755334103 / 1000000000000), orderedInterval (-20707819827 / 1000000000000) (-20707819826 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1194757858747711 / 4000000000000) 4 (IntervalRat.scale (811 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-39414833061 / 1000000000000) (-39414833060 / 1000000000000), orderedInterval (-23972454182 / 1000000000000) (-23972454181 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (386360143669663 / 800000000000) 4 (IntervalRat.scale (811 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-2537584920 / 1000000000000) (-2537584919 / 1000000000000), orderedInterval (36220726091 / 1000000000000) (36220726092 / 1000000000000)))) (orderedInterval (-13810128041 / 1000000000000) (-13810127991 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (348627363414077 / 4000000000000) 4 (IntervalRat.scale (811 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-2032955791 / 1000000000000) (-2032955780 / 1000000000000), orderedInterval (85453383957 / 1000000000000) (85453383968 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (936462136625369 / 4000000000000) 4 (IntervalRat.scale (811 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (34347299779 / 1000000000000) (34347321830 / 1000000000000), orderedInterval (-39310054709 / 1000000000000) (-39310032657 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2542676868766773 / 4000000000000) 4 (IntervalRat.scale (811 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30397211705 / 1000000000000) (30397234761 / 1000000000000), orderedInterval (-8827550908 / 1000000000000) (-8827527852 / 1000000000000)))) (orderedInterval (-12899740644 / 1000000000000) (-12899730448 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1872924273251549 / 4000000000000) 4 (IntervalRat.scale (811 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-29311588398 / 1000000000000) (-29311588397 / 1000000000000), orderedInterval (-22339617048 / 1000000000000) (-22339617047 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3209287665188177 / 4000000000000) 4 (IntervalRat.scale (811 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-25601585319 / 1000000000000) (-25601512272 / 1000000000000), orderedInterval (11764632469 / 1000000000000) (11764705516 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2363946768781043 / 4000000000000) 4 (IntervalRat.scale (811 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (29990668693 / 1000000000000) (29990668695 / 1000000000000), orderedInterval (13307840995 / 1000000000000) (13307840998 / 1000000000000)))) (orderedInterval (15363454902 / 1000000000000) (15363489756 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate534_chunkChecks4_1 :
    compactCertificate534.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3626902259504189 / 4000000000000) 4 (IntervalRat.scale (811 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (10548756699 / 1000000000000) (10548756706 / 1000000000000), orderedInterval (-24312860290 / 1000000000000) (-24312860283 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2093992995848981 / 4000000000000) 4 (IntervalRat.scale (811 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (12368329266 / 1000000000000) (12368329330 / 1000000000000), orderedInterval (-32617219595 / 1000000000000) (-32617219532 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3715827317200729 / 4000000000000) 4 (IntervalRat.scale (811 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-4411693057 / 1000000000000) (-4411693056 / 1000000000000), orderedInterval (25806311215 / 1000000000000) (25806311216 / 1000000000000)))) (orderedInterval (-61157652603 / 1000000000000) (-61157649081 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3471807884171101 / 4000000000000) 4 (IntervalRat.scale (811 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (26980615659 / 1000000000000) (26980626619 / 1000000000000), orderedInterval (-2364900904 / 1000000000000) (-2364889944 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2477645925738733 / 4000000000000) 4 (IntervalRat.scale (811 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-30915692088 / 1000000000000) (-30915692057 / 1000000000000), orderedInterval (-8460406712 / 1000000000000) (-8460406682 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2809386409876107 / 4000000000000) 4 (IntervalRat.scale (811 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-16623230530 / 1000000000000) (-16623230147 / 1000000000000), orderedInterval (25113358602 / 1000000000000) (25113358985 / 1000000000000)))) (orderedInterval (-25398739529 / 1000000000000) (-25398734951 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2342173495297883 / 4000000000000) 4 (IntervalRat.scale (811 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (30086798501 / 1000000000000) (30086862863 / 1000000000000), orderedInterval (-13516881685 / 1000000000000) (-13516817324 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2069381314091543 / 4000000000000) 4 (IntervalRat.scale (811 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (8075900363 / 1000000000000) (8075900372 / 1000000000000), orderedInterval (-34144753907 / 1000000000000) (-34144753898 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (599787362834757 / 800000000000) 4 (IntervalRat.scale (811 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (9199843235 / 1000000000000) (9199843241 / 1000000000000), orderedInterval (-27655553579 / 1000000000000) (-27655553573 / 1000000000000)))) (orderedInterval (3034380048 / 1000000000000) (3034383497 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate534_chunkChecks4_2 :
    compactCertificate534.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1659043410680479 / 4000000000000) 4 (IntervalRat.scale (811 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (29580977103 / 1000000000000) (29580977104 / 1000000000000), orderedInterval (25652346488 / 1000000000000) (25652346489 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1406389472636519 / 4000000000000) 4 (IntervalRat.scale (811 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (21291877519 / 1000000000000) (21291877520 / 1000000000000), orderedInterval (36811367001 / 1000000000000) (36811367002 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (880053231218957 / 4000000000000) 4 (IntervalRat.scale (811 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (41686401678 / 1000000000000) (41686401679 / 1000000000000), orderedInterval (33902229253 / 1000000000000) (33902229254 / 1000000000000)))) (orderedInterval (-5767805583 / 1000000000000) (-5767805496 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (473295554674419 / 4000000000000) 4 (IntervalRat.scale (811 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-19726694204 / 1000000000000) (-19726693897 / 1000000000000), orderedInterval (70731877741 / 1000000000000) (70731878047 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1285089500040257 / 4000000000000) 4 (IntervalRat.scale (811 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (44471312448 / 1000000000000) (44471312740 / 1000000000000), orderedInterval (-2033324138 / 1000000000000) (-2033323846 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1754679846624289 / 4000000000000) 4 (IntervalRat.scale (811 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-13701098733 / 1000000000000) (-13701098607 / 1000000000000), orderedInterval (35561791766 / 1000000000000) (35561791893 / 1000000000000)))) (orderedInterval (1026132975 / 1000000000000) (1026133038 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (741946768781043 / 4000000000000) 4 (IntervalRat.scale (811 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-46519282348 / 1000000000000) (-46519282347 / 1000000000000), orderedInterval (-35485161255 / 1000000000000) (-35485161254 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3015972423442003 / 4000000000000) 4 (IntervalRat.scale (811 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (20765398729 / 1000000000000) (20765398730 / 1000000000000), orderedInterval (20311810580 / 1000000000000) (20311810581 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2014529806441277 / 4000000000000) 4 (IntervalRat.scale (811 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (34900376698 / 1000000000000) (34900381560 / 1000000000000), orderedInterval (-6818400138 / 1000000000000) (-6818395276 / 1000000000000)))) (orderedInterval (-35840153538 / 1000000000000) (-35840150781 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate534_chunkChecks4 :
    compactCertificate534.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate534.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate534_chunkChecks4_0
    compactCertificate534_chunkChecks4_1 compactCertificate534_chunkChecks4_2

theorem compactCertificate534_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate534.chunkCheck r b = true :=
  compactCertificate534.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate534_chunkChecks0
    · exact compactCertificate534_chunkChecks1
    · exact compactCertificate534_chunkChecks2
    · exact compactCertificate534_chunkChecks3
    · exact compactCertificate534_chunkChecks4)

theorem compactCertificate534_coefficient0 :
    compactCertificate534.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate534_coefficient1 :
    compactCertificate534.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate534_coefficient2 :
    compactCertificate534.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate534_coefficient3 :
    compactCertificate534.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate534_coefficient4 :
    compactCertificate534.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate534_coefficients : ∀ r : Fin 5,
    compactCertificate534.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate534_coefficient0
  · exact compactCertificate534_coefficient1
  · exact compactCertificate534_coefficient2
  · exact compactCertificate534_coefficient3
  · exact compactCertificate534_coefficient4

theorem compactCertificate534_lower : (1 : ℚ) ≤ compactCertificate534.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate534, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate534_proves {t : ℝ} (ht : t ∈ compactCertificate534.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate534.proves compactCertificate534_states compactCertificate534_chunks
    compactCertificate534_coefficients compactCertificate534_lower ht

end Erdos232
