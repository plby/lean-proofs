/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate528 : CompactCertificate where
  left := 399
  right := 400
  center := 799 / 2
  grid := fun i =>
    match i.val with
    | 0 => 127
    | 1 => 94
    | 2 => 152
    | 3 => 27
    | 4 => 73
    | 5 => 199
    | 6 => 147
    | 7 => 252
    | 8 => 185
    | 9 => 284
    | 10 => 164
    | 11 => 291
    | 12 => 272
    | 13 => 194
    | 14 => 220
    | 15 => 184
    | 16 => 162
    | 17 => 235
    | 18 => 130
    | 19 => 110
    | 20 => 69
    | 21 => 37
    | 22 => 101
    | 23 => 138
    | 24 => 58
    | 25 => 237
    | _ => 158
  point := fun i =>
    match i.val with
    | 0 => 799 / 2
    | 1 => 1177079567372899 / 4000000000000
    | 2 => 380643347462467 / 800000000000
    | 3 => 343468882081193 / 4000000000000
    | 4 => 922605730164821 / 4000000000000
    | 5 => 2505054029771457 / 4000000000000
    | 6 => 1845211460330441 / 4000000000000
    | 7 => 3161801287898093 / 4000000000000
    | 8 => 2328968518194887 / 4000000000000
    | 9 => 3573236628044201 / 4000000000000
    | 10 => 2063009129079329 / 4000000000000
    | 11 => 3660845901903061 / 4000000000000
    | 12 => 3420437113998409 / 4000000000000
    | 13 => 2440985320179097 / 4000000000000
    | 14 => 2767817190494463 / 4000000000000
    | 15 => 2307517413986447 / 4000000000000
    | 16 => 2038761615239387 / 4000000000000
    | 17 => 590912580647313 / 800000000000
    | 18 => 1634495296095811 / 4000000000000
    | 19 => 1385579764040171 / 4000000000000
    | 20 => 867031481805113 / 4000000000000
    | 21 => 466292414531271 / 4000000000000
    | 22 => 1266074612246813 / 4000000000000
    | 23 => 1728716642975101 / 4000000000000
    | 24 => 730968518194887 / 4000000000000
    | 25 => 2971346444303527 / 4000000000000
    | _ => 1984721720525993 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-38494384321 / 1000000000000) (-38494384315 / 1000000000000), orderedInterval (-10521715939 / 1000000000000) (-10521715934 / 1000000000000))
    | 1 => (orderedInterval (-11725475582 / 1000000000000) (-11725475510 / 1000000000000), orderedInterval (45029958849 / 1000000000000) (45029958921 / 1000000000000))
    | 2 => (orderedInterval (-29382395407 / 1000000000000) (-29382344804 / 1000000000000), orderedInterval (21817612330 / 1000000000000) (21817662933 / 1000000000000))
    | 3 => (orderedInterval (-83267955553 / 1000000000000) (-83267954600 / 1000000000000), orderedInterval (22401521589 / 1000000000000) (22401522543 / 1000000000000))
    | 4 => (orderedInterval (-45349385895 / 1000000000000) (-45349351871 / 1000000000000), orderedInterval (26622355500 / 1000000000000) (26622389524 / 1000000000000))
    | 5 => (orderedInterval (-30449995529 / 1000000000000) (-30449969192 / 1000000000000), orderedInterval (9476010456 / 1000000000000) (9476036792 / 1000000000000))
    | 6 => (orderedInterval (-10047362035 / 1000000000000) (-10047362034 / 1000000000000), orderedInterval (-35753596469 / 1000000000000) (-35753596468 / 1000000000000))
    | 7 => (orderedInterval (-12236270892 / 1000000000000) (-12236270863 / 1000000000000), orderedInterval (25613647476 / 1000000000000) (25613647506 / 1000000000000))
    | 8 => (orderedInterval (-31939135146 / 1000000000000) (-31939120419 / 1000000000000), orderedInterval (8588102164 / 1000000000000) (8588116891 / 1000000000000))
    | 9 => (orderedInterval (25412383445 / 1000000000000) (25412478504 / 1000000000000), orderedInterval (-8191162786 / 1000000000000) (-8191067726 / 1000000000000))
    | 10 => (orderedInterval (34001193066 / 1000000000000) (34001193082 / 1000000000000), orderedInterval (8814081499 / 1000000000000) (8814081516 / 1000000000000))
    | 11 => (orderedInterval (-25724194009 / 1000000000000) (-25724145306 / 1000000000000), orderedInterval (5833437843 / 1000000000000) (5833486545 / 1000000000000))
    | 12 => (orderedInterval (26797049236 / 1000000000000) (26797049704 / 1000000000000), orderedInterval (5123143712 / 1000000000000) (5123144180 / 1000000000000))
    | 13 => (orderedInterval (32297776302 / 1000000000000) (32297777246 / 1000000000000), orderedInterval (239926774 / 1000000000000) (239927717 / 1000000000000))
    | 14 => (orderedInterval (30326918273 / 1000000000000) (30326920348 / 1000000000000), orderedInterval (-578022195 / 1000000000000) (-578020119 / 1000000000000))
    | 15 => (orderedInterval (-12584102970 / 1000000000000) (-12584102907 / 1000000000000), orderedInterval (30754988659 / 1000000000000) (30754988722 / 1000000000000))
    | 16 => (orderedInterval (35322108446 / 1000000000000) (35322108814 / 1000000000000), orderedInterval (1140224648 / 1000000000000) (1140225016 / 1000000000000))
    | 17 => (orderedInterval (-26816856730 / 1000000000000) (-26816856722 / 1000000000000), orderedInterval (-11929072937 / 1000000000000) (-11929072930 / 1000000000000))
    | 18 => (orderedInterval (33253545735 / 1000000000000) (33253545736 / 1000000000000), orderedInterval (21223404409 / 1000000000000) (21223404410 / 1000000000000))
    | 19 => (orderedInterval (42845295167 / 1000000000000) (42845295469 / 1000000000000), orderedInterval (-1518722806 / 1000000000000) (-1518722504 / 1000000000000))
    | 20 => (orderedInterval (-37835171356 / 1000000000000) (-37835171355 / 1000000000000), orderedInterval (-38713611889 / 1000000000000) (-38713611888 / 1000000000000))
    | 21 => (orderedInterval (-66468246587 / 1000000000000) (-66468246586 / 1000000000000), orderedInterval (-32011378593 / 1000000000000) (-32011378592 / 1000000000000))
    | 22 => (orderedInterval (-125496838 / 1000000000000) (-125496836 / 1000000000000), orderedInterval (-44847378074 / 1000000000000) (-44847378072 / 1000000000000))
    | 23 => (orderedInterval (-20889159474 / 1000000000000) (-20889157692 / 1000000000000), orderedInterval (32221828134 / 1000000000000) (32221829916 / 1000000000000))
    | 24 => (orderedInterval (57094410247 / 1000000000000) (57094410248 / 1000000000000), orderedInterval (14807826060 / 1000000000000) (14807826062 / 1000000000000))
    | 25 => (orderedInterval (23565175898 / 1000000000000) (23565190806 / 1000000000000), orderedInterval (-17385207167 / 1000000000000) (-17385192259 / 1000000000000))
    | _ => (orderedInterval (20045630832 / 1000000000000) (20045630833 / 1000000000000), orderedInterval (29665045592 / 1000000000000) (29665045593 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-17091277529 / 1000000000000) (-17091274529 / 1000000000000)
      | 1 => orderedInterval (1412290366 / 1000000000000) (1412293539 / 1000000000000)
      | 2 => orderedInterval (-394490341 / 1000000000000) (-394489962 / 1000000000000)
      | 3 => orderedInterval (-5653127814 / 1000000000000) (-5653103840 / 1000000000000)
      | 4 => orderedInterval (2416929140 / 1000000000000) (2416929297 / 1000000000000)
      | 5 => orderedInterval (-2853301459 / 1000000000000) (-2853301398 / 1000000000000)
      | 6 => orderedInterval (-8973766778 / 1000000000000) (-8973766661 / 1000000000000)
      | 7 => orderedInterval (2831112496 / 1000000000000) (2831112681 / 1000000000000)
      | _ => orderedInterval (-5335156725 / 1000000000000) (-5335155401 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-2336555133 / 1000000000000) (-2336551562 / 1000000000000)
      | 1 => orderedInterval (-547060375 / 1000000000000) (-547056666 / 1000000000000)
      | 2 => orderedInterval (-1260647520 / 1000000000000) (-1260646960 / 1000000000000)
      | 3 => orderedInterval (5997318411 / 1000000000000) (5997372370 / 1000000000000)
      | 4 => orderedInterval (-158243878 / 1000000000000) (-158243628 / 1000000000000)
      | 5 => orderedInterval (-135129448 / 1000000000000) (-135129364 / 1000000000000)
      | 6 => orderedInterval (-4080251186 / 1000000000000) (-4080251078 / 1000000000000)
      | 7 => orderedInterval (-1692856441 / 1000000000000) (-1692856250 / 1000000000000)
      | _ => orderedInterval (-4240678013 / 1000000000000) (-4240675600 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (17768682627 / 1000000000000) (17768686887 / 1000000000000)
      | 1 => orderedInterval (-4807979157 / 1000000000000) (-4807974057 / 1000000000000)
      | 2 => orderedInterval (165228383 / 1000000000000) (165229214 / 1000000000000)
      | 3 => orderedInterval (37555450952 / 1000000000000) (37555572581 / 1000000000000)
      | 4 => orderedInterval (-4449186727 / 1000000000000) (-4449186320 / 1000000000000)
      | 5 => orderedInterval (5940749561 / 1000000000000) (5940749681 / 1000000000000)
      | 6 => orderedInterval (7758618372 / 1000000000000) (7758618474 / 1000000000000)
      | 7 => orderedInterval (-1975597968 / 1000000000000) (-1975597765 / 1000000000000)
      | _ => orderedInterval (12372556526 / 1000000000000) (12372560957 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (1795331520 / 1000000000000) (1795336591 / 1000000000000)
      | 1 => orderedInterval (2422469906 / 1000000000000) (2422477484 / 1000000000000)
      | 2 => orderedInterval (5476533383 / 1000000000000) (5476534620 / 1000000000000)
      | 3 => orderedInterval (-27742042692 / 1000000000000) (-27741768760 / 1000000000000)
      | 4 => orderedInterval (822060334 / 1000000000000) (822061007 / 1000000000000)
      | 5 => orderedInterval (981767525 / 1000000000000) (981767699 / 1000000000000)
      | 6 => orderedInterval (3757138829 / 1000000000000) (3757138926 / 1000000000000)
      | 7 => orderedInterval (2610608736 / 1000000000000) (2610608954 / 1000000000000)
      | _ => orderedInterval (1526211480 / 1000000000000) (1526219646 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-18768085448 / 1000000000000) (-18768079397 / 1000000000000)
      | 1 => orderedInterval (12878168278 / 1000000000000) (12878179934 / 1000000000000)
      | 2 => orderedInterval (2274221088 / 1000000000000) (2274222946 / 1000000000000)
      | 3 => orderedInterval (-206472577743 / 1000000000000) (-206471959991 / 1000000000000)
      | 4 => orderedInterval (5088389815 / 1000000000000) (5088390951 / 1000000000000)
      | 5 => orderedInterval (-14016050594 / 1000000000000) (-14016050331 / 1000000000000)
      | 6 => orderedInterval (-7315797759 / 1000000000000) (-7315797664 / 1000000000000)
      | 7 => orderedInterval (2189531863 / 1000000000000) (2189532098 / 1000000000000)
      | _ => orderedInterval (-31872492317 / 1000000000000) (-31872477203 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-33640788644 / 1000000000000) (-33640756274 / 1000000000000)
    | 1 => orderedInterval (-8454103583 / 1000000000000) (-8454038738 / 1000000000000)
    | 2 => orderedInterval (70328522569 / 1000000000000) (70328659652 / 1000000000000)
    | 3 => orderedInterval (-8349920979 / 1000000000000) (-8349623833 / 1000000000000)
    | _ => orderedInterval (-256014692817 / 1000000000000) (-256014038657 / 1000000000000)

theorem compactCertificate528_stateChecks0 :
    compactCertificate528.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 127 12 (799 / 2)) (orderedInterval (-38494384321 / 1000000000000) (-38494384315 / 1000000000000), orderedInterval (-10521715939 / 1000000000000) (-10521715934 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 94 12 (1177079567372899 / 4000000000000)) (orderedInterval (-11725475582 / 1000000000000) (-11725475510 / 1000000000000), orderedInterval (45029958849 / 1000000000000) (45029958921 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 152 12 (380643347462467 / 800000000000)) (orderedInterval (-29382395407 / 1000000000000) (-29382344804 / 1000000000000), orderedInterval (21817612330 / 1000000000000) (21817662933 / 1000000000000))) = true
  rfl'

theorem compactCertificate528_stateChecks1 :
    compactCertificate528.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 27 12 (343468882081193 / 4000000000000)) (orderedInterval (-83267955553 / 1000000000000) (-83267954600 / 1000000000000), orderedInterval (22401521589 / 1000000000000) (22401522543 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 73 12 (922605730164821 / 4000000000000)) (orderedInterval (-45349385895 / 1000000000000) (-45349351871 / 1000000000000), orderedInterval (26622355500 / 1000000000000) (26622389524 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 199 12 (2505054029771457 / 4000000000000)) (orderedInterval (-30449995529 / 1000000000000) (-30449969192 / 1000000000000), orderedInterval (9476010456 / 1000000000000) (9476036792 / 1000000000000))) = true
  rfl'

theorem compactCertificate528_stateChecks2 :
    compactCertificate528.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 147 12 (1845211460330441 / 4000000000000)) (orderedInterval (-10047362035 / 1000000000000) (-10047362034 / 1000000000000), orderedInterval (-35753596469 / 1000000000000) (-35753596468 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 252 12 (3161801287898093 / 4000000000000)) (orderedInterval (-12236270892 / 1000000000000) (-12236270863 / 1000000000000), orderedInterval (25613647476 / 1000000000000) (25613647506 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 185 12 (2328968518194887 / 4000000000000)) (orderedInterval (-31939135146 / 1000000000000) (-31939120419 / 1000000000000), orderedInterval (8588102164 / 1000000000000) (8588116891 / 1000000000000))) = true
  rfl'

theorem compactCertificate528_stateChecks3 :
    compactCertificate528.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 284 12 (3573236628044201 / 4000000000000)) (orderedInterval (25412383445 / 1000000000000) (25412478504 / 1000000000000), orderedInterval (-8191162786 / 1000000000000) (-8191067726 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 164 12 (2063009129079329 / 4000000000000)) (orderedInterval (34001193066 / 1000000000000) (34001193082 / 1000000000000), orderedInterval (8814081499 / 1000000000000) (8814081516 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 291 12 (3660845901903061 / 4000000000000)) (orderedInterval (-25724194009 / 1000000000000) (-25724145306 / 1000000000000), orderedInterval (5833437843 / 1000000000000) (5833486545 / 1000000000000))) = true
  rfl'

theorem compactCertificate528_stateChecks4 :
    compactCertificate528.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 272 12 (3420437113998409 / 4000000000000)) (orderedInterval (26797049236 / 1000000000000) (26797049704 / 1000000000000), orderedInterval (5123143712 / 1000000000000) (5123144180 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 194 12 (2440985320179097 / 4000000000000)) (orderedInterval (32297776302 / 1000000000000) (32297777246 / 1000000000000), orderedInterval (239926774 / 1000000000000) (239927717 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 220 12 (2767817190494463 / 4000000000000)) (orderedInterval (30326918273 / 1000000000000) (30326920348 / 1000000000000), orderedInterval (-578022195 / 1000000000000) (-578020119 / 1000000000000))) = true
  rfl'

theorem compactCertificate528_stateChecks5 :
    compactCertificate528.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 184 12 (2307517413986447 / 4000000000000)) (orderedInterval (-12584102970 / 1000000000000) (-12584102907 / 1000000000000), orderedInterval (30754988659 / 1000000000000) (30754988722 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 162 12 (2038761615239387 / 4000000000000)) (orderedInterval (35322108446 / 1000000000000) (35322108814 / 1000000000000), orderedInterval (1140224648 / 1000000000000) (1140225016 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 235 12 (590912580647313 / 800000000000)) (orderedInterval (-26816856730 / 1000000000000) (-26816856722 / 1000000000000), orderedInterval (-11929072937 / 1000000000000) (-11929072930 / 1000000000000))) = true
  rfl'

theorem compactCertificate528_stateChecks6 :
    compactCertificate528.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 130 12 (1634495296095811 / 4000000000000)) (orderedInterval (33253545735 / 1000000000000) (33253545736 / 1000000000000), orderedInterval (21223404409 / 1000000000000) (21223404410 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 110 12 (1385579764040171 / 4000000000000)) (orderedInterval (42845295167 / 1000000000000) (42845295469 / 1000000000000), orderedInterval (-1518722806 / 1000000000000) (-1518722504 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (867031481805113 / 4000000000000)) (orderedInterval (-37835171356 / 1000000000000) (-37835171355 / 1000000000000), orderedInterval (-38713611889 / 1000000000000) (-38713611888 / 1000000000000))) = true
  rfl'

theorem compactCertificate528_stateChecks7 :
    compactCertificate528.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (466292414531271 / 4000000000000)) (orderedInterval (-66468246587 / 1000000000000) (-66468246586 / 1000000000000), orderedInterval (-32011378593 / 1000000000000) (-32011378592 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 101 12 (1266074612246813 / 4000000000000)) (orderedInterval (-125496838 / 1000000000000) (-125496836 / 1000000000000), orderedInterval (-44847378074 / 1000000000000) (-44847378072 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 138 12 (1728716642975101 / 4000000000000)) (orderedInterval (-20889159474 / 1000000000000) (-20889157692 / 1000000000000), orderedInterval (32221828134 / 1000000000000) (32221829916 / 1000000000000))) = true
  rfl'

theorem compactCertificate528_stateChecks8 :
    compactCertificate528.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (730968518194887 / 4000000000000)) (orderedInterval (57094410247 / 1000000000000) (57094410248 / 1000000000000), orderedInterval (14807826060 / 1000000000000) (14807826062 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 237 12 (2971346444303527 / 4000000000000)) (orderedInterval (23565175898 / 1000000000000) (23565190806 / 1000000000000), orderedInterval (-17385207167 / 1000000000000) (-17385192259 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 158 12 (1984721720525993 / 4000000000000)) (orderedInterval (20045630832 / 1000000000000) (20045630833 / 1000000000000), orderedInterval (29665045592 / 1000000000000) (29665045593 / 1000000000000))) = true
  rfl'

theorem compactCertificate528_states : ∀ j,
    BesselStateValid (compactCertificate528.point j) (compactCertificate528.state j) :=
  compactCertificate528.statesValid_of_checks3 compactCertificate528_stateChecks0
    compactCertificate528_stateChecks1 compactCertificate528_stateChecks2
    compactCertificate528_stateChecks3 compactCertificate528_stateChecks4
    compactCertificate528_stateChecks5 compactCertificate528_stateChecks6
    compactCertificate528_stateChecks7 compactCertificate528_stateChecks8

theorem compactCertificate528_chunkChecks0_0 :
    compactCertificate528.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (799 / 2) 0 (IntervalRat.scale (799 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-38494384321 / 1000000000000) (-38494384315 / 1000000000000), orderedInterval (-10521715939 / 1000000000000) (-10521715934 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1177079567372899 / 4000000000000) 0 (IntervalRat.scale (799 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-11725475582 / 1000000000000) (-11725475510 / 1000000000000), orderedInterval (45029958849 / 1000000000000) (45029958921 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (380643347462467 / 800000000000) 0 (IntervalRat.scale (799 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-29382395407 / 1000000000000) (-29382344804 / 1000000000000), orderedInterval (21817612330 / 1000000000000) (21817662933 / 1000000000000)))) (orderedInterval (-17091277529 / 1000000000000) (-17091274529 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (343468882081193 / 4000000000000) 0 (IntervalRat.scale (799 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-83267955553 / 1000000000000) (-83267954600 / 1000000000000), orderedInterval (22401521589 / 1000000000000) (22401522543 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (922605730164821 / 4000000000000) 0 (IntervalRat.scale (799 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-45349385895 / 1000000000000) (-45349351871 / 1000000000000), orderedInterval (26622355500 / 1000000000000) (26622389524 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2505054029771457 / 4000000000000) 0 (IntervalRat.scale (799 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30449995529 / 1000000000000) (-30449969192 / 1000000000000), orderedInterval (9476010456 / 1000000000000) (9476036792 / 1000000000000)))) (orderedInterval (1412290366 / 1000000000000) (1412293539 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1845211460330441 / 4000000000000) 0 (IntervalRat.scale (799 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-10047362035 / 1000000000000) (-10047362034 / 1000000000000), orderedInterval (-35753596469 / 1000000000000) (-35753596468 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3161801287898093 / 4000000000000) 0 (IntervalRat.scale (799 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-12236270892 / 1000000000000) (-12236270863 / 1000000000000), orderedInterval (25613647476 / 1000000000000) (25613647506 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2328968518194887 / 4000000000000) 0 (IntervalRat.scale (799 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-31939135146 / 1000000000000) (-31939120419 / 1000000000000), orderedInterval (8588102164 / 1000000000000) (8588116891 / 1000000000000)))) (orderedInterval (-394490341 / 1000000000000) (-394489962 / 1000000000000))) = true
  rfl'

theorem compactCertificate528_chunkChecks0_1 :
    compactCertificate528.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3573236628044201 / 4000000000000) 0 (IntervalRat.scale (799 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (25412383445 / 1000000000000) (25412478504 / 1000000000000), orderedInterval (-8191162786 / 1000000000000) (-8191067726 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2063009129079329 / 4000000000000) 0 (IntervalRat.scale (799 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (34001193066 / 1000000000000) (34001193082 / 1000000000000), orderedInterval (8814081499 / 1000000000000) (8814081516 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3660845901903061 / 4000000000000) 0 (IntervalRat.scale (799 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-25724194009 / 1000000000000) (-25724145306 / 1000000000000), orderedInterval (5833437843 / 1000000000000) (5833486545 / 1000000000000)))) (orderedInterval (-5653127814 / 1000000000000) (-5653103840 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3420437113998409 / 4000000000000) 0 (IntervalRat.scale (799 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (26797049236 / 1000000000000) (26797049704 / 1000000000000), orderedInterval (5123143712 / 1000000000000) (5123144180 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2440985320179097 / 4000000000000) 0 (IntervalRat.scale (799 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (32297776302 / 1000000000000) (32297777246 / 1000000000000), orderedInterval (239926774 / 1000000000000) (239927717 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2767817190494463 / 4000000000000) 0 (IntervalRat.scale (799 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (30326918273 / 1000000000000) (30326920348 / 1000000000000), orderedInterval (-578022195 / 1000000000000) (-578020119 / 1000000000000)))) (orderedInterval (2416929140 / 1000000000000) (2416929297 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2307517413986447 / 4000000000000) 0 (IntervalRat.scale (799 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-12584102970 / 1000000000000) (-12584102907 / 1000000000000), orderedInterval (30754988659 / 1000000000000) (30754988722 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2038761615239387 / 4000000000000) 0 (IntervalRat.scale (799 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (35322108446 / 1000000000000) (35322108814 / 1000000000000), orderedInterval (1140224648 / 1000000000000) (1140225016 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (590912580647313 / 800000000000) 0 (IntervalRat.scale (799 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-26816856730 / 1000000000000) (-26816856722 / 1000000000000), orderedInterval (-11929072937 / 1000000000000) (-11929072930 / 1000000000000)))) (orderedInterval (-2853301459 / 1000000000000) (-2853301398 / 1000000000000))) = true
  rfl'

theorem compactCertificate528_chunkChecks0_2 :
    compactCertificate528.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1634495296095811 / 4000000000000) 0 (IntervalRat.scale (799 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (33253545735 / 1000000000000) (33253545736 / 1000000000000), orderedInterval (21223404409 / 1000000000000) (21223404410 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1385579764040171 / 4000000000000) 0 (IntervalRat.scale (799 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (42845295167 / 1000000000000) (42845295469 / 1000000000000), orderedInterval (-1518722806 / 1000000000000) (-1518722504 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (867031481805113 / 4000000000000) 0 (IntervalRat.scale (799 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-37835171356 / 1000000000000) (-37835171355 / 1000000000000), orderedInterval (-38713611889 / 1000000000000) (-38713611888 / 1000000000000)))) (orderedInterval (-8973766778 / 1000000000000) (-8973766661 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (466292414531271 / 4000000000000) 0 (IntervalRat.scale (799 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-66468246587 / 1000000000000) (-66468246586 / 1000000000000), orderedInterval (-32011378593 / 1000000000000) (-32011378592 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1266074612246813 / 4000000000000) 0 (IntervalRat.scale (799 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-125496838 / 1000000000000) (-125496836 / 1000000000000), orderedInterval (-44847378074 / 1000000000000) (-44847378072 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1728716642975101 / 4000000000000) 0 (IntervalRat.scale (799 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-20889159474 / 1000000000000) (-20889157692 / 1000000000000), orderedInterval (32221828134 / 1000000000000) (32221829916 / 1000000000000)))) (orderedInterval (2831112496 / 1000000000000) (2831112681 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (730968518194887 / 4000000000000) 0 (IntervalRat.scale (799 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (57094410247 / 1000000000000) (57094410248 / 1000000000000), orderedInterval (14807826060 / 1000000000000) (14807826062 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2971346444303527 / 4000000000000) 0 (IntervalRat.scale (799 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (23565175898 / 1000000000000) (23565190806 / 1000000000000), orderedInterval (-17385207167 / 1000000000000) (-17385192259 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1984721720525993 / 4000000000000) 0 (IntervalRat.scale (799 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (20045630832 / 1000000000000) (20045630833 / 1000000000000), orderedInterval (29665045592 / 1000000000000) (29665045593 / 1000000000000)))) (orderedInterval (-5335156725 / 1000000000000) (-5335155401 / 1000000000000))) = true
  rfl'

theorem compactCertificate528_chunkChecks0 :
    compactCertificate528.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate528.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate528_chunkChecks0_0
    compactCertificate528_chunkChecks0_1 compactCertificate528_chunkChecks0_2

theorem compactCertificate528_chunkChecks1_0 :
    compactCertificate528.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (799 / 2) 1 (IntervalRat.scale (799 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-38494384321 / 1000000000000) (-38494384315 / 1000000000000), orderedInterval (-10521715939 / 1000000000000) (-10521715934 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1177079567372899 / 4000000000000) 1 (IntervalRat.scale (799 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-11725475582 / 1000000000000) (-11725475510 / 1000000000000), orderedInterval (45029958849 / 1000000000000) (45029958921 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (380643347462467 / 800000000000) 1 (IntervalRat.scale (799 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-29382395407 / 1000000000000) (-29382344804 / 1000000000000), orderedInterval (21817612330 / 1000000000000) (21817662933 / 1000000000000)))) (orderedInterval (-2336555133 / 1000000000000) (-2336551562 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (343468882081193 / 4000000000000) 1 (IntervalRat.scale (799 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-83267955553 / 1000000000000) (-83267954600 / 1000000000000), orderedInterval (22401521589 / 1000000000000) (22401522543 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (922605730164821 / 4000000000000) 1 (IntervalRat.scale (799 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-45349385895 / 1000000000000) (-45349351871 / 1000000000000), orderedInterval (26622355500 / 1000000000000) (26622389524 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2505054029771457 / 4000000000000) 1 (IntervalRat.scale (799 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30449995529 / 1000000000000) (-30449969192 / 1000000000000), orderedInterval (9476010456 / 1000000000000) (9476036792 / 1000000000000)))) (orderedInterval (-547060375 / 1000000000000) (-547056666 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1845211460330441 / 4000000000000) 1 (IntervalRat.scale (799 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-10047362035 / 1000000000000) (-10047362034 / 1000000000000), orderedInterval (-35753596469 / 1000000000000) (-35753596468 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3161801287898093 / 4000000000000) 1 (IntervalRat.scale (799 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-12236270892 / 1000000000000) (-12236270863 / 1000000000000), orderedInterval (25613647476 / 1000000000000) (25613647506 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2328968518194887 / 4000000000000) 1 (IntervalRat.scale (799 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-31939135146 / 1000000000000) (-31939120419 / 1000000000000), orderedInterval (8588102164 / 1000000000000) (8588116891 / 1000000000000)))) (orderedInterval (-1260647520 / 1000000000000) (-1260646960 / 1000000000000))) = true
  rfl'

theorem compactCertificate528_chunkChecks1_1 :
    compactCertificate528.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3573236628044201 / 4000000000000) 1 (IntervalRat.scale (799 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (25412383445 / 1000000000000) (25412478504 / 1000000000000), orderedInterval (-8191162786 / 1000000000000) (-8191067726 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2063009129079329 / 4000000000000) 1 (IntervalRat.scale (799 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (34001193066 / 1000000000000) (34001193082 / 1000000000000), orderedInterval (8814081499 / 1000000000000) (8814081516 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3660845901903061 / 4000000000000) 1 (IntervalRat.scale (799 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-25724194009 / 1000000000000) (-25724145306 / 1000000000000), orderedInterval (5833437843 / 1000000000000) (5833486545 / 1000000000000)))) (orderedInterval (5997318411 / 1000000000000) (5997372370 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3420437113998409 / 4000000000000) 1 (IntervalRat.scale (799 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (26797049236 / 1000000000000) (26797049704 / 1000000000000), orderedInterval (5123143712 / 1000000000000) (5123144180 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2440985320179097 / 4000000000000) 1 (IntervalRat.scale (799 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (32297776302 / 1000000000000) (32297777246 / 1000000000000), orderedInterval (239926774 / 1000000000000) (239927717 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2767817190494463 / 4000000000000) 1 (IntervalRat.scale (799 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (30326918273 / 1000000000000) (30326920348 / 1000000000000), orderedInterval (-578022195 / 1000000000000) (-578020119 / 1000000000000)))) (orderedInterval (-158243878 / 1000000000000) (-158243628 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2307517413986447 / 4000000000000) 1 (IntervalRat.scale (799 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-12584102970 / 1000000000000) (-12584102907 / 1000000000000), orderedInterval (30754988659 / 1000000000000) (30754988722 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2038761615239387 / 4000000000000) 1 (IntervalRat.scale (799 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (35322108446 / 1000000000000) (35322108814 / 1000000000000), orderedInterval (1140224648 / 1000000000000) (1140225016 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (590912580647313 / 800000000000) 1 (IntervalRat.scale (799 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-26816856730 / 1000000000000) (-26816856722 / 1000000000000), orderedInterval (-11929072937 / 1000000000000) (-11929072930 / 1000000000000)))) (orderedInterval (-135129448 / 1000000000000) (-135129364 / 1000000000000))) = true
  rfl'

theorem compactCertificate528_chunkChecks1_2 :
    compactCertificate528.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1634495296095811 / 4000000000000) 1 (IntervalRat.scale (799 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (33253545735 / 1000000000000) (33253545736 / 1000000000000), orderedInterval (21223404409 / 1000000000000) (21223404410 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1385579764040171 / 4000000000000) 1 (IntervalRat.scale (799 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (42845295167 / 1000000000000) (42845295469 / 1000000000000), orderedInterval (-1518722806 / 1000000000000) (-1518722504 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (867031481805113 / 4000000000000) 1 (IntervalRat.scale (799 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-37835171356 / 1000000000000) (-37835171355 / 1000000000000), orderedInterval (-38713611889 / 1000000000000) (-38713611888 / 1000000000000)))) (orderedInterval (-4080251186 / 1000000000000) (-4080251078 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (466292414531271 / 4000000000000) 1 (IntervalRat.scale (799 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-66468246587 / 1000000000000) (-66468246586 / 1000000000000), orderedInterval (-32011378593 / 1000000000000) (-32011378592 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1266074612246813 / 4000000000000) 1 (IntervalRat.scale (799 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-125496838 / 1000000000000) (-125496836 / 1000000000000), orderedInterval (-44847378074 / 1000000000000) (-44847378072 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1728716642975101 / 4000000000000) 1 (IntervalRat.scale (799 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-20889159474 / 1000000000000) (-20889157692 / 1000000000000), orderedInterval (32221828134 / 1000000000000) (32221829916 / 1000000000000)))) (orderedInterval (-1692856441 / 1000000000000) (-1692856250 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (730968518194887 / 4000000000000) 1 (IntervalRat.scale (799 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (57094410247 / 1000000000000) (57094410248 / 1000000000000), orderedInterval (14807826060 / 1000000000000) (14807826062 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2971346444303527 / 4000000000000) 1 (IntervalRat.scale (799 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (23565175898 / 1000000000000) (23565190806 / 1000000000000), orderedInterval (-17385207167 / 1000000000000) (-17385192259 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1984721720525993 / 4000000000000) 1 (IntervalRat.scale (799 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (20045630832 / 1000000000000) (20045630833 / 1000000000000), orderedInterval (29665045592 / 1000000000000) (29665045593 / 1000000000000)))) (orderedInterval (-4240678013 / 1000000000000) (-4240675600 / 1000000000000))) = true
  rfl'

theorem compactCertificate528_chunkChecks1 :
    compactCertificate528.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate528.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate528_chunkChecks1_0
    compactCertificate528_chunkChecks1_1 compactCertificate528_chunkChecks1_2

theorem compactCertificate528_chunkChecks2_0 :
    compactCertificate528.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (799 / 2) 2 (IntervalRat.scale (799 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-38494384321 / 1000000000000) (-38494384315 / 1000000000000), orderedInterval (-10521715939 / 1000000000000) (-10521715934 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1177079567372899 / 4000000000000) 2 (IntervalRat.scale (799 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-11725475582 / 1000000000000) (-11725475510 / 1000000000000), orderedInterval (45029958849 / 1000000000000) (45029958921 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (380643347462467 / 800000000000) 2 (IntervalRat.scale (799 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-29382395407 / 1000000000000) (-29382344804 / 1000000000000), orderedInterval (21817612330 / 1000000000000) (21817662933 / 1000000000000)))) (orderedInterval (17768682627 / 1000000000000) (17768686887 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (343468882081193 / 4000000000000) 2 (IntervalRat.scale (799 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-83267955553 / 1000000000000) (-83267954600 / 1000000000000), orderedInterval (22401521589 / 1000000000000) (22401522543 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (922605730164821 / 4000000000000) 2 (IntervalRat.scale (799 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-45349385895 / 1000000000000) (-45349351871 / 1000000000000), orderedInterval (26622355500 / 1000000000000) (26622389524 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2505054029771457 / 4000000000000) 2 (IntervalRat.scale (799 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30449995529 / 1000000000000) (-30449969192 / 1000000000000), orderedInterval (9476010456 / 1000000000000) (9476036792 / 1000000000000)))) (orderedInterval (-4807979157 / 1000000000000) (-4807974057 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1845211460330441 / 4000000000000) 2 (IntervalRat.scale (799 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-10047362035 / 1000000000000) (-10047362034 / 1000000000000), orderedInterval (-35753596469 / 1000000000000) (-35753596468 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3161801287898093 / 4000000000000) 2 (IntervalRat.scale (799 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-12236270892 / 1000000000000) (-12236270863 / 1000000000000), orderedInterval (25613647476 / 1000000000000) (25613647506 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2328968518194887 / 4000000000000) 2 (IntervalRat.scale (799 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-31939135146 / 1000000000000) (-31939120419 / 1000000000000), orderedInterval (8588102164 / 1000000000000) (8588116891 / 1000000000000)))) (orderedInterval (165228383 / 1000000000000) (165229214 / 1000000000000))) = true
  rfl'

theorem compactCertificate528_chunkChecks2_1 :
    compactCertificate528.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3573236628044201 / 4000000000000) 2 (IntervalRat.scale (799 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (25412383445 / 1000000000000) (25412478504 / 1000000000000), orderedInterval (-8191162786 / 1000000000000) (-8191067726 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2063009129079329 / 4000000000000) 2 (IntervalRat.scale (799 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (34001193066 / 1000000000000) (34001193082 / 1000000000000), orderedInterval (8814081499 / 1000000000000) (8814081516 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3660845901903061 / 4000000000000) 2 (IntervalRat.scale (799 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-25724194009 / 1000000000000) (-25724145306 / 1000000000000), orderedInterval (5833437843 / 1000000000000) (5833486545 / 1000000000000)))) (orderedInterval (37555450952 / 1000000000000) (37555572581 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3420437113998409 / 4000000000000) 2 (IntervalRat.scale (799 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (26797049236 / 1000000000000) (26797049704 / 1000000000000), orderedInterval (5123143712 / 1000000000000) (5123144180 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2440985320179097 / 4000000000000) 2 (IntervalRat.scale (799 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (32297776302 / 1000000000000) (32297777246 / 1000000000000), orderedInterval (239926774 / 1000000000000) (239927717 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2767817190494463 / 4000000000000) 2 (IntervalRat.scale (799 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (30326918273 / 1000000000000) (30326920348 / 1000000000000), orderedInterval (-578022195 / 1000000000000) (-578020119 / 1000000000000)))) (orderedInterval (-4449186727 / 1000000000000) (-4449186320 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2307517413986447 / 4000000000000) 2 (IntervalRat.scale (799 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-12584102970 / 1000000000000) (-12584102907 / 1000000000000), orderedInterval (30754988659 / 1000000000000) (30754988722 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2038761615239387 / 4000000000000) 2 (IntervalRat.scale (799 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (35322108446 / 1000000000000) (35322108814 / 1000000000000), orderedInterval (1140224648 / 1000000000000) (1140225016 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (590912580647313 / 800000000000) 2 (IntervalRat.scale (799 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-26816856730 / 1000000000000) (-26816856722 / 1000000000000), orderedInterval (-11929072937 / 1000000000000) (-11929072930 / 1000000000000)))) (orderedInterval (5940749561 / 1000000000000) (5940749681 / 1000000000000))) = true
  rfl'

theorem compactCertificate528_chunkChecks2_2 :
    compactCertificate528.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1634495296095811 / 4000000000000) 2 (IntervalRat.scale (799 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (33253545735 / 1000000000000) (33253545736 / 1000000000000), orderedInterval (21223404409 / 1000000000000) (21223404410 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1385579764040171 / 4000000000000) 2 (IntervalRat.scale (799 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (42845295167 / 1000000000000) (42845295469 / 1000000000000), orderedInterval (-1518722806 / 1000000000000) (-1518722504 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (867031481805113 / 4000000000000) 2 (IntervalRat.scale (799 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-37835171356 / 1000000000000) (-37835171355 / 1000000000000), orderedInterval (-38713611889 / 1000000000000) (-38713611888 / 1000000000000)))) (orderedInterval (7758618372 / 1000000000000) (7758618474 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (466292414531271 / 4000000000000) 2 (IntervalRat.scale (799 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-66468246587 / 1000000000000) (-66468246586 / 1000000000000), orderedInterval (-32011378593 / 1000000000000) (-32011378592 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1266074612246813 / 4000000000000) 2 (IntervalRat.scale (799 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-125496838 / 1000000000000) (-125496836 / 1000000000000), orderedInterval (-44847378074 / 1000000000000) (-44847378072 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1728716642975101 / 4000000000000) 2 (IntervalRat.scale (799 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-20889159474 / 1000000000000) (-20889157692 / 1000000000000), orderedInterval (32221828134 / 1000000000000) (32221829916 / 1000000000000)))) (orderedInterval (-1975597968 / 1000000000000) (-1975597765 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (730968518194887 / 4000000000000) 2 (IntervalRat.scale (799 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (57094410247 / 1000000000000) (57094410248 / 1000000000000), orderedInterval (14807826060 / 1000000000000) (14807826062 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2971346444303527 / 4000000000000) 2 (IntervalRat.scale (799 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (23565175898 / 1000000000000) (23565190806 / 1000000000000), orderedInterval (-17385207167 / 1000000000000) (-17385192259 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1984721720525993 / 4000000000000) 2 (IntervalRat.scale (799 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (20045630832 / 1000000000000) (20045630833 / 1000000000000), orderedInterval (29665045592 / 1000000000000) (29665045593 / 1000000000000)))) (orderedInterval (12372556526 / 1000000000000) (12372560957 / 1000000000000))) = true
  rfl'

theorem compactCertificate528_chunkChecks2 :
    compactCertificate528.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate528.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate528_chunkChecks2_0
    compactCertificate528_chunkChecks2_1 compactCertificate528_chunkChecks2_2

theorem compactCertificate528_chunkChecks3_0 :
    compactCertificate528.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (799 / 2) 3 (IntervalRat.scale (799 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-38494384321 / 1000000000000) (-38494384315 / 1000000000000), orderedInterval (-10521715939 / 1000000000000) (-10521715934 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1177079567372899 / 4000000000000) 3 (IntervalRat.scale (799 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-11725475582 / 1000000000000) (-11725475510 / 1000000000000), orderedInterval (45029958849 / 1000000000000) (45029958921 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (380643347462467 / 800000000000) 3 (IntervalRat.scale (799 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-29382395407 / 1000000000000) (-29382344804 / 1000000000000), orderedInterval (21817612330 / 1000000000000) (21817662933 / 1000000000000)))) (orderedInterval (1795331520 / 1000000000000) (1795336591 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (343468882081193 / 4000000000000) 3 (IntervalRat.scale (799 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-83267955553 / 1000000000000) (-83267954600 / 1000000000000), orderedInterval (22401521589 / 1000000000000) (22401522543 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (922605730164821 / 4000000000000) 3 (IntervalRat.scale (799 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-45349385895 / 1000000000000) (-45349351871 / 1000000000000), orderedInterval (26622355500 / 1000000000000) (26622389524 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2505054029771457 / 4000000000000) 3 (IntervalRat.scale (799 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30449995529 / 1000000000000) (-30449969192 / 1000000000000), orderedInterval (9476010456 / 1000000000000) (9476036792 / 1000000000000)))) (orderedInterval (2422469906 / 1000000000000) (2422477484 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1845211460330441 / 4000000000000) 3 (IntervalRat.scale (799 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-10047362035 / 1000000000000) (-10047362034 / 1000000000000), orderedInterval (-35753596469 / 1000000000000) (-35753596468 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3161801287898093 / 4000000000000) 3 (IntervalRat.scale (799 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-12236270892 / 1000000000000) (-12236270863 / 1000000000000), orderedInterval (25613647476 / 1000000000000) (25613647506 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2328968518194887 / 4000000000000) 3 (IntervalRat.scale (799 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-31939135146 / 1000000000000) (-31939120419 / 1000000000000), orderedInterval (8588102164 / 1000000000000) (8588116891 / 1000000000000)))) (orderedInterval (5476533383 / 1000000000000) (5476534620 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate528_chunkChecks3_1 :
    compactCertificate528.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3573236628044201 / 4000000000000) 3 (IntervalRat.scale (799 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (25412383445 / 1000000000000) (25412478504 / 1000000000000), orderedInterval (-8191162786 / 1000000000000) (-8191067726 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2063009129079329 / 4000000000000) 3 (IntervalRat.scale (799 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (34001193066 / 1000000000000) (34001193082 / 1000000000000), orderedInterval (8814081499 / 1000000000000) (8814081516 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3660845901903061 / 4000000000000) 3 (IntervalRat.scale (799 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-25724194009 / 1000000000000) (-25724145306 / 1000000000000), orderedInterval (5833437843 / 1000000000000) (5833486545 / 1000000000000)))) (orderedInterval (-27742042692 / 1000000000000) (-27741768760 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3420437113998409 / 4000000000000) 3 (IntervalRat.scale (799 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (26797049236 / 1000000000000) (26797049704 / 1000000000000), orderedInterval (5123143712 / 1000000000000) (5123144180 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2440985320179097 / 4000000000000) 3 (IntervalRat.scale (799 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (32297776302 / 1000000000000) (32297777246 / 1000000000000), orderedInterval (239926774 / 1000000000000) (239927717 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2767817190494463 / 4000000000000) 3 (IntervalRat.scale (799 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (30326918273 / 1000000000000) (30326920348 / 1000000000000), orderedInterval (-578022195 / 1000000000000) (-578020119 / 1000000000000)))) (orderedInterval (822060334 / 1000000000000) (822061007 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2307517413986447 / 4000000000000) 3 (IntervalRat.scale (799 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-12584102970 / 1000000000000) (-12584102907 / 1000000000000), orderedInterval (30754988659 / 1000000000000) (30754988722 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2038761615239387 / 4000000000000) 3 (IntervalRat.scale (799 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (35322108446 / 1000000000000) (35322108814 / 1000000000000), orderedInterval (1140224648 / 1000000000000) (1140225016 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (590912580647313 / 800000000000) 3 (IntervalRat.scale (799 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-26816856730 / 1000000000000) (-26816856722 / 1000000000000), orderedInterval (-11929072937 / 1000000000000) (-11929072930 / 1000000000000)))) (orderedInterval (981767525 / 1000000000000) (981767699 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate528_chunkChecks3_2 :
    compactCertificate528.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1634495296095811 / 4000000000000) 3 (IntervalRat.scale (799 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (33253545735 / 1000000000000) (33253545736 / 1000000000000), orderedInterval (21223404409 / 1000000000000) (21223404410 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1385579764040171 / 4000000000000) 3 (IntervalRat.scale (799 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (42845295167 / 1000000000000) (42845295469 / 1000000000000), orderedInterval (-1518722806 / 1000000000000) (-1518722504 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (867031481805113 / 4000000000000) 3 (IntervalRat.scale (799 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-37835171356 / 1000000000000) (-37835171355 / 1000000000000), orderedInterval (-38713611889 / 1000000000000) (-38713611888 / 1000000000000)))) (orderedInterval (3757138829 / 1000000000000) (3757138926 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (466292414531271 / 4000000000000) 3 (IntervalRat.scale (799 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-66468246587 / 1000000000000) (-66468246586 / 1000000000000), orderedInterval (-32011378593 / 1000000000000) (-32011378592 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1266074612246813 / 4000000000000) 3 (IntervalRat.scale (799 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-125496838 / 1000000000000) (-125496836 / 1000000000000), orderedInterval (-44847378074 / 1000000000000) (-44847378072 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1728716642975101 / 4000000000000) 3 (IntervalRat.scale (799 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-20889159474 / 1000000000000) (-20889157692 / 1000000000000), orderedInterval (32221828134 / 1000000000000) (32221829916 / 1000000000000)))) (orderedInterval (2610608736 / 1000000000000) (2610608954 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (730968518194887 / 4000000000000) 3 (IntervalRat.scale (799 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (57094410247 / 1000000000000) (57094410248 / 1000000000000), orderedInterval (14807826060 / 1000000000000) (14807826062 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2971346444303527 / 4000000000000) 3 (IntervalRat.scale (799 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (23565175898 / 1000000000000) (23565190806 / 1000000000000), orderedInterval (-17385207167 / 1000000000000) (-17385192259 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1984721720525993 / 4000000000000) 3 (IntervalRat.scale (799 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (20045630832 / 1000000000000) (20045630833 / 1000000000000), orderedInterval (29665045592 / 1000000000000) (29665045593 / 1000000000000)))) (orderedInterval (1526211480 / 1000000000000) (1526219646 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate528_chunkChecks3 :
    compactCertificate528.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate528.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate528_chunkChecks3_0
    compactCertificate528_chunkChecks3_1 compactCertificate528_chunkChecks3_2

theorem compactCertificate528_chunkChecks4_0 :
    compactCertificate528.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (799 / 2) 4 (IntervalRat.scale (799 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-38494384321 / 1000000000000) (-38494384315 / 1000000000000), orderedInterval (-10521715939 / 1000000000000) (-10521715934 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1177079567372899 / 4000000000000) 4 (IntervalRat.scale (799 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-11725475582 / 1000000000000) (-11725475510 / 1000000000000), orderedInterval (45029958849 / 1000000000000) (45029958921 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (380643347462467 / 800000000000) 4 (IntervalRat.scale (799 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-29382395407 / 1000000000000) (-29382344804 / 1000000000000), orderedInterval (21817612330 / 1000000000000) (21817662933 / 1000000000000)))) (orderedInterval (-18768085448 / 1000000000000) (-18768079397 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (343468882081193 / 4000000000000) 4 (IntervalRat.scale (799 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-83267955553 / 1000000000000) (-83267954600 / 1000000000000), orderedInterval (22401521589 / 1000000000000) (22401522543 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (922605730164821 / 4000000000000) 4 (IntervalRat.scale (799 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-45349385895 / 1000000000000) (-45349351871 / 1000000000000), orderedInterval (26622355500 / 1000000000000) (26622389524 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2505054029771457 / 4000000000000) 4 (IntervalRat.scale (799 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30449995529 / 1000000000000) (-30449969192 / 1000000000000), orderedInterval (9476010456 / 1000000000000) (9476036792 / 1000000000000)))) (orderedInterval (12878168278 / 1000000000000) (12878179934 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1845211460330441 / 4000000000000) 4 (IntervalRat.scale (799 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-10047362035 / 1000000000000) (-10047362034 / 1000000000000), orderedInterval (-35753596469 / 1000000000000) (-35753596468 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3161801287898093 / 4000000000000) 4 (IntervalRat.scale (799 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-12236270892 / 1000000000000) (-12236270863 / 1000000000000), orderedInterval (25613647476 / 1000000000000) (25613647506 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2328968518194887 / 4000000000000) 4 (IntervalRat.scale (799 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-31939135146 / 1000000000000) (-31939120419 / 1000000000000), orderedInterval (8588102164 / 1000000000000) (8588116891 / 1000000000000)))) (orderedInterval (2274221088 / 1000000000000) (2274222946 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate528_chunkChecks4_1 :
    compactCertificate528.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3573236628044201 / 4000000000000) 4 (IntervalRat.scale (799 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (25412383445 / 1000000000000) (25412478504 / 1000000000000), orderedInterval (-8191162786 / 1000000000000) (-8191067726 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2063009129079329 / 4000000000000) 4 (IntervalRat.scale (799 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (34001193066 / 1000000000000) (34001193082 / 1000000000000), orderedInterval (8814081499 / 1000000000000) (8814081516 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3660845901903061 / 4000000000000) 4 (IntervalRat.scale (799 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-25724194009 / 1000000000000) (-25724145306 / 1000000000000), orderedInterval (5833437843 / 1000000000000) (5833486545 / 1000000000000)))) (orderedInterval (-206472577743 / 1000000000000) (-206471959991 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3420437113998409 / 4000000000000) 4 (IntervalRat.scale (799 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (26797049236 / 1000000000000) (26797049704 / 1000000000000), orderedInterval (5123143712 / 1000000000000) (5123144180 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2440985320179097 / 4000000000000) 4 (IntervalRat.scale (799 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (32297776302 / 1000000000000) (32297777246 / 1000000000000), orderedInterval (239926774 / 1000000000000) (239927717 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2767817190494463 / 4000000000000) 4 (IntervalRat.scale (799 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (30326918273 / 1000000000000) (30326920348 / 1000000000000), orderedInterval (-578022195 / 1000000000000) (-578020119 / 1000000000000)))) (orderedInterval (5088389815 / 1000000000000) (5088390951 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2307517413986447 / 4000000000000) 4 (IntervalRat.scale (799 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-12584102970 / 1000000000000) (-12584102907 / 1000000000000), orderedInterval (30754988659 / 1000000000000) (30754988722 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2038761615239387 / 4000000000000) 4 (IntervalRat.scale (799 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (35322108446 / 1000000000000) (35322108814 / 1000000000000), orderedInterval (1140224648 / 1000000000000) (1140225016 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (590912580647313 / 800000000000) 4 (IntervalRat.scale (799 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-26816856730 / 1000000000000) (-26816856722 / 1000000000000), orderedInterval (-11929072937 / 1000000000000) (-11929072930 / 1000000000000)))) (orderedInterval (-14016050594 / 1000000000000) (-14016050331 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate528_chunkChecks4_2 :
    compactCertificate528.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1634495296095811 / 4000000000000) 4 (IntervalRat.scale (799 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (33253545735 / 1000000000000) (33253545736 / 1000000000000), orderedInterval (21223404409 / 1000000000000) (21223404410 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1385579764040171 / 4000000000000) 4 (IntervalRat.scale (799 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (42845295167 / 1000000000000) (42845295469 / 1000000000000), orderedInterval (-1518722806 / 1000000000000) (-1518722504 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (867031481805113 / 4000000000000) 4 (IntervalRat.scale (799 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-37835171356 / 1000000000000) (-37835171355 / 1000000000000), orderedInterval (-38713611889 / 1000000000000) (-38713611888 / 1000000000000)))) (orderedInterval (-7315797759 / 1000000000000) (-7315797664 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (466292414531271 / 4000000000000) 4 (IntervalRat.scale (799 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-66468246587 / 1000000000000) (-66468246586 / 1000000000000), orderedInterval (-32011378593 / 1000000000000) (-32011378592 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1266074612246813 / 4000000000000) 4 (IntervalRat.scale (799 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-125496838 / 1000000000000) (-125496836 / 1000000000000), orderedInterval (-44847378074 / 1000000000000) (-44847378072 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1728716642975101 / 4000000000000) 4 (IntervalRat.scale (799 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-20889159474 / 1000000000000) (-20889157692 / 1000000000000), orderedInterval (32221828134 / 1000000000000) (32221829916 / 1000000000000)))) (orderedInterval (2189531863 / 1000000000000) (2189532098 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (730968518194887 / 4000000000000) 4 (IntervalRat.scale (799 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (57094410247 / 1000000000000) (57094410248 / 1000000000000), orderedInterval (14807826060 / 1000000000000) (14807826062 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2971346444303527 / 4000000000000) 4 (IntervalRat.scale (799 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (23565175898 / 1000000000000) (23565190806 / 1000000000000), orderedInterval (-17385207167 / 1000000000000) (-17385192259 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1984721720525993 / 4000000000000) 4 (IntervalRat.scale (799 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (20045630832 / 1000000000000) (20045630833 / 1000000000000), orderedInterval (29665045592 / 1000000000000) (29665045593 / 1000000000000)))) (orderedInterval (-31872492317 / 1000000000000) (-31872477203 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate528_chunkChecks4 :
    compactCertificate528.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate528.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate528_chunkChecks4_0
    compactCertificate528_chunkChecks4_1 compactCertificate528_chunkChecks4_2

theorem compactCertificate528_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate528.chunkCheck r b = true :=
  compactCertificate528.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate528_chunkChecks0
    · exact compactCertificate528_chunkChecks1
    · exact compactCertificate528_chunkChecks2
    · exact compactCertificate528_chunkChecks3
    · exact compactCertificate528_chunkChecks4)

theorem compactCertificate528_coefficient0 :
    compactCertificate528.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate528_coefficient1 :
    compactCertificate528.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate528_coefficient2 :
    compactCertificate528.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate528_coefficient3 :
    compactCertificate528.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate528_coefficient4 :
    compactCertificate528.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate528_coefficients : ∀ r : Fin 5,
    compactCertificate528.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate528_coefficient0
  · exact compactCertificate528_coefficient1
  · exact compactCertificate528_coefficient2
  · exact compactCertificate528_coefficient3
  · exact compactCertificate528_coefficient4

theorem compactCertificate528_lower : (1 : ℚ) ≤ compactCertificate528.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate528, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate528_proves {t : ℝ} (ht : t ∈ compactCertificate528.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate528.proves compactCertificate528_states compactCertificate528_chunks
    compactCertificate528_coefficients compactCertificate528_lower ht

end Erdos232
