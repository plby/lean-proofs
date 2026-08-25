/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate484 : CompactCertificate where
  left := 355
  right := 356
  center := 711 / 2
  grid := fun i =>
    match i.val with
    | 0 => 113
    | 1 => 83
    | 2 => 135
    | 3 => 24
    | 4 => 65
    | 5 => 177
    | 6 => 131
    | 7 => 224
    | 8 => 165
    | 9 => 253
    | 10 => 146
    | 11 => 259
    | 12 => 242
    | 13 => 173
    | 14 => 196
    | 15 => 163
    | 16 => 144
    | 17 => 209
    | 18 => 116
    | 19 => 98
    | 20 => 61
    | 21 => 33
    | 22 => 90
    | 23 => 122
    | 24 => 52
    | 25 => 211
    | _ => 141
  point := fun i =>
    match i.val with
    | 0 => 711 / 2
    | 1 => 1047438763957611 / 4000000000000
    | 2 => 338720175276363 / 800000000000
    | 3 => 305640018973377 / 4000000000000
    | 4 => 820992082787469 / 4000000000000
    | 5 => 2229153210472473 / 4000000000000
    | 6 => 1641984165575649 / 4000000000000
    | 7 => 2813567854437477 / 4000000000000
    | 8 => 2072461347229743 / 4000000000000
    | 9 => 3179688664004289 / 4000000000000
    | 10 => 1835794106101881 / 4000000000000
    | 11 => 3257648856386829 / 4000000000000
    | 12 => 3043718132732001 / 4000000000000
    | 13 => 2172140879408433 / 4000000000000
    | 14 => 2462976248362407 / 4000000000000
    | 15 => 2053372817702583 / 4000000000000
    | 16 => 1814217156990243 / 4000000000000
    | 17 => 525830844606057 / 800000000000
    | 18 => 1454475789141579 / 4000000000000
    | 19 => 1232975234333619 / 4000000000000
    | 20 => 771538652770257 / 4000000000000
    | 21 => 414936053481519 / 4000000000000
    | 22 => 1126632101761557 / 4000000000000
    | 23 => 1538319816214389 / 4000000000000
    | 24 => 650461347229743 / 4000000000000
    | 25 => 2644089263954703 / 4000000000000
    | _ => 1766129090480577 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-40601913203 / 1000000000000) (-40601913200 / 1000000000000), orderedInterval (-11870009770 / 1000000000000) (-11870009767 / 1000000000000))
    | 1 => (orderedInterval (-46778334768 / 1000000000000) (-46778329521 / 1000000000000), orderedInterval (15675608500 / 1000000000000) (15675613747 / 1000000000000))
    | 2 => (orderedInterval (-2724250233 / 1000000000000) (-2724250232 / 1000000000000), orderedInterval (-38677115997 / 1000000000000) (-38677115996 / 1000000000000))
    | 3 => (orderedInterval (88981211524 / 1000000000000) (88981212131 / 1000000000000), orderedInterval (-20924601938 / 1000000000000) (-20924601332 / 1000000000000))
    | 4 => (orderedInterval (-53842616561 / 1000000000000) (-53842614627 / 1000000000000), orderedInterval (14367539638 / 1000000000000) (14367541571 / 1000000000000))
    | 5 => (orderedInterval (-30568218587 / 1000000000000) (-30568151427 / 1000000000000), orderedInterval (14447459954 / 1000000000000) (14447527113 / 1000000000000))
    | 6 => (orderedInterval (10409298193 / 1000000000000) (10409298229 / 1000000000000), orderedInterval (-37992967759 / 1000000000000) (-37992967722 / 1000000000000))
    | 7 => (orderedInterval (13367492085 / 1000000000000) (13367492086 / 1000000000000), orderedInterval (26941962406 / 1000000000000) (26941962407 / 1000000000000))
    | 8 => (orderedInterval (-17953051734 / 1000000000000) (-17953051733 / 1000000000000), orderedInterval (-30089323777 / 1000000000000) (-30089323776 / 1000000000000))
    | 9 => (orderedInterval (-21891773105 / 1000000000000) (-21891773104 / 1000000000000), orderedInterval (-17919669253 / 1000000000000) (-17919669252 / 1000000000000))
    | 10 => (orderedInterval (32510590389 / 1000000000000) (32510590390 / 1000000000000), orderedInterval (18135652419 / 1000000000000) (18135652420 / 1000000000000))
    | 11 => (orderedInterval (-27929396215 / 1000000000000) (-27929394188 / 1000000000000), orderedInterval (-1263890633 / 1000000000000) (-1263888606 / 1000000000000))
    | 12 => (orderedInterval (28711564986 / 1000000000000) (28711565589 / 1000000000000), orderedInterval (3485441782 / 1000000000000) (3485442385 / 1000000000000))
    | 13 => (orderedInterval (-10928353826 / 1000000000000) (-10928353825 / 1000000000000), orderedInterval (-32438474553 / 1000000000000) (-32438474552 / 1000000000000))
    | 14 => (orderedInterval (22547048350 / 1000000000000) (22547048351 / 1000000000000), orderedInterval (22906216145 / 1000000000000) (22906216146 / 1000000000000))
    | 15 => (orderedInterval (-31269269897 / 1000000000000) (-31269193582 / 1000000000000), orderedInterval (16228543306 / 1000000000000) (16228619621 / 1000000000000))
    | 16 => (orderedInterval (34802460838 / 1000000000000) (34802485012 / 1000000000000), orderedInterval (-13909622703 / 1000000000000) (-13909598529 / 1000000000000))
    | 17 => (orderedInterval (-30995933579 / 1000000000000) (-30995933114 / 1000000000000), orderedInterval (-2770400028 / 1000000000000) (-2770399564 / 1000000000000))
    | 18 => (orderedInterval (-868005750 / 1000000000000) (-868005749 / 1000000000000), orderedInterval (41834630520 / 1000000000000) (41834630522 / 1000000000000))
    | 19 => (orderedInterval (41531539064 / 1000000000000) (41531539065 / 1000000000000), orderedInterval (18383699391 / 1000000000000) (18383699392 / 1000000000000))
    | 20 => (orderedInterval (-51440853888 / 1000000000000) (-51440838796 / 1000000000000), orderedInterval (25713662620 / 1000000000000) (25713677712 / 1000000000000))
    | 21 => (orderedInterval (-58628897979 / 1000000000000) (-58628897978 / 1000000000000), orderedInterval (-51675893590 / 1000000000000) (-51675893589 / 1000000000000))
    | 22 => (orderedInterval (-14065965957 / 1000000000000) (-14065965808 / 1000000000000), orderedInterval (45438727881 / 1000000000000) (45438728030 / 1000000000000))
    | 23 => (orderedInterval (35309659092 / 1000000000000) (35309721576 / 1000000000000), orderedInterval (-20259519029 / 1000000000000) (-20259456545 / 1000000000000))
    | 24 => (orderedInterval (2323793328 / 1000000000000) (2323793331 / 1000000000000), orderedInterval (62518849039 / 1000000000000) (62518849042 / 1000000000000))
    | 25 => (orderedInterval (27200629143 / 1000000000000) (27200701940 / 1000000000000), orderedInterval (-14960731851 / 1000000000000) (-14960659054 / 1000000000000))
    | _ => (orderedInterval (22894441009 / 1000000000000) (22894444745 / 1000000000000), orderedInterval (-30319272557 / 1000000000000) (-30319268821 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-16688922494 / 1000000000000) (-16688922419 / 1000000000000)
      | 1 => orderedInterval (-758192114 / 1000000000000) (-758187220 / 1000000000000)
      | 2 => orderedInterval (-846196789 / 1000000000000) (-846196768 / 1000000000000)
      | 3 => orderedInterval (2328342675 / 1000000000000) (2328343104 / 1000000000000)
      | 4 => orderedInterval (-1665849894 / 1000000000000) (-1665849841 / 1000000000000)
      | 5 => orderedInterval (-3146336129 / 1000000000000) (-3146333818 / 1000000000000)
      | 6 => orderedInterval (-3886566708 / 1000000000000) (-3886566127 / 1000000000000)
      | 7 => orderedInterval (-1304395097 / 1000000000000) (-1304390262 / 1000000000000)
      | _ => orderedInterval (-6495782090 / 1000000000000) (-6495775364 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-7300376969 / 1000000000000) (-7300376903 / 1000000000000)
      | 1 => orderedInterval (-1258389986 / 1000000000000) (-1258382410 / 1000000000000)
      | 2 => orderedInterval (-2704052101 / 1000000000000) (-2704052066 / 1000000000000)
      | 3 => orderedInterval (8442992851 / 1000000000000) (8442993804 / 1000000000000)
      | 4 => orderedInterval (-5021106107 / 1000000000000) (-5021106014 / 1000000000000)
      | 5 => orderedInterval (1155013093 / 1000000000000) (1155016202 / 1000000000000)
      | 6 => orderedInterval (-7289812223 / 1000000000000) (-7289811873 / 1000000000000)
      | 7 => orderedInterval (1141364735 / 1000000000000) (1141369957 / 1000000000000)
      | _ => orderedInterval (9502223222 / 1000000000000) (9502235250 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (16576972060 / 1000000000000) (16576972120 / 1000000000000)
      | 1 => orderedInterval (-4636760511 / 1000000000000) (-4636748666 / 1000000000000)
      | 2 => orderedInterval (2543350569 / 1000000000000) (2543350631 / 1000000000000)
      | 3 => orderedInterval (-2650855092 / 1000000000000) (-2650852951 / 1000000000000)
      | 4 => orderedInterval (5142482729 / 1000000000000) (5142482894 / 1000000000000)
      | 5 => orderedInterval (6704448290 / 1000000000000) (6704452503 / 1000000000000)
      | 6 => orderedInterval (2135577918 / 1000000000000) (2135578143 / 1000000000000)
      | 7 => orderedInterval (2871215579 / 1000000000000) (2871221239 / 1000000000000)
      | _ => orderedInterval (14251986911 / 1000000000000) (14252008718 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (8434100588 / 1000000000000) (8434100646 / 1000000000000)
      | 1 => orderedInterval (3866391849 / 1000000000000) (3866410389 / 1000000000000)
      | 2 => orderedInterval (8680873702 / 1000000000000) (8680873815 / 1000000000000)
      | 3 => orderedInterval (-36322915434 / 1000000000000) (-36322910592 / 1000000000000)
      | 4 => orderedInterval (12138053695 / 1000000000000) (12138053996 / 1000000000000)
      | 5 => orderedInterval (-1787819072 / 1000000000000) (-1787813346 / 1000000000000)
      | 6 => orderedInterval (7696395588 / 1000000000000) (7696395744 / 1000000000000)
      | 7 => orderedInterval (-1484802396 / 1000000000000) (-1484796276 / 1000000000000)
      | _ => orderedInterval (-18804139397 / 1000000000000) (-18804099583 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-16590468462 / 1000000000000) (-16590468402 / 1000000000000)
      | 1 => orderedInterval (12880829477 / 1000000000000) (12880858576 / 1000000000000)
      | 2 => orderedInterval (-8325481108 / 1000000000000) (-8325480899 / 1000000000000)
      | 3 => orderedInterval (-5213687010 / 1000000000000) (-5213676004 / 1000000000000)
      | 4 => orderedInterval (-17601503757 / 1000000000000) (-17601503192 / 1000000000000)
      | 5 => orderedInterval (-16110820982 / 1000000000000) (-16110813135 / 1000000000000)
      | 6 => orderedInterval (-1365164219 / 1000000000000) (-1365164100 / 1000000000000)
      | 7 => orderedInterval (-3564258225 / 1000000000000) (-3564251590 / 1000000000000)
      | _ => orderedInterval (-36582946167 / 1000000000000) (-36582872936 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-32463898640 / 1000000000000) (-32463878715 / 1000000000000)
    | 1 => orderedInterval (-3332143485 / 1000000000000) (-3332114053 / 1000000000000)
    | 2 => orderedInterval (42938418453 / 1000000000000) (42938464631 / 1000000000000)
    | 3 => orderedInterval (-17583860877 / 1000000000000) (-17583785207 / 1000000000000)
    | _ => orderedInterval (-92473500453 / 1000000000000) (-92473371682 / 1000000000000)

theorem compactCertificate484_stateChecks0 :
    compactCertificate484.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 113 12 (711 / 2)) (orderedInterval (-40601913203 / 1000000000000) (-40601913200 / 1000000000000), orderedInterval (-11870009770 / 1000000000000) (-11870009767 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 83 12 (1047438763957611 / 4000000000000)) (orderedInterval (-46778334768 / 1000000000000) (-46778329521 / 1000000000000), orderedInterval (15675608500 / 1000000000000) (15675613747 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 135 12 (338720175276363 / 800000000000)) (orderedInterval (-2724250233 / 1000000000000) (-2724250232 / 1000000000000), orderedInterval (-38677115997 / 1000000000000) (-38677115996 / 1000000000000))) = true
  rfl'

theorem compactCertificate484_stateChecks1 :
    compactCertificate484.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 24 12 (305640018973377 / 4000000000000)) (orderedInterval (88981211524 / 1000000000000) (88981212131 / 1000000000000), orderedInterval (-20924601938 / 1000000000000) (-20924601332 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 65 12 (820992082787469 / 4000000000000)) (orderedInterval (-53842616561 / 1000000000000) (-53842614627 / 1000000000000), orderedInterval (14367539638 / 1000000000000) (14367541571 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 177 12 (2229153210472473 / 4000000000000)) (orderedInterval (-30568218587 / 1000000000000) (-30568151427 / 1000000000000), orderedInterval (14447459954 / 1000000000000) (14447527113 / 1000000000000))) = true
  rfl'

theorem compactCertificate484_stateChecks2 :
    compactCertificate484.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 131 12 (1641984165575649 / 4000000000000)) (orderedInterval (10409298193 / 1000000000000) (10409298229 / 1000000000000), orderedInterval (-37992967759 / 1000000000000) (-37992967722 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 224 12 (2813567854437477 / 4000000000000)) (orderedInterval (13367492085 / 1000000000000) (13367492086 / 1000000000000), orderedInterval (26941962406 / 1000000000000) (26941962407 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 165 12 (2072461347229743 / 4000000000000)) (orderedInterval (-17953051734 / 1000000000000) (-17953051733 / 1000000000000), orderedInterval (-30089323777 / 1000000000000) (-30089323776 / 1000000000000))) = true
  rfl'

theorem compactCertificate484_stateChecks3 :
    compactCertificate484.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 253 12 (3179688664004289 / 4000000000000)) (orderedInterval (-21891773105 / 1000000000000) (-21891773104 / 1000000000000), orderedInterval (-17919669253 / 1000000000000) (-17919669252 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 146 12 (1835794106101881 / 4000000000000)) (orderedInterval (32510590389 / 1000000000000) (32510590390 / 1000000000000), orderedInterval (18135652419 / 1000000000000) (18135652420 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 259 12 (3257648856386829 / 4000000000000)) (orderedInterval (-27929396215 / 1000000000000) (-27929394188 / 1000000000000), orderedInterval (-1263890633 / 1000000000000) (-1263888606 / 1000000000000))) = true
  rfl'

theorem compactCertificate484_stateChecks4 :
    compactCertificate484.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 242 12 (3043718132732001 / 4000000000000)) (orderedInterval (28711564986 / 1000000000000) (28711565589 / 1000000000000), orderedInterval (3485441782 / 1000000000000) (3485442385 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 173 12 (2172140879408433 / 4000000000000)) (orderedInterval (-10928353826 / 1000000000000) (-10928353825 / 1000000000000), orderedInterval (-32438474553 / 1000000000000) (-32438474552 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 196 12 (2462976248362407 / 4000000000000)) (orderedInterval (22547048350 / 1000000000000) (22547048351 / 1000000000000), orderedInterval (22906216145 / 1000000000000) (22906216146 / 1000000000000))) = true
  rfl'

theorem compactCertificate484_stateChecks5 :
    compactCertificate484.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 163 12 (2053372817702583 / 4000000000000)) (orderedInterval (-31269269897 / 1000000000000) (-31269193582 / 1000000000000), orderedInterval (16228543306 / 1000000000000) (16228619621 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 144 12 (1814217156990243 / 4000000000000)) (orderedInterval (34802460838 / 1000000000000) (34802485012 / 1000000000000), orderedInterval (-13909622703 / 1000000000000) (-13909598529 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 209 12 (525830844606057 / 800000000000)) (orderedInterval (-30995933579 / 1000000000000) (-30995933114 / 1000000000000), orderedInterval (-2770400028 / 1000000000000) (-2770399564 / 1000000000000))) = true
  rfl'

theorem compactCertificate484_stateChecks6 :
    compactCertificate484.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 116 12 (1454475789141579 / 4000000000000)) (orderedInterval (-868005750 / 1000000000000) (-868005749 / 1000000000000), orderedInterval (41834630520 / 1000000000000) (41834630522 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 98 12 (1232975234333619 / 4000000000000)) (orderedInterval (41531539064 / 1000000000000) (41531539065 / 1000000000000), orderedInterval (18383699391 / 1000000000000) (18383699392 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 61 12 (771538652770257 / 4000000000000)) (orderedInterval (-51440853888 / 1000000000000) (-51440838796 / 1000000000000), orderedInterval (25713662620 / 1000000000000) (25713677712 / 1000000000000))) = true
  rfl'

theorem compactCertificate484_stateChecks7 :
    compactCertificate484.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 33 12 (414936053481519 / 4000000000000)) (orderedInterval (-58628897979 / 1000000000000) (-58628897978 / 1000000000000), orderedInterval (-51675893590 / 1000000000000) (-51675893589 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 90 12 (1126632101761557 / 4000000000000)) (orderedInterval (-14065965957 / 1000000000000) (-14065965808 / 1000000000000), orderedInterval (45438727881 / 1000000000000) (45438728030 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 122 12 (1538319816214389 / 4000000000000)) (orderedInterval (35309659092 / 1000000000000) (35309721576 / 1000000000000), orderedInterval (-20259519029 / 1000000000000) (-20259456545 / 1000000000000))) = true
  rfl'

theorem compactCertificate484_stateChecks8 :
    compactCertificate484.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 52 12 (650461347229743 / 4000000000000)) (orderedInterval (2323793328 / 1000000000000) (2323793331 / 1000000000000), orderedInterval (62518849039 / 1000000000000) (62518849042 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 211 12 (2644089263954703 / 4000000000000)) (orderedInterval (27200629143 / 1000000000000) (27200701940 / 1000000000000), orderedInterval (-14960731851 / 1000000000000) (-14960659054 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 141 12 (1766129090480577 / 4000000000000)) (orderedInterval (22894441009 / 1000000000000) (22894444745 / 1000000000000), orderedInterval (-30319272557 / 1000000000000) (-30319268821 / 1000000000000))) = true
  rfl'

theorem compactCertificate484_states : ∀ j,
    BesselStateValid (compactCertificate484.point j) (compactCertificate484.state j) :=
  compactCertificate484.statesValid_of_checks3 compactCertificate484_stateChecks0
    compactCertificate484_stateChecks1 compactCertificate484_stateChecks2
    compactCertificate484_stateChecks3 compactCertificate484_stateChecks4
    compactCertificate484_stateChecks5 compactCertificate484_stateChecks6
    compactCertificate484_stateChecks7 compactCertificate484_stateChecks8

theorem compactCertificate484_chunkChecks0_0 :
    compactCertificate484.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (711 / 2) 0 (IntervalRat.scale (711 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-40601913203 / 1000000000000) (-40601913200 / 1000000000000), orderedInterval (-11870009770 / 1000000000000) (-11870009767 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1047438763957611 / 4000000000000) 0 (IntervalRat.scale (711 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-46778334768 / 1000000000000) (-46778329521 / 1000000000000), orderedInterval (15675608500 / 1000000000000) (15675613747 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (338720175276363 / 800000000000) 0 (IntervalRat.scale (711 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-2724250233 / 1000000000000) (-2724250232 / 1000000000000), orderedInterval (-38677115997 / 1000000000000) (-38677115996 / 1000000000000)))) (orderedInterval (-16688922494 / 1000000000000) (-16688922419 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (305640018973377 / 4000000000000) 0 (IntervalRat.scale (711 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (88981211524 / 1000000000000) (88981212131 / 1000000000000), orderedInterval (-20924601938 / 1000000000000) (-20924601332 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (820992082787469 / 4000000000000) 0 (IntervalRat.scale (711 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-53842616561 / 1000000000000) (-53842614627 / 1000000000000), orderedInterval (14367539638 / 1000000000000) (14367541571 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2229153210472473 / 4000000000000) 0 (IntervalRat.scale (711 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30568218587 / 1000000000000) (-30568151427 / 1000000000000), orderedInterval (14447459954 / 1000000000000) (14447527113 / 1000000000000)))) (orderedInterval (-758192114 / 1000000000000) (-758187220 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1641984165575649 / 4000000000000) 0 (IntervalRat.scale (711 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (10409298193 / 1000000000000) (10409298229 / 1000000000000), orderedInterval (-37992967759 / 1000000000000) (-37992967722 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2813567854437477 / 4000000000000) 0 (IntervalRat.scale (711 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (13367492085 / 1000000000000) (13367492086 / 1000000000000), orderedInterval (26941962406 / 1000000000000) (26941962407 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2072461347229743 / 4000000000000) 0 (IntervalRat.scale (711 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-17953051734 / 1000000000000) (-17953051733 / 1000000000000), orderedInterval (-30089323777 / 1000000000000) (-30089323776 / 1000000000000)))) (orderedInterval (-846196789 / 1000000000000) (-846196768 / 1000000000000))) = true
  rfl'

theorem compactCertificate484_chunkChecks0_1 :
    compactCertificate484.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3179688664004289 / 4000000000000) 0 (IntervalRat.scale (711 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-21891773105 / 1000000000000) (-21891773104 / 1000000000000), orderedInterval (-17919669253 / 1000000000000) (-17919669252 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1835794106101881 / 4000000000000) 0 (IntervalRat.scale (711 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (32510590389 / 1000000000000) (32510590390 / 1000000000000), orderedInterval (18135652419 / 1000000000000) (18135652420 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3257648856386829 / 4000000000000) 0 (IntervalRat.scale (711 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-27929396215 / 1000000000000) (-27929394188 / 1000000000000), orderedInterval (-1263890633 / 1000000000000) (-1263888606 / 1000000000000)))) (orderedInterval (2328342675 / 1000000000000) (2328343104 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3043718132732001 / 4000000000000) 0 (IntervalRat.scale (711 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (28711564986 / 1000000000000) (28711565589 / 1000000000000), orderedInterval (3485441782 / 1000000000000) (3485442385 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2172140879408433 / 4000000000000) 0 (IntervalRat.scale (711 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-10928353826 / 1000000000000) (-10928353825 / 1000000000000), orderedInterval (-32438474553 / 1000000000000) (-32438474552 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2462976248362407 / 4000000000000) 0 (IntervalRat.scale (711 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (22547048350 / 1000000000000) (22547048351 / 1000000000000), orderedInterval (22906216145 / 1000000000000) (22906216146 / 1000000000000)))) (orderedInterval (-1665849894 / 1000000000000) (-1665849841 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2053372817702583 / 4000000000000) 0 (IntervalRat.scale (711 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-31269269897 / 1000000000000) (-31269193582 / 1000000000000), orderedInterval (16228543306 / 1000000000000) (16228619621 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1814217156990243 / 4000000000000) 0 (IntervalRat.scale (711 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (34802460838 / 1000000000000) (34802485012 / 1000000000000), orderedInterval (-13909622703 / 1000000000000) (-13909598529 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (525830844606057 / 800000000000) 0 (IntervalRat.scale (711 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-30995933579 / 1000000000000) (-30995933114 / 1000000000000), orderedInterval (-2770400028 / 1000000000000) (-2770399564 / 1000000000000)))) (orderedInterval (-3146336129 / 1000000000000) (-3146333818 / 1000000000000))) = true
  rfl'

theorem compactCertificate484_chunkChecks0_2 :
    compactCertificate484.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1454475789141579 / 4000000000000) 0 (IntervalRat.scale (711 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-868005750 / 1000000000000) (-868005749 / 1000000000000), orderedInterval (41834630520 / 1000000000000) (41834630522 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1232975234333619 / 4000000000000) 0 (IntervalRat.scale (711 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (41531539064 / 1000000000000) (41531539065 / 1000000000000), orderedInterval (18383699391 / 1000000000000) (18383699392 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (771538652770257 / 4000000000000) 0 (IntervalRat.scale (711 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-51440853888 / 1000000000000) (-51440838796 / 1000000000000), orderedInterval (25713662620 / 1000000000000) (25713677712 / 1000000000000)))) (orderedInterval (-3886566708 / 1000000000000) (-3886566127 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (414936053481519 / 4000000000000) 0 (IntervalRat.scale (711 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-58628897979 / 1000000000000) (-58628897978 / 1000000000000), orderedInterval (-51675893590 / 1000000000000) (-51675893589 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1126632101761557 / 4000000000000) 0 (IntervalRat.scale (711 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-14065965957 / 1000000000000) (-14065965808 / 1000000000000), orderedInterval (45438727881 / 1000000000000) (45438728030 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1538319816214389 / 4000000000000) 0 (IntervalRat.scale (711 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (35309659092 / 1000000000000) (35309721576 / 1000000000000), orderedInterval (-20259519029 / 1000000000000) (-20259456545 / 1000000000000)))) (orderedInterval (-1304395097 / 1000000000000) (-1304390262 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (650461347229743 / 4000000000000) 0 (IntervalRat.scale (711 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (2323793328 / 1000000000000) (2323793331 / 1000000000000), orderedInterval (62518849039 / 1000000000000) (62518849042 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2644089263954703 / 4000000000000) 0 (IntervalRat.scale (711 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27200629143 / 1000000000000) (27200701940 / 1000000000000), orderedInterval (-14960731851 / 1000000000000) (-14960659054 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1766129090480577 / 4000000000000) 0 (IntervalRat.scale (711 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (22894441009 / 1000000000000) (22894444745 / 1000000000000), orderedInterval (-30319272557 / 1000000000000) (-30319268821 / 1000000000000)))) (orderedInterval (-6495782090 / 1000000000000) (-6495775364 / 1000000000000))) = true
  rfl'

theorem compactCertificate484_chunkChecks0 :
    compactCertificate484.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate484.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate484_chunkChecks0_0
    compactCertificate484_chunkChecks0_1 compactCertificate484_chunkChecks0_2

theorem compactCertificate484_chunkChecks1_0 :
    compactCertificate484.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (711 / 2) 1 (IntervalRat.scale (711 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-40601913203 / 1000000000000) (-40601913200 / 1000000000000), orderedInterval (-11870009770 / 1000000000000) (-11870009767 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1047438763957611 / 4000000000000) 1 (IntervalRat.scale (711 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-46778334768 / 1000000000000) (-46778329521 / 1000000000000), orderedInterval (15675608500 / 1000000000000) (15675613747 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (338720175276363 / 800000000000) 1 (IntervalRat.scale (711 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-2724250233 / 1000000000000) (-2724250232 / 1000000000000), orderedInterval (-38677115997 / 1000000000000) (-38677115996 / 1000000000000)))) (orderedInterval (-7300376969 / 1000000000000) (-7300376903 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (305640018973377 / 4000000000000) 1 (IntervalRat.scale (711 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (88981211524 / 1000000000000) (88981212131 / 1000000000000), orderedInterval (-20924601938 / 1000000000000) (-20924601332 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (820992082787469 / 4000000000000) 1 (IntervalRat.scale (711 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-53842616561 / 1000000000000) (-53842614627 / 1000000000000), orderedInterval (14367539638 / 1000000000000) (14367541571 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2229153210472473 / 4000000000000) 1 (IntervalRat.scale (711 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30568218587 / 1000000000000) (-30568151427 / 1000000000000), orderedInterval (14447459954 / 1000000000000) (14447527113 / 1000000000000)))) (orderedInterval (-1258389986 / 1000000000000) (-1258382410 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1641984165575649 / 4000000000000) 1 (IntervalRat.scale (711 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (10409298193 / 1000000000000) (10409298229 / 1000000000000), orderedInterval (-37992967759 / 1000000000000) (-37992967722 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2813567854437477 / 4000000000000) 1 (IntervalRat.scale (711 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (13367492085 / 1000000000000) (13367492086 / 1000000000000), orderedInterval (26941962406 / 1000000000000) (26941962407 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2072461347229743 / 4000000000000) 1 (IntervalRat.scale (711 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-17953051734 / 1000000000000) (-17953051733 / 1000000000000), orderedInterval (-30089323777 / 1000000000000) (-30089323776 / 1000000000000)))) (orderedInterval (-2704052101 / 1000000000000) (-2704052066 / 1000000000000))) = true
  rfl'

theorem compactCertificate484_chunkChecks1_1 :
    compactCertificate484.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3179688664004289 / 4000000000000) 1 (IntervalRat.scale (711 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-21891773105 / 1000000000000) (-21891773104 / 1000000000000), orderedInterval (-17919669253 / 1000000000000) (-17919669252 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1835794106101881 / 4000000000000) 1 (IntervalRat.scale (711 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (32510590389 / 1000000000000) (32510590390 / 1000000000000), orderedInterval (18135652419 / 1000000000000) (18135652420 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3257648856386829 / 4000000000000) 1 (IntervalRat.scale (711 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-27929396215 / 1000000000000) (-27929394188 / 1000000000000), orderedInterval (-1263890633 / 1000000000000) (-1263888606 / 1000000000000)))) (orderedInterval (8442992851 / 1000000000000) (8442993804 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3043718132732001 / 4000000000000) 1 (IntervalRat.scale (711 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (28711564986 / 1000000000000) (28711565589 / 1000000000000), orderedInterval (3485441782 / 1000000000000) (3485442385 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2172140879408433 / 4000000000000) 1 (IntervalRat.scale (711 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-10928353826 / 1000000000000) (-10928353825 / 1000000000000), orderedInterval (-32438474553 / 1000000000000) (-32438474552 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2462976248362407 / 4000000000000) 1 (IntervalRat.scale (711 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (22547048350 / 1000000000000) (22547048351 / 1000000000000), orderedInterval (22906216145 / 1000000000000) (22906216146 / 1000000000000)))) (orderedInterval (-5021106107 / 1000000000000) (-5021106014 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2053372817702583 / 4000000000000) 1 (IntervalRat.scale (711 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-31269269897 / 1000000000000) (-31269193582 / 1000000000000), orderedInterval (16228543306 / 1000000000000) (16228619621 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1814217156990243 / 4000000000000) 1 (IntervalRat.scale (711 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (34802460838 / 1000000000000) (34802485012 / 1000000000000), orderedInterval (-13909622703 / 1000000000000) (-13909598529 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (525830844606057 / 800000000000) 1 (IntervalRat.scale (711 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-30995933579 / 1000000000000) (-30995933114 / 1000000000000), orderedInterval (-2770400028 / 1000000000000) (-2770399564 / 1000000000000)))) (orderedInterval (1155013093 / 1000000000000) (1155016202 / 1000000000000))) = true
  rfl'

theorem compactCertificate484_chunkChecks1_2 :
    compactCertificate484.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1454475789141579 / 4000000000000) 1 (IntervalRat.scale (711 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-868005750 / 1000000000000) (-868005749 / 1000000000000), orderedInterval (41834630520 / 1000000000000) (41834630522 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1232975234333619 / 4000000000000) 1 (IntervalRat.scale (711 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (41531539064 / 1000000000000) (41531539065 / 1000000000000), orderedInterval (18383699391 / 1000000000000) (18383699392 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (771538652770257 / 4000000000000) 1 (IntervalRat.scale (711 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-51440853888 / 1000000000000) (-51440838796 / 1000000000000), orderedInterval (25713662620 / 1000000000000) (25713677712 / 1000000000000)))) (orderedInterval (-7289812223 / 1000000000000) (-7289811873 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (414936053481519 / 4000000000000) 1 (IntervalRat.scale (711 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-58628897979 / 1000000000000) (-58628897978 / 1000000000000), orderedInterval (-51675893590 / 1000000000000) (-51675893589 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1126632101761557 / 4000000000000) 1 (IntervalRat.scale (711 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-14065965957 / 1000000000000) (-14065965808 / 1000000000000), orderedInterval (45438727881 / 1000000000000) (45438728030 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1538319816214389 / 4000000000000) 1 (IntervalRat.scale (711 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (35309659092 / 1000000000000) (35309721576 / 1000000000000), orderedInterval (-20259519029 / 1000000000000) (-20259456545 / 1000000000000)))) (orderedInterval (1141364735 / 1000000000000) (1141369957 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (650461347229743 / 4000000000000) 1 (IntervalRat.scale (711 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (2323793328 / 1000000000000) (2323793331 / 1000000000000), orderedInterval (62518849039 / 1000000000000) (62518849042 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2644089263954703 / 4000000000000) 1 (IntervalRat.scale (711 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27200629143 / 1000000000000) (27200701940 / 1000000000000), orderedInterval (-14960731851 / 1000000000000) (-14960659054 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1766129090480577 / 4000000000000) 1 (IntervalRat.scale (711 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (22894441009 / 1000000000000) (22894444745 / 1000000000000), orderedInterval (-30319272557 / 1000000000000) (-30319268821 / 1000000000000)))) (orderedInterval (9502223222 / 1000000000000) (9502235250 / 1000000000000))) = true
  rfl'

theorem compactCertificate484_chunkChecks1 :
    compactCertificate484.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate484.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate484_chunkChecks1_0
    compactCertificate484_chunkChecks1_1 compactCertificate484_chunkChecks1_2

theorem compactCertificate484_chunkChecks2_0 :
    compactCertificate484.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (711 / 2) 2 (IntervalRat.scale (711 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-40601913203 / 1000000000000) (-40601913200 / 1000000000000), orderedInterval (-11870009770 / 1000000000000) (-11870009767 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1047438763957611 / 4000000000000) 2 (IntervalRat.scale (711 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-46778334768 / 1000000000000) (-46778329521 / 1000000000000), orderedInterval (15675608500 / 1000000000000) (15675613747 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (338720175276363 / 800000000000) 2 (IntervalRat.scale (711 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-2724250233 / 1000000000000) (-2724250232 / 1000000000000), orderedInterval (-38677115997 / 1000000000000) (-38677115996 / 1000000000000)))) (orderedInterval (16576972060 / 1000000000000) (16576972120 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (305640018973377 / 4000000000000) 2 (IntervalRat.scale (711 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (88981211524 / 1000000000000) (88981212131 / 1000000000000), orderedInterval (-20924601938 / 1000000000000) (-20924601332 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (820992082787469 / 4000000000000) 2 (IntervalRat.scale (711 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-53842616561 / 1000000000000) (-53842614627 / 1000000000000), orderedInterval (14367539638 / 1000000000000) (14367541571 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2229153210472473 / 4000000000000) 2 (IntervalRat.scale (711 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30568218587 / 1000000000000) (-30568151427 / 1000000000000), orderedInterval (14447459954 / 1000000000000) (14447527113 / 1000000000000)))) (orderedInterval (-4636760511 / 1000000000000) (-4636748666 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1641984165575649 / 4000000000000) 2 (IntervalRat.scale (711 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (10409298193 / 1000000000000) (10409298229 / 1000000000000), orderedInterval (-37992967759 / 1000000000000) (-37992967722 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2813567854437477 / 4000000000000) 2 (IntervalRat.scale (711 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (13367492085 / 1000000000000) (13367492086 / 1000000000000), orderedInterval (26941962406 / 1000000000000) (26941962407 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2072461347229743 / 4000000000000) 2 (IntervalRat.scale (711 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-17953051734 / 1000000000000) (-17953051733 / 1000000000000), orderedInterval (-30089323777 / 1000000000000) (-30089323776 / 1000000000000)))) (orderedInterval (2543350569 / 1000000000000) (2543350631 / 1000000000000))) = true
  rfl'

theorem compactCertificate484_chunkChecks2_1 :
    compactCertificate484.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3179688664004289 / 4000000000000) 2 (IntervalRat.scale (711 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-21891773105 / 1000000000000) (-21891773104 / 1000000000000), orderedInterval (-17919669253 / 1000000000000) (-17919669252 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1835794106101881 / 4000000000000) 2 (IntervalRat.scale (711 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (32510590389 / 1000000000000) (32510590390 / 1000000000000), orderedInterval (18135652419 / 1000000000000) (18135652420 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3257648856386829 / 4000000000000) 2 (IntervalRat.scale (711 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-27929396215 / 1000000000000) (-27929394188 / 1000000000000), orderedInterval (-1263890633 / 1000000000000) (-1263888606 / 1000000000000)))) (orderedInterval (-2650855092 / 1000000000000) (-2650852951 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3043718132732001 / 4000000000000) 2 (IntervalRat.scale (711 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (28711564986 / 1000000000000) (28711565589 / 1000000000000), orderedInterval (3485441782 / 1000000000000) (3485442385 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2172140879408433 / 4000000000000) 2 (IntervalRat.scale (711 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-10928353826 / 1000000000000) (-10928353825 / 1000000000000), orderedInterval (-32438474553 / 1000000000000) (-32438474552 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2462976248362407 / 4000000000000) 2 (IntervalRat.scale (711 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (22547048350 / 1000000000000) (22547048351 / 1000000000000), orderedInterval (22906216145 / 1000000000000) (22906216146 / 1000000000000)))) (orderedInterval (5142482729 / 1000000000000) (5142482894 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2053372817702583 / 4000000000000) 2 (IntervalRat.scale (711 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-31269269897 / 1000000000000) (-31269193582 / 1000000000000), orderedInterval (16228543306 / 1000000000000) (16228619621 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1814217156990243 / 4000000000000) 2 (IntervalRat.scale (711 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (34802460838 / 1000000000000) (34802485012 / 1000000000000), orderedInterval (-13909622703 / 1000000000000) (-13909598529 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (525830844606057 / 800000000000) 2 (IntervalRat.scale (711 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-30995933579 / 1000000000000) (-30995933114 / 1000000000000), orderedInterval (-2770400028 / 1000000000000) (-2770399564 / 1000000000000)))) (orderedInterval (6704448290 / 1000000000000) (6704452503 / 1000000000000))) = true
  rfl'

theorem compactCertificate484_chunkChecks2_2 :
    compactCertificate484.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1454475789141579 / 4000000000000) 2 (IntervalRat.scale (711 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-868005750 / 1000000000000) (-868005749 / 1000000000000), orderedInterval (41834630520 / 1000000000000) (41834630522 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1232975234333619 / 4000000000000) 2 (IntervalRat.scale (711 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (41531539064 / 1000000000000) (41531539065 / 1000000000000), orderedInterval (18383699391 / 1000000000000) (18383699392 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (771538652770257 / 4000000000000) 2 (IntervalRat.scale (711 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-51440853888 / 1000000000000) (-51440838796 / 1000000000000), orderedInterval (25713662620 / 1000000000000) (25713677712 / 1000000000000)))) (orderedInterval (2135577918 / 1000000000000) (2135578143 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (414936053481519 / 4000000000000) 2 (IntervalRat.scale (711 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-58628897979 / 1000000000000) (-58628897978 / 1000000000000), orderedInterval (-51675893590 / 1000000000000) (-51675893589 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1126632101761557 / 4000000000000) 2 (IntervalRat.scale (711 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-14065965957 / 1000000000000) (-14065965808 / 1000000000000), orderedInterval (45438727881 / 1000000000000) (45438728030 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1538319816214389 / 4000000000000) 2 (IntervalRat.scale (711 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (35309659092 / 1000000000000) (35309721576 / 1000000000000), orderedInterval (-20259519029 / 1000000000000) (-20259456545 / 1000000000000)))) (orderedInterval (2871215579 / 1000000000000) (2871221239 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (650461347229743 / 4000000000000) 2 (IntervalRat.scale (711 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (2323793328 / 1000000000000) (2323793331 / 1000000000000), orderedInterval (62518849039 / 1000000000000) (62518849042 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2644089263954703 / 4000000000000) 2 (IntervalRat.scale (711 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27200629143 / 1000000000000) (27200701940 / 1000000000000), orderedInterval (-14960731851 / 1000000000000) (-14960659054 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1766129090480577 / 4000000000000) 2 (IntervalRat.scale (711 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (22894441009 / 1000000000000) (22894444745 / 1000000000000), orderedInterval (-30319272557 / 1000000000000) (-30319268821 / 1000000000000)))) (orderedInterval (14251986911 / 1000000000000) (14252008718 / 1000000000000))) = true
  rfl'

theorem compactCertificate484_chunkChecks2 :
    compactCertificate484.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate484.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate484_chunkChecks2_0
    compactCertificate484_chunkChecks2_1 compactCertificate484_chunkChecks2_2

theorem compactCertificate484_chunkChecks3_0 :
    compactCertificate484.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (711 / 2) 3 (IntervalRat.scale (711 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-40601913203 / 1000000000000) (-40601913200 / 1000000000000), orderedInterval (-11870009770 / 1000000000000) (-11870009767 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1047438763957611 / 4000000000000) 3 (IntervalRat.scale (711 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-46778334768 / 1000000000000) (-46778329521 / 1000000000000), orderedInterval (15675608500 / 1000000000000) (15675613747 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (338720175276363 / 800000000000) 3 (IntervalRat.scale (711 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-2724250233 / 1000000000000) (-2724250232 / 1000000000000), orderedInterval (-38677115997 / 1000000000000) (-38677115996 / 1000000000000)))) (orderedInterval (8434100588 / 1000000000000) (8434100646 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (305640018973377 / 4000000000000) 3 (IntervalRat.scale (711 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (88981211524 / 1000000000000) (88981212131 / 1000000000000), orderedInterval (-20924601938 / 1000000000000) (-20924601332 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (820992082787469 / 4000000000000) 3 (IntervalRat.scale (711 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-53842616561 / 1000000000000) (-53842614627 / 1000000000000), orderedInterval (14367539638 / 1000000000000) (14367541571 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2229153210472473 / 4000000000000) 3 (IntervalRat.scale (711 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30568218587 / 1000000000000) (-30568151427 / 1000000000000), orderedInterval (14447459954 / 1000000000000) (14447527113 / 1000000000000)))) (orderedInterval (3866391849 / 1000000000000) (3866410389 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1641984165575649 / 4000000000000) 3 (IntervalRat.scale (711 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (10409298193 / 1000000000000) (10409298229 / 1000000000000), orderedInterval (-37992967759 / 1000000000000) (-37992967722 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2813567854437477 / 4000000000000) 3 (IntervalRat.scale (711 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (13367492085 / 1000000000000) (13367492086 / 1000000000000), orderedInterval (26941962406 / 1000000000000) (26941962407 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2072461347229743 / 4000000000000) 3 (IntervalRat.scale (711 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-17953051734 / 1000000000000) (-17953051733 / 1000000000000), orderedInterval (-30089323777 / 1000000000000) (-30089323776 / 1000000000000)))) (orderedInterval (8680873702 / 1000000000000) (8680873815 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate484_chunkChecks3_1 :
    compactCertificate484.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3179688664004289 / 4000000000000) 3 (IntervalRat.scale (711 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-21891773105 / 1000000000000) (-21891773104 / 1000000000000), orderedInterval (-17919669253 / 1000000000000) (-17919669252 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1835794106101881 / 4000000000000) 3 (IntervalRat.scale (711 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (32510590389 / 1000000000000) (32510590390 / 1000000000000), orderedInterval (18135652419 / 1000000000000) (18135652420 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3257648856386829 / 4000000000000) 3 (IntervalRat.scale (711 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-27929396215 / 1000000000000) (-27929394188 / 1000000000000), orderedInterval (-1263890633 / 1000000000000) (-1263888606 / 1000000000000)))) (orderedInterval (-36322915434 / 1000000000000) (-36322910592 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3043718132732001 / 4000000000000) 3 (IntervalRat.scale (711 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (28711564986 / 1000000000000) (28711565589 / 1000000000000), orderedInterval (3485441782 / 1000000000000) (3485442385 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2172140879408433 / 4000000000000) 3 (IntervalRat.scale (711 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-10928353826 / 1000000000000) (-10928353825 / 1000000000000), orderedInterval (-32438474553 / 1000000000000) (-32438474552 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2462976248362407 / 4000000000000) 3 (IntervalRat.scale (711 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (22547048350 / 1000000000000) (22547048351 / 1000000000000), orderedInterval (22906216145 / 1000000000000) (22906216146 / 1000000000000)))) (orderedInterval (12138053695 / 1000000000000) (12138053996 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2053372817702583 / 4000000000000) 3 (IntervalRat.scale (711 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-31269269897 / 1000000000000) (-31269193582 / 1000000000000), orderedInterval (16228543306 / 1000000000000) (16228619621 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1814217156990243 / 4000000000000) 3 (IntervalRat.scale (711 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (34802460838 / 1000000000000) (34802485012 / 1000000000000), orderedInterval (-13909622703 / 1000000000000) (-13909598529 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (525830844606057 / 800000000000) 3 (IntervalRat.scale (711 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-30995933579 / 1000000000000) (-30995933114 / 1000000000000), orderedInterval (-2770400028 / 1000000000000) (-2770399564 / 1000000000000)))) (orderedInterval (-1787819072 / 1000000000000) (-1787813346 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate484_chunkChecks3_2 :
    compactCertificate484.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1454475789141579 / 4000000000000) 3 (IntervalRat.scale (711 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-868005750 / 1000000000000) (-868005749 / 1000000000000), orderedInterval (41834630520 / 1000000000000) (41834630522 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1232975234333619 / 4000000000000) 3 (IntervalRat.scale (711 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (41531539064 / 1000000000000) (41531539065 / 1000000000000), orderedInterval (18383699391 / 1000000000000) (18383699392 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (771538652770257 / 4000000000000) 3 (IntervalRat.scale (711 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-51440853888 / 1000000000000) (-51440838796 / 1000000000000), orderedInterval (25713662620 / 1000000000000) (25713677712 / 1000000000000)))) (orderedInterval (7696395588 / 1000000000000) (7696395744 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (414936053481519 / 4000000000000) 3 (IntervalRat.scale (711 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-58628897979 / 1000000000000) (-58628897978 / 1000000000000), orderedInterval (-51675893590 / 1000000000000) (-51675893589 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1126632101761557 / 4000000000000) 3 (IntervalRat.scale (711 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-14065965957 / 1000000000000) (-14065965808 / 1000000000000), orderedInterval (45438727881 / 1000000000000) (45438728030 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1538319816214389 / 4000000000000) 3 (IntervalRat.scale (711 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (35309659092 / 1000000000000) (35309721576 / 1000000000000), orderedInterval (-20259519029 / 1000000000000) (-20259456545 / 1000000000000)))) (orderedInterval (-1484802396 / 1000000000000) (-1484796276 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (650461347229743 / 4000000000000) 3 (IntervalRat.scale (711 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (2323793328 / 1000000000000) (2323793331 / 1000000000000), orderedInterval (62518849039 / 1000000000000) (62518849042 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2644089263954703 / 4000000000000) 3 (IntervalRat.scale (711 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27200629143 / 1000000000000) (27200701940 / 1000000000000), orderedInterval (-14960731851 / 1000000000000) (-14960659054 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1766129090480577 / 4000000000000) 3 (IntervalRat.scale (711 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (22894441009 / 1000000000000) (22894444745 / 1000000000000), orderedInterval (-30319272557 / 1000000000000) (-30319268821 / 1000000000000)))) (orderedInterval (-18804139397 / 1000000000000) (-18804099583 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate484_chunkChecks3 :
    compactCertificate484.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate484.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate484_chunkChecks3_0
    compactCertificate484_chunkChecks3_1 compactCertificate484_chunkChecks3_2

theorem compactCertificate484_chunkChecks4_0 :
    compactCertificate484.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (711 / 2) 4 (IntervalRat.scale (711 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-40601913203 / 1000000000000) (-40601913200 / 1000000000000), orderedInterval (-11870009770 / 1000000000000) (-11870009767 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1047438763957611 / 4000000000000) 4 (IntervalRat.scale (711 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-46778334768 / 1000000000000) (-46778329521 / 1000000000000), orderedInterval (15675608500 / 1000000000000) (15675613747 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (338720175276363 / 800000000000) 4 (IntervalRat.scale (711 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-2724250233 / 1000000000000) (-2724250232 / 1000000000000), orderedInterval (-38677115997 / 1000000000000) (-38677115996 / 1000000000000)))) (orderedInterval (-16590468462 / 1000000000000) (-16590468402 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (305640018973377 / 4000000000000) 4 (IntervalRat.scale (711 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (88981211524 / 1000000000000) (88981212131 / 1000000000000), orderedInterval (-20924601938 / 1000000000000) (-20924601332 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (820992082787469 / 4000000000000) 4 (IntervalRat.scale (711 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-53842616561 / 1000000000000) (-53842614627 / 1000000000000), orderedInterval (14367539638 / 1000000000000) (14367541571 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2229153210472473 / 4000000000000) 4 (IntervalRat.scale (711 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30568218587 / 1000000000000) (-30568151427 / 1000000000000), orderedInterval (14447459954 / 1000000000000) (14447527113 / 1000000000000)))) (orderedInterval (12880829477 / 1000000000000) (12880858576 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1641984165575649 / 4000000000000) 4 (IntervalRat.scale (711 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (10409298193 / 1000000000000) (10409298229 / 1000000000000), orderedInterval (-37992967759 / 1000000000000) (-37992967722 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2813567854437477 / 4000000000000) 4 (IntervalRat.scale (711 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (13367492085 / 1000000000000) (13367492086 / 1000000000000), orderedInterval (26941962406 / 1000000000000) (26941962407 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2072461347229743 / 4000000000000) 4 (IntervalRat.scale (711 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-17953051734 / 1000000000000) (-17953051733 / 1000000000000), orderedInterval (-30089323777 / 1000000000000) (-30089323776 / 1000000000000)))) (orderedInterval (-8325481108 / 1000000000000) (-8325480899 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate484_chunkChecks4_1 :
    compactCertificate484.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3179688664004289 / 4000000000000) 4 (IntervalRat.scale (711 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-21891773105 / 1000000000000) (-21891773104 / 1000000000000), orderedInterval (-17919669253 / 1000000000000) (-17919669252 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1835794106101881 / 4000000000000) 4 (IntervalRat.scale (711 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (32510590389 / 1000000000000) (32510590390 / 1000000000000), orderedInterval (18135652419 / 1000000000000) (18135652420 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3257648856386829 / 4000000000000) 4 (IntervalRat.scale (711 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-27929396215 / 1000000000000) (-27929394188 / 1000000000000), orderedInterval (-1263890633 / 1000000000000) (-1263888606 / 1000000000000)))) (orderedInterval (-5213687010 / 1000000000000) (-5213676004 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3043718132732001 / 4000000000000) 4 (IntervalRat.scale (711 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (28711564986 / 1000000000000) (28711565589 / 1000000000000), orderedInterval (3485441782 / 1000000000000) (3485442385 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2172140879408433 / 4000000000000) 4 (IntervalRat.scale (711 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-10928353826 / 1000000000000) (-10928353825 / 1000000000000), orderedInterval (-32438474553 / 1000000000000) (-32438474552 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2462976248362407 / 4000000000000) 4 (IntervalRat.scale (711 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (22547048350 / 1000000000000) (22547048351 / 1000000000000), orderedInterval (22906216145 / 1000000000000) (22906216146 / 1000000000000)))) (orderedInterval (-17601503757 / 1000000000000) (-17601503192 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2053372817702583 / 4000000000000) 4 (IntervalRat.scale (711 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-31269269897 / 1000000000000) (-31269193582 / 1000000000000), orderedInterval (16228543306 / 1000000000000) (16228619621 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1814217156990243 / 4000000000000) 4 (IntervalRat.scale (711 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (34802460838 / 1000000000000) (34802485012 / 1000000000000), orderedInterval (-13909622703 / 1000000000000) (-13909598529 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (525830844606057 / 800000000000) 4 (IntervalRat.scale (711 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-30995933579 / 1000000000000) (-30995933114 / 1000000000000), orderedInterval (-2770400028 / 1000000000000) (-2770399564 / 1000000000000)))) (orderedInterval (-16110820982 / 1000000000000) (-16110813135 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate484_chunkChecks4_2 :
    compactCertificate484.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1454475789141579 / 4000000000000) 4 (IntervalRat.scale (711 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-868005750 / 1000000000000) (-868005749 / 1000000000000), orderedInterval (41834630520 / 1000000000000) (41834630522 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1232975234333619 / 4000000000000) 4 (IntervalRat.scale (711 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (41531539064 / 1000000000000) (41531539065 / 1000000000000), orderedInterval (18383699391 / 1000000000000) (18383699392 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (771538652770257 / 4000000000000) 4 (IntervalRat.scale (711 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-51440853888 / 1000000000000) (-51440838796 / 1000000000000), orderedInterval (25713662620 / 1000000000000) (25713677712 / 1000000000000)))) (orderedInterval (-1365164219 / 1000000000000) (-1365164100 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (414936053481519 / 4000000000000) 4 (IntervalRat.scale (711 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-58628897979 / 1000000000000) (-58628897978 / 1000000000000), orderedInterval (-51675893590 / 1000000000000) (-51675893589 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1126632101761557 / 4000000000000) 4 (IntervalRat.scale (711 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-14065965957 / 1000000000000) (-14065965808 / 1000000000000), orderedInterval (45438727881 / 1000000000000) (45438728030 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1538319816214389 / 4000000000000) 4 (IntervalRat.scale (711 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (35309659092 / 1000000000000) (35309721576 / 1000000000000), orderedInterval (-20259519029 / 1000000000000) (-20259456545 / 1000000000000)))) (orderedInterval (-3564258225 / 1000000000000) (-3564251590 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (650461347229743 / 4000000000000) 4 (IntervalRat.scale (711 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (2323793328 / 1000000000000) (2323793331 / 1000000000000), orderedInterval (62518849039 / 1000000000000) (62518849042 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2644089263954703 / 4000000000000) 4 (IntervalRat.scale (711 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27200629143 / 1000000000000) (27200701940 / 1000000000000), orderedInterval (-14960731851 / 1000000000000) (-14960659054 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1766129090480577 / 4000000000000) 4 (IntervalRat.scale (711 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (22894441009 / 1000000000000) (22894444745 / 1000000000000), orderedInterval (-30319272557 / 1000000000000) (-30319268821 / 1000000000000)))) (orderedInterval (-36582946167 / 1000000000000) (-36582872936 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate484_chunkChecks4 :
    compactCertificate484.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate484.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate484_chunkChecks4_0
    compactCertificate484_chunkChecks4_1 compactCertificate484_chunkChecks4_2

theorem compactCertificate484_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate484.chunkCheck r b = true :=
  compactCertificate484.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate484_chunkChecks0
    · exact compactCertificate484_chunkChecks1
    · exact compactCertificate484_chunkChecks2
    · exact compactCertificate484_chunkChecks3
    · exact compactCertificate484_chunkChecks4)

theorem compactCertificate484_coefficient0 :
    compactCertificate484.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate484_coefficient1 :
    compactCertificate484.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate484_coefficient2 :
    compactCertificate484.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate484_coefficient3 :
    compactCertificate484.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate484_coefficient4 :
    compactCertificate484.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate484_coefficients : ∀ r : Fin 5,
    compactCertificate484.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate484_coefficient0
  · exact compactCertificate484_coefficient1
  · exact compactCertificate484_coefficient2
  · exact compactCertificate484_coefficient3
  · exact compactCertificate484_coefficient4

theorem compactCertificate484_lower : (1 : ℚ) ≤ compactCertificate484.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate484, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate484_proves {t : ℝ} (ht : t ∈ compactCertificate484.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate484.proves compactCertificate484_states compactCertificate484_chunks
    compactCertificate484_coefficients compactCertificate484_lower ht

end Erdos232
