/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate492 : CompactCertificate where
  left := 363
  right := 364
  center := 727 / 2
  grid := fun i =>
    match i.val with
    | 0 => 116
    | 1 => 85
    | 2 => 138
    | 3 => 25
    | 4 => 67
    | 5 => 181
    | 6 => 134
    | 7 => 229
    | 8 => 169
    | 9 => 259
    | 10 => 149
    | 11 => 265
    | 12 => 248
    | 13 => 177
    | 14 => 201
    | 15 => 167
    | 16 => 148
    | 17 => 214
    | 18 => 118
    | 19 => 100
    | 20 => 63
    | 21 => 34
    | 22 => 92
    | 23 => 125
    | 24 => 53
    | 25 => 215
    | _ => 144
  point := fun i =>
    match i.val with
    | 0 => 727 / 2
    | 1 => 1071009819124027 / 4000000000000
    | 2 => 346342570219291 / 800000000000
    | 3 => 312517994083889 / 4000000000000
    | 4 => 839467291401533 / 4000000000000
    | 5 => 2279316995799561 / 4000000000000
    | 6 => 1678934582803793 / 4000000000000
    | 7 => 2876883024157589 / 4000000000000
    | 8 => 2119099014677951 / 4000000000000
    | 9 => 3251242839284273 / 4000000000000
    | 10 => 1877105928461417 / 4000000000000
    | 11 => 3330957410117053 / 4000000000000
    | 12 => 3112212492962257 / 4000000000000
    | 13 => 2221021686821281 / 4000000000000
    | 14 => 2518401874204599 / 4000000000000
    | 15 => 2099580926117831 / 4000000000000
    | 16 => 1855043422126451 / 4000000000000
    | 17 => 537663887522649 / 800000000000
    | 18 => 1487206608587803 / 4000000000000
    | 19 => 1260721512462083 / 4000000000000
    | 20 => 788900985322049 / 4000000000000
    | 21 => 424273573672383 / 4000000000000
    | 22 => 1151985285486149 / 4000000000000
    | 23 => 1572937421079973 / 4000000000000
    | 24 => 665099014677951 / 4000000000000
    | 25 => 2703590569472671 / 4000000000000
    | _ => 1805873205034289 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-5827073979 / 1000000000000) (-5827073971 / 1000000000000), orderedInterval (41449636030 / 1000000000000) (41449636037 / 1000000000000))
    | 1 => (orderedInterval (-48645728605 / 1000000000000) (-48645728563 / 1000000000000), orderedInterval (-3260587262 / 1000000000000) (-3260587220 / 1000000000000))
    | 2 => (orderedInterval (6621244320 / 1000000000000) (6621244321 / 1000000000000), orderedInterval (37763470977 / 1000000000000) (37763470978 / 1000000000000))
    | 3 => (orderedInterval (-32934592215 / 1000000000000) (-32934592214 / 1000000000000), orderedInterval (-83835053892 / 1000000000000) (-83835053891 / 1000000000000))
    | 4 => (orderedInterval (-9041992945 / 1000000000000) (-9041992943 / 1000000000000), orderedInterval (-54307980043 / 1000000000000) (-54307980042 / 1000000000000))
    | 5 => (orderedInterval (-30582653915 / 1000000000000) (-30582596986 / 1000000000000), orderedInterval (13514361331 / 1000000000000) (13514418260 / 1000000000000))
    | 6 => (orderedInterval (-17103349609 / 1000000000000) (-17103349157 / 1000000000000), orderedInterval (35008933841 / 1000000000000) (35008934292 / 1000000000000))
    | 7 => (orderedInterval (-16335946874 / 1000000000000) (-16335946873 / 1000000000000), orderedInterval (-24854061829 / 1000000000000) (-24854061828 / 1000000000000))
    | 8 => (orderedInterval (12511006131 / 1000000000000) (12511006198 / 1000000000000), orderedInterval (-32340668173 / 1000000000000) (-32340668106 / 1000000000000))
    | 9 => (orderedInterval (2140065666 / 1000000000000) (2140065667 / 1000000000000), orderedInterval (-27905666934 / 1000000000000) (-27905666933 / 1000000000000))
    | 10 => (orderedInterval (-34016892102 / 1000000000000) (-34016862419 / 1000000000000), orderedInterval (14158905190 / 1000000000000) (14158934873 / 1000000000000))
    | 11 => (orderedInterval (-23304135263 / 1000000000000) (-23304135261 / 1000000000000), orderedInterval (-14865720534 / 1000000000000) (-14865720532 / 1000000000000))
    | 12 => (orderedInterval (-7811997690 / 1000000000000) (-7811997687 / 1000000000000), orderedInterval (27522184109 / 1000000000000) (27522184111 / 1000000000000))
    | 13 => (orderedInterval (721341614 / 1000000000000) (721341615 / 1000000000000), orderedInterval (-33853494728 / 1000000000000) (-33853494727 / 1000000000000))
    | 14 => (orderedInterval (27961410495 / 1000000000000) (27961498156 / 1000000000000), orderedInterval (-15165090507 / 1000000000000) (-15165002846 / 1000000000000))
    | 15 => (orderedInterval (-29935224474 / 1000000000000) (-29935224473 / 1000000000000), orderedInterval (-17768484302 / 1000000000000) (-17768484301 / 1000000000000))
    | 16 => (orderedInterval (-14759411181 / 1000000000000) (-14759410993 / 1000000000000), orderedInterval (33999632309 / 1000000000000) (33999632496 / 1000000000000))
    | 17 => (orderedInterval (16458953071 / 1000000000000) (16458953072 / 1000000000000), orderedInterval (25994317070 / 1000000000000) (25994317071 / 1000000000000))
    | 18 => (orderedInterval (39432349094 / 1000000000000) (39432357182 / 1000000000000), orderedInterval (-12596743753 / 1000000000000) (-12596735665 / 1000000000000))
    | 19 => (orderedInterval (43704193835 / 1000000000000) (43704196609 / 1000000000000), orderedInterval (-10547862285 / 1000000000000) (-10547859510 / 1000000000000))
    | 20 => (orderedInterval (-5087918940 / 1000000000000) (-5087918939 / 1000000000000), orderedInterval (-56573363202 / 1000000000000) (-56573363201 / 1000000000000))
    | 21 => (orderedInterval (2979064595 / 1000000000000) (2979064599 / 1000000000000), orderedInterval (77401498016 / 1000000000000) (77401498020 / 1000000000000))
    | 22 => (orderedInterval (-11414927483 / 1000000000000) (-11414927417 / 1000000000000), orderedInterval (45629201925 / 1000000000000) (45629201990 / 1000000000000))
    | 23 => (orderedInterval (-38980694361 / 1000000000000) (-38980694354 / 1000000000000), orderedInterval (-9922223645 / 1000000000000) (-9922223638 / 1000000000000))
    | 24 => (orderedInterval (-32604865466 / 1000000000000) (-32604865465 / 1000000000000), orderedInterval (-52491424594 / 1000000000000) (-52491424593 / 1000000000000))
    | 25 => (orderedInterval (-29030621985 / 1000000000000) (-29030621967 / 1000000000000), orderedInterval (-9933956452 / 1000000000000) (-9933956434 / 1000000000000))
    | _ => (orderedInterval (-5088271286 / 1000000000000) (-5088271283 / 1000000000000), orderedInterval (37210741055 / 1000000000000) (37210741059 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-2374389803 / 1000000000000) (-2374389773 / 1000000000000)
      | 1 => orderedInterval (2201283844 / 1000000000000) (2201287935 / 1000000000000)
      | 2 => orderedInterval (806232285 / 1000000000000) (806232308 / 1000000000000)
      | 3 => orderedInterval (-6213455817 / 1000000000000) (-6213453473 / 1000000000000)
      | 4 => orderedInterval (67741488 / 1000000000000) (67741976 / 1000000000000)
      | 5 => orderedInterval (920364146 / 1000000000000) (920364192 / 1000000000000)
      | 6 => orderedInterval (-8944230114 / 1000000000000) (-8944228573 / 1000000000000)
      | 7 => orderedInterval (3191396452 / 1000000000000) (3191396498 / 1000000000000)
      | _ => orderedInterval (3121286011 / 1000000000000) (3121286114 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (19046063631 / 1000000000000) (19046063663 / 1000000000000)
      | 1 => orderedInterval (-2455385944 / 1000000000000) (-2455379549 / 1000000000000)
      | 2 => orderedInterval (377651652 / 1000000000000) (377651690 / 1000000000000)
      | 3 => orderedInterval (7600644001 / 1000000000000) (7600647139 / 1000000000000)
      | 4 => orderedInterval (-5820621566 / 1000000000000) (-5820620727 / 1000000000000)
      | 5 => orderedInterval (-1548076578 / 1000000000000) (-1548076513 / 1000000000000)
      | 6 => orderedInterval (1578480624 / 1000000000000) (1578482168 / 1000000000000)
      | 7 => orderedInterval (-414576317 / 1000000000000) (-414576276 / 1000000000000)
      | _ => orderedInterval (-7312468951 / 1000000000000) (-7312468805 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (1952052358 / 1000000000000) (1952052395 / 1000000000000)
      | 1 => orderedInterval (-5242422720 / 1000000000000) (-5242412688 / 1000000000000)
      | 2 => orderedInterval (-2615855199 / 1000000000000) (-2615855132 / 1000000000000)
      | 3 => orderedInterval (23467326561 / 1000000000000) (23467330877 / 1000000000000)
      | 4 => orderedInterval (-364781398 / 1000000000000) (-364779947 / 1000000000000)
      | 5 => orderedInterval (-2090362725 / 1000000000000) (-2090362632 / 1000000000000)
      | 6 => orderedInterval (8500352705 / 1000000000000) (8500354260 / 1000000000000)
      | 7 => orderedInterval (-3652906941 / 1000000000000) (-3652906900 / 1000000000000)
      | _ => orderedInterval (-9581841639 / 1000000000000) (-9581841424 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-20166001219 / 1000000000000) (-20166001177 / 1000000000000)
      | 1 => orderedInterval (4088008986 / 1000000000000) (4088024707 / 1000000000000)
      | 2 => orderedInterval (-3511178642 / 1000000000000) (-3511178521 / 1000000000000)
      | 3 => orderedInterval (-32351767216 / 1000000000000) (-32351761067 / 1000000000000)
      | 4 => orderedInterval (15884748120 / 1000000000000) (15884750627 / 1000000000000)
      | 5 => orderedInterval (457468424 / 1000000000000) (457468562 / 1000000000000)
      | 6 => orderedInterval (-2273667531 / 1000000000000) (-2273665962 / 1000000000000)
      | 7 => orderedInterval (-402331323 / 1000000000000) (-402331281 / 1000000000000)
      | _ => orderedInterval (8234148763 / 1000000000000) (8234149096 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-1550340192 / 1000000000000) (-1550340144 / 1000000000000)
      | 1 => orderedInterval (13070860315 / 1000000000000) (13070884999 / 1000000000000)
      | 2 => orderedInterval (9105799305 / 1000000000000) (9105799525 / 1000000000000)
      | 3 => orderedInterval (-107576021599 / 1000000000000) (-107576012338 / 1000000000000)
      | 4 => orderedInterval (1970744591 / 1000000000000) (1970748940 / 1000000000000)
      | 5 => orderedInterval (5656971014 / 1000000000000) (5656971227 / 1000000000000)
      | 6 => orderedInterval (-8300885422 / 1000000000000) (-8300883832 / 1000000000000)
      | 7 => orderedInterval (4195369030 / 1000000000000) (4195369074 / 1000000000000)
      | _ => orderedInterval (30466301470 / 1000000000000) (30466302006 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-7223771508 / 1000000000000) (-7223762796 / 1000000000000)
    | 1 => orderedInterval (11051710552 / 1000000000000) (11051722790 / 1000000000000)
    | 2 => orderedInterval (10371561002 / 1000000000000) (10371578809 / 1000000000000)
    | 3 => orderedInterval (-30040571638 / 1000000000000) (-30040545016 / 1000000000000)
    | _ => orderedInterval (-52961201488 / 1000000000000) (-52961160543 / 1000000000000)

theorem compactCertificate492_stateChecks0 :
    compactCertificate492.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 116 12 (727 / 2)) (orderedInterval (-5827073979 / 1000000000000) (-5827073971 / 1000000000000), orderedInterval (41449636030 / 1000000000000) (41449636037 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 85 12 (1071009819124027 / 4000000000000)) (orderedInterval (-48645728605 / 1000000000000) (-48645728563 / 1000000000000), orderedInterval (-3260587262 / 1000000000000) (-3260587220 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 138 12 (346342570219291 / 800000000000)) (orderedInterval (6621244320 / 1000000000000) (6621244321 / 1000000000000), orderedInterval (37763470977 / 1000000000000) (37763470978 / 1000000000000))) = true
  rfl'

theorem compactCertificate492_stateChecks1 :
    compactCertificate492.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 25 12 (312517994083889 / 4000000000000)) (orderedInterval (-32934592215 / 1000000000000) (-32934592214 / 1000000000000), orderedInterval (-83835053892 / 1000000000000) (-83835053891 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (839467291401533 / 4000000000000)) (orderedInterval (-9041992945 / 1000000000000) (-9041992943 / 1000000000000), orderedInterval (-54307980043 / 1000000000000) (-54307980042 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 181 12 (2279316995799561 / 4000000000000)) (orderedInterval (-30582653915 / 1000000000000) (-30582596986 / 1000000000000), orderedInterval (13514361331 / 1000000000000) (13514418260 / 1000000000000))) = true
  rfl'

theorem compactCertificate492_stateChecks2 :
    compactCertificate492.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 134 12 (1678934582803793 / 4000000000000)) (orderedInterval (-17103349609 / 1000000000000) (-17103349157 / 1000000000000), orderedInterval (35008933841 / 1000000000000) (35008934292 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 229 12 (2876883024157589 / 4000000000000)) (orderedInterval (-16335946874 / 1000000000000) (-16335946873 / 1000000000000), orderedInterval (-24854061829 / 1000000000000) (-24854061828 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 169 12 (2119099014677951 / 4000000000000)) (orderedInterval (12511006131 / 1000000000000) (12511006198 / 1000000000000), orderedInterval (-32340668173 / 1000000000000) (-32340668106 / 1000000000000))) = true
  rfl'

theorem compactCertificate492_stateChecks3 :
    compactCertificate492.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 259 12 (3251242839284273 / 4000000000000)) (orderedInterval (2140065666 / 1000000000000) (2140065667 / 1000000000000), orderedInterval (-27905666934 / 1000000000000) (-27905666933 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 149 12 (1877105928461417 / 4000000000000)) (orderedInterval (-34016892102 / 1000000000000) (-34016862419 / 1000000000000), orderedInterval (14158905190 / 1000000000000) (14158934873 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 265 12 (3330957410117053 / 4000000000000)) (orderedInterval (-23304135263 / 1000000000000) (-23304135261 / 1000000000000), orderedInterval (-14865720534 / 1000000000000) (-14865720532 / 1000000000000))) = true
  rfl'

theorem compactCertificate492_stateChecks4 :
    compactCertificate492.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 248 12 (3112212492962257 / 4000000000000)) (orderedInterval (-7811997690 / 1000000000000) (-7811997687 / 1000000000000), orderedInterval (27522184109 / 1000000000000) (27522184111 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 177 12 (2221021686821281 / 4000000000000)) (orderedInterval (721341614 / 1000000000000) (721341615 / 1000000000000), orderedInterval (-33853494728 / 1000000000000) (-33853494727 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 201 12 (2518401874204599 / 4000000000000)) (orderedInterval (27961410495 / 1000000000000) (27961498156 / 1000000000000), orderedInterval (-15165090507 / 1000000000000) (-15165002846 / 1000000000000))) = true
  rfl'

theorem compactCertificate492_stateChecks5 :
    compactCertificate492.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 167 12 (2099580926117831 / 4000000000000)) (orderedInterval (-29935224474 / 1000000000000) (-29935224473 / 1000000000000), orderedInterval (-17768484302 / 1000000000000) (-17768484301 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 148 12 (1855043422126451 / 4000000000000)) (orderedInterval (-14759411181 / 1000000000000) (-14759410993 / 1000000000000), orderedInterval (33999632309 / 1000000000000) (33999632496 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 214 12 (537663887522649 / 800000000000)) (orderedInterval (16458953071 / 1000000000000) (16458953072 / 1000000000000), orderedInterval (25994317070 / 1000000000000) (25994317071 / 1000000000000))) = true
  rfl'

theorem compactCertificate492_stateChecks6 :
    compactCertificate492.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 118 12 (1487206608587803 / 4000000000000)) (orderedInterval (39432349094 / 1000000000000) (39432357182 / 1000000000000), orderedInterval (-12596743753 / 1000000000000) (-12596735665 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 100 12 (1260721512462083 / 4000000000000)) (orderedInterval (43704193835 / 1000000000000) (43704196609 / 1000000000000), orderedInterval (-10547862285 / 1000000000000) (-10547859510 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (788900985322049 / 4000000000000)) (orderedInterval (-5087918940 / 1000000000000) (-5087918939 / 1000000000000), orderedInterval (-56573363202 / 1000000000000) (-56573363201 / 1000000000000))) = true
  rfl'

theorem compactCertificate492_stateChecks7 :
    compactCertificate492.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (424273573672383 / 4000000000000)) (orderedInterval (2979064595 / 1000000000000) (2979064599 / 1000000000000), orderedInterval (77401498016 / 1000000000000) (77401498020 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 92 12 (1151985285486149 / 4000000000000)) (orderedInterval (-11414927483 / 1000000000000) (-11414927417 / 1000000000000), orderedInterval (45629201925 / 1000000000000) (45629201990 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 125 12 (1572937421079973 / 4000000000000)) (orderedInterval (-38980694361 / 1000000000000) (-38980694354 / 1000000000000), orderedInterval (-9922223645 / 1000000000000) (-9922223638 / 1000000000000))) = true
  rfl'

theorem compactCertificate492_stateChecks8 :
    compactCertificate492.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 53 12 (665099014677951 / 4000000000000)) (orderedInterval (-32604865466 / 1000000000000) (-32604865465 / 1000000000000), orderedInterval (-52491424594 / 1000000000000) (-52491424593 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 215 12 (2703590569472671 / 4000000000000)) (orderedInterval (-29030621985 / 1000000000000) (-29030621967 / 1000000000000), orderedInterval (-9933956452 / 1000000000000) (-9933956434 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 144 12 (1805873205034289 / 4000000000000)) (orderedInterval (-5088271286 / 1000000000000) (-5088271283 / 1000000000000), orderedInterval (37210741055 / 1000000000000) (37210741059 / 1000000000000))) = true
  rfl'

theorem compactCertificate492_states : ∀ j,
    BesselStateValid (compactCertificate492.point j) (compactCertificate492.state j) :=
  compactCertificate492.statesValid_of_checks3 compactCertificate492_stateChecks0
    compactCertificate492_stateChecks1 compactCertificate492_stateChecks2
    compactCertificate492_stateChecks3 compactCertificate492_stateChecks4
    compactCertificate492_stateChecks5 compactCertificate492_stateChecks6
    compactCertificate492_stateChecks7 compactCertificate492_stateChecks8

theorem compactCertificate492_chunkChecks0_0 :
    compactCertificate492.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (727 / 2) 0 (IntervalRat.scale (727 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-5827073979 / 1000000000000) (-5827073971 / 1000000000000), orderedInterval (41449636030 / 1000000000000) (41449636037 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1071009819124027 / 4000000000000) 0 (IntervalRat.scale (727 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-48645728605 / 1000000000000) (-48645728563 / 1000000000000), orderedInterval (-3260587262 / 1000000000000) (-3260587220 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (346342570219291 / 800000000000) 0 (IntervalRat.scale (727 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (6621244320 / 1000000000000) (6621244321 / 1000000000000), orderedInterval (37763470977 / 1000000000000) (37763470978 / 1000000000000)))) (orderedInterval (-2374389803 / 1000000000000) (-2374389773 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (312517994083889 / 4000000000000) 0 (IntervalRat.scale (727 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-32934592215 / 1000000000000) (-32934592214 / 1000000000000), orderedInterval (-83835053892 / 1000000000000) (-83835053891 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (839467291401533 / 4000000000000) 0 (IntervalRat.scale (727 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-9041992945 / 1000000000000) (-9041992943 / 1000000000000), orderedInterval (-54307980043 / 1000000000000) (-54307980042 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2279316995799561 / 4000000000000) 0 (IntervalRat.scale (727 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30582653915 / 1000000000000) (-30582596986 / 1000000000000), orderedInterval (13514361331 / 1000000000000) (13514418260 / 1000000000000)))) (orderedInterval (2201283844 / 1000000000000) (2201287935 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1678934582803793 / 4000000000000) 0 (IntervalRat.scale (727 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-17103349609 / 1000000000000) (-17103349157 / 1000000000000), orderedInterval (35008933841 / 1000000000000) (35008934292 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2876883024157589 / 4000000000000) 0 (IntervalRat.scale (727 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-16335946874 / 1000000000000) (-16335946873 / 1000000000000), orderedInterval (-24854061829 / 1000000000000) (-24854061828 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2119099014677951 / 4000000000000) 0 (IntervalRat.scale (727 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (12511006131 / 1000000000000) (12511006198 / 1000000000000), orderedInterval (-32340668173 / 1000000000000) (-32340668106 / 1000000000000)))) (orderedInterval (806232285 / 1000000000000) (806232308 / 1000000000000))) = true
  rfl'

theorem compactCertificate492_chunkChecks0_1 :
    compactCertificate492.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3251242839284273 / 4000000000000) 0 (IntervalRat.scale (727 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (2140065666 / 1000000000000) (2140065667 / 1000000000000), orderedInterval (-27905666934 / 1000000000000) (-27905666933 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1877105928461417 / 4000000000000) 0 (IntervalRat.scale (727 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-34016892102 / 1000000000000) (-34016862419 / 1000000000000), orderedInterval (14158905190 / 1000000000000) (14158934873 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3330957410117053 / 4000000000000) 0 (IntervalRat.scale (727 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-23304135263 / 1000000000000) (-23304135261 / 1000000000000), orderedInterval (-14865720534 / 1000000000000) (-14865720532 / 1000000000000)))) (orderedInterval (-6213455817 / 1000000000000) (-6213453473 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3112212492962257 / 4000000000000) 0 (IntervalRat.scale (727 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-7811997690 / 1000000000000) (-7811997687 / 1000000000000), orderedInterval (27522184109 / 1000000000000) (27522184111 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2221021686821281 / 4000000000000) 0 (IntervalRat.scale (727 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (721341614 / 1000000000000) (721341615 / 1000000000000), orderedInterval (-33853494728 / 1000000000000) (-33853494727 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2518401874204599 / 4000000000000) 0 (IntervalRat.scale (727 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (27961410495 / 1000000000000) (27961498156 / 1000000000000), orderedInterval (-15165090507 / 1000000000000) (-15165002846 / 1000000000000)))) (orderedInterval (67741488 / 1000000000000) (67741976 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2099580926117831 / 4000000000000) 0 (IntervalRat.scale (727 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-29935224474 / 1000000000000) (-29935224473 / 1000000000000), orderedInterval (-17768484302 / 1000000000000) (-17768484301 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1855043422126451 / 4000000000000) 0 (IntervalRat.scale (727 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-14759411181 / 1000000000000) (-14759410993 / 1000000000000), orderedInterval (33999632309 / 1000000000000) (33999632496 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (537663887522649 / 800000000000) 0 (IntervalRat.scale (727 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16458953071 / 1000000000000) (16458953072 / 1000000000000), orderedInterval (25994317070 / 1000000000000) (25994317071 / 1000000000000)))) (orderedInterval (920364146 / 1000000000000) (920364192 / 1000000000000))) = true
  rfl'

theorem compactCertificate492_chunkChecks0_2 :
    compactCertificate492.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1487206608587803 / 4000000000000) 0 (IntervalRat.scale (727 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (39432349094 / 1000000000000) (39432357182 / 1000000000000), orderedInterval (-12596743753 / 1000000000000) (-12596735665 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1260721512462083 / 4000000000000) 0 (IntervalRat.scale (727 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (43704193835 / 1000000000000) (43704196609 / 1000000000000), orderedInterval (-10547862285 / 1000000000000) (-10547859510 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (788900985322049 / 4000000000000) 0 (IntervalRat.scale (727 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-5087918940 / 1000000000000) (-5087918939 / 1000000000000), orderedInterval (-56573363202 / 1000000000000) (-56573363201 / 1000000000000)))) (orderedInterval (-8944230114 / 1000000000000) (-8944228573 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (424273573672383 / 4000000000000) 0 (IntervalRat.scale (727 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (2979064595 / 1000000000000) (2979064599 / 1000000000000), orderedInterval (77401498016 / 1000000000000) (77401498020 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1151985285486149 / 4000000000000) 0 (IntervalRat.scale (727 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-11414927483 / 1000000000000) (-11414927417 / 1000000000000), orderedInterval (45629201925 / 1000000000000) (45629201990 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1572937421079973 / 4000000000000) 0 (IntervalRat.scale (727 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-38980694361 / 1000000000000) (-38980694354 / 1000000000000), orderedInterval (-9922223645 / 1000000000000) (-9922223638 / 1000000000000)))) (orderedInterval (3191396452 / 1000000000000) (3191396498 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (665099014677951 / 4000000000000) 0 (IntervalRat.scale (727 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-32604865466 / 1000000000000) (-32604865465 / 1000000000000), orderedInterval (-52491424594 / 1000000000000) (-52491424593 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2703590569472671 / 4000000000000) 0 (IntervalRat.scale (727 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-29030621985 / 1000000000000) (-29030621967 / 1000000000000), orderedInterval (-9933956452 / 1000000000000) (-9933956434 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1805873205034289 / 4000000000000) 0 (IntervalRat.scale (727 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-5088271286 / 1000000000000) (-5088271283 / 1000000000000), orderedInterval (37210741055 / 1000000000000) (37210741059 / 1000000000000)))) (orderedInterval (3121286011 / 1000000000000) (3121286114 / 1000000000000))) = true
  rfl'

theorem compactCertificate492_chunkChecks0 :
    compactCertificate492.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate492.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate492_chunkChecks0_0
    compactCertificate492_chunkChecks0_1 compactCertificate492_chunkChecks0_2

theorem compactCertificate492_chunkChecks1_0 :
    compactCertificate492.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (727 / 2) 1 (IntervalRat.scale (727 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-5827073979 / 1000000000000) (-5827073971 / 1000000000000), orderedInterval (41449636030 / 1000000000000) (41449636037 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1071009819124027 / 4000000000000) 1 (IntervalRat.scale (727 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-48645728605 / 1000000000000) (-48645728563 / 1000000000000), orderedInterval (-3260587262 / 1000000000000) (-3260587220 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (346342570219291 / 800000000000) 1 (IntervalRat.scale (727 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (6621244320 / 1000000000000) (6621244321 / 1000000000000), orderedInterval (37763470977 / 1000000000000) (37763470978 / 1000000000000)))) (orderedInterval (19046063631 / 1000000000000) (19046063663 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (312517994083889 / 4000000000000) 1 (IntervalRat.scale (727 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-32934592215 / 1000000000000) (-32934592214 / 1000000000000), orderedInterval (-83835053892 / 1000000000000) (-83835053891 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (839467291401533 / 4000000000000) 1 (IntervalRat.scale (727 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-9041992945 / 1000000000000) (-9041992943 / 1000000000000), orderedInterval (-54307980043 / 1000000000000) (-54307980042 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2279316995799561 / 4000000000000) 1 (IntervalRat.scale (727 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30582653915 / 1000000000000) (-30582596986 / 1000000000000), orderedInterval (13514361331 / 1000000000000) (13514418260 / 1000000000000)))) (orderedInterval (-2455385944 / 1000000000000) (-2455379549 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1678934582803793 / 4000000000000) 1 (IntervalRat.scale (727 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-17103349609 / 1000000000000) (-17103349157 / 1000000000000), orderedInterval (35008933841 / 1000000000000) (35008934292 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2876883024157589 / 4000000000000) 1 (IntervalRat.scale (727 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-16335946874 / 1000000000000) (-16335946873 / 1000000000000), orderedInterval (-24854061829 / 1000000000000) (-24854061828 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2119099014677951 / 4000000000000) 1 (IntervalRat.scale (727 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (12511006131 / 1000000000000) (12511006198 / 1000000000000), orderedInterval (-32340668173 / 1000000000000) (-32340668106 / 1000000000000)))) (orderedInterval (377651652 / 1000000000000) (377651690 / 1000000000000))) = true
  rfl'

theorem compactCertificate492_chunkChecks1_1 :
    compactCertificate492.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3251242839284273 / 4000000000000) 1 (IntervalRat.scale (727 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (2140065666 / 1000000000000) (2140065667 / 1000000000000), orderedInterval (-27905666934 / 1000000000000) (-27905666933 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1877105928461417 / 4000000000000) 1 (IntervalRat.scale (727 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-34016892102 / 1000000000000) (-34016862419 / 1000000000000), orderedInterval (14158905190 / 1000000000000) (14158934873 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3330957410117053 / 4000000000000) 1 (IntervalRat.scale (727 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-23304135263 / 1000000000000) (-23304135261 / 1000000000000), orderedInterval (-14865720534 / 1000000000000) (-14865720532 / 1000000000000)))) (orderedInterval (7600644001 / 1000000000000) (7600647139 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3112212492962257 / 4000000000000) 1 (IntervalRat.scale (727 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-7811997690 / 1000000000000) (-7811997687 / 1000000000000), orderedInterval (27522184109 / 1000000000000) (27522184111 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2221021686821281 / 4000000000000) 1 (IntervalRat.scale (727 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (721341614 / 1000000000000) (721341615 / 1000000000000), orderedInterval (-33853494728 / 1000000000000) (-33853494727 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2518401874204599 / 4000000000000) 1 (IntervalRat.scale (727 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (27961410495 / 1000000000000) (27961498156 / 1000000000000), orderedInterval (-15165090507 / 1000000000000) (-15165002846 / 1000000000000)))) (orderedInterval (-5820621566 / 1000000000000) (-5820620727 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2099580926117831 / 4000000000000) 1 (IntervalRat.scale (727 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-29935224474 / 1000000000000) (-29935224473 / 1000000000000), orderedInterval (-17768484302 / 1000000000000) (-17768484301 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1855043422126451 / 4000000000000) 1 (IntervalRat.scale (727 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-14759411181 / 1000000000000) (-14759410993 / 1000000000000), orderedInterval (33999632309 / 1000000000000) (33999632496 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (537663887522649 / 800000000000) 1 (IntervalRat.scale (727 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16458953071 / 1000000000000) (16458953072 / 1000000000000), orderedInterval (25994317070 / 1000000000000) (25994317071 / 1000000000000)))) (orderedInterval (-1548076578 / 1000000000000) (-1548076513 / 1000000000000))) = true
  rfl'

theorem compactCertificate492_chunkChecks1_2 :
    compactCertificate492.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1487206608587803 / 4000000000000) 1 (IntervalRat.scale (727 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (39432349094 / 1000000000000) (39432357182 / 1000000000000), orderedInterval (-12596743753 / 1000000000000) (-12596735665 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1260721512462083 / 4000000000000) 1 (IntervalRat.scale (727 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (43704193835 / 1000000000000) (43704196609 / 1000000000000), orderedInterval (-10547862285 / 1000000000000) (-10547859510 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (788900985322049 / 4000000000000) 1 (IntervalRat.scale (727 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-5087918940 / 1000000000000) (-5087918939 / 1000000000000), orderedInterval (-56573363202 / 1000000000000) (-56573363201 / 1000000000000)))) (orderedInterval (1578480624 / 1000000000000) (1578482168 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (424273573672383 / 4000000000000) 1 (IntervalRat.scale (727 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (2979064595 / 1000000000000) (2979064599 / 1000000000000), orderedInterval (77401498016 / 1000000000000) (77401498020 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1151985285486149 / 4000000000000) 1 (IntervalRat.scale (727 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-11414927483 / 1000000000000) (-11414927417 / 1000000000000), orderedInterval (45629201925 / 1000000000000) (45629201990 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1572937421079973 / 4000000000000) 1 (IntervalRat.scale (727 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-38980694361 / 1000000000000) (-38980694354 / 1000000000000), orderedInterval (-9922223645 / 1000000000000) (-9922223638 / 1000000000000)))) (orderedInterval (-414576317 / 1000000000000) (-414576276 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (665099014677951 / 4000000000000) 1 (IntervalRat.scale (727 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-32604865466 / 1000000000000) (-32604865465 / 1000000000000), orderedInterval (-52491424594 / 1000000000000) (-52491424593 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2703590569472671 / 4000000000000) 1 (IntervalRat.scale (727 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-29030621985 / 1000000000000) (-29030621967 / 1000000000000), orderedInterval (-9933956452 / 1000000000000) (-9933956434 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1805873205034289 / 4000000000000) 1 (IntervalRat.scale (727 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-5088271286 / 1000000000000) (-5088271283 / 1000000000000), orderedInterval (37210741055 / 1000000000000) (37210741059 / 1000000000000)))) (orderedInterval (-7312468951 / 1000000000000) (-7312468805 / 1000000000000))) = true
  rfl'

theorem compactCertificate492_chunkChecks1 :
    compactCertificate492.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate492.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate492_chunkChecks1_0
    compactCertificate492_chunkChecks1_1 compactCertificate492_chunkChecks1_2

theorem compactCertificate492_chunkChecks2_0 :
    compactCertificate492.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (727 / 2) 2 (IntervalRat.scale (727 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-5827073979 / 1000000000000) (-5827073971 / 1000000000000), orderedInterval (41449636030 / 1000000000000) (41449636037 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1071009819124027 / 4000000000000) 2 (IntervalRat.scale (727 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-48645728605 / 1000000000000) (-48645728563 / 1000000000000), orderedInterval (-3260587262 / 1000000000000) (-3260587220 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (346342570219291 / 800000000000) 2 (IntervalRat.scale (727 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (6621244320 / 1000000000000) (6621244321 / 1000000000000), orderedInterval (37763470977 / 1000000000000) (37763470978 / 1000000000000)))) (orderedInterval (1952052358 / 1000000000000) (1952052395 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (312517994083889 / 4000000000000) 2 (IntervalRat.scale (727 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-32934592215 / 1000000000000) (-32934592214 / 1000000000000), orderedInterval (-83835053892 / 1000000000000) (-83835053891 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (839467291401533 / 4000000000000) 2 (IntervalRat.scale (727 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-9041992945 / 1000000000000) (-9041992943 / 1000000000000), orderedInterval (-54307980043 / 1000000000000) (-54307980042 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2279316995799561 / 4000000000000) 2 (IntervalRat.scale (727 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30582653915 / 1000000000000) (-30582596986 / 1000000000000), orderedInterval (13514361331 / 1000000000000) (13514418260 / 1000000000000)))) (orderedInterval (-5242422720 / 1000000000000) (-5242412688 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1678934582803793 / 4000000000000) 2 (IntervalRat.scale (727 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-17103349609 / 1000000000000) (-17103349157 / 1000000000000), orderedInterval (35008933841 / 1000000000000) (35008934292 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2876883024157589 / 4000000000000) 2 (IntervalRat.scale (727 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-16335946874 / 1000000000000) (-16335946873 / 1000000000000), orderedInterval (-24854061829 / 1000000000000) (-24854061828 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2119099014677951 / 4000000000000) 2 (IntervalRat.scale (727 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (12511006131 / 1000000000000) (12511006198 / 1000000000000), orderedInterval (-32340668173 / 1000000000000) (-32340668106 / 1000000000000)))) (orderedInterval (-2615855199 / 1000000000000) (-2615855132 / 1000000000000))) = true
  rfl'

theorem compactCertificate492_chunkChecks2_1 :
    compactCertificate492.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3251242839284273 / 4000000000000) 2 (IntervalRat.scale (727 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (2140065666 / 1000000000000) (2140065667 / 1000000000000), orderedInterval (-27905666934 / 1000000000000) (-27905666933 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1877105928461417 / 4000000000000) 2 (IntervalRat.scale (727 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-34016892102 / 1000000000000) (-34016862419 / 1000000000000), orderedInterval (14158905190 / 1000000000000) (14158934873 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3330957410117053 / 4000000000000) 2 (IntervalRat.scale (727 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-23304135263 / 1000000000000) (-23304135261 / 1000000000000), orderedInterval (-14865720534 / 1000000000000) (-14865720532 / 1000000000000)))) (orderedInterval (23467326561 / 1000000000000) (23467330877 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3112212492962257 / 4000000000000) 2 (IntervalRat.scale (727 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-7811997690 / 1000000000000) (-7811997687 / 1000000000000), orderedInterval (27522184109 / 1000000000000) (27522184111 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2221021686821281 / 4000000000000) 2 (IntervalRat.scale (727 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (721341614 / 1000000000000) (721341615 / 1000000000000), orderedInterval (-33853494728 / 1000000000000) (-33853494727 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2518401874204599 / 4000000000000) 2 (IntervalRat.scale (727 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (27961410495 / 1000000000000) (27961498156 / 1000000000000), orderedInterval (-15165090507 / 1000000000000) (-15165002846 / 1000000000000)))) (orderedInterval (-364781398 / 1000000000000) (-364779947 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2099580926117831 / 4000000000000) 2 (IntervalRat.scale (727 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-29935224474 / 1000000000000) (-29935224473 / 1000000000000), orderedInterval (-17768484302 / 1000000000000) (-17768484301 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1855043422126451 / 4000000000000) 2 (IntervalRat.scale (727 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-14759411181 / 1000000000000) (-14759410993 / 1000000000000), orderedInterval (33999632309 / 1000000000000) (33999632496 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (537663887522649 / 800000000000) 2 (IntervalRat.scale (727 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16458953071 / 1000000000000) (16458953072 / 1000000000000), orderedInterval (25994317070 / 1000000000000) (25994317071 / 1000000000000)))) (orderedInterval (-2090362725 / 1000000000000) (-2090362632 / 1000000000000))) = true
  rfl'

theorem compactCertificate492_chunkChecks2_2 :
    compactCertificate492.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1487206608587803 / 4000000000000) 2 (IntervalRat.scale (727 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (39432349094 / 1000000000000) (39432357182 / 1000000000000), orderedInterval (-12596743753 / 1000000000000) (-12596735665 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1260721512462083 / 4000000000000) 2 (IntervalRat.scale (727 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (43704193835 / 1000000000000) (43704196609 / 1000000000000), orderedInterval (-10547862285 / 1000000000000) (-10547859510 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (788900985322049 / 4000000000000) 2 (IntervalRat.scale (727 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-5087918940 / 1000000000000) (-5087918939 / 1000000000000), orderedInterval (-56573363202 / 1000000000000) (-56573363201 / 1000000000000)))) (orderedInterval (8500352705 / 1000000000000) (8500354260 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (424273573672383 / 4000000000000) 2 (IntervalRat.scale (727 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (2979064595 / 1000000000000) (2979064599 / 1000000000000), orderedInterval (77401498016 / 1000000000000) (77401498020 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1151985285486149 / 4000000000000) 2 (IntervalRat.scale (727 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-11414927483 / 1000000000000) (-11414927417 / 1000000000000), orderedInterval (45629201925 / 1000000000000) (45629201990 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1572937421079973 / 4000000000000) 2 (IntervalRat.scale (727 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-38980694361 / 1000000000000) (-38980694354 / 1000000000000), orderedInterval (-9922223645 / 1000000000000) (-9922223638 / 1000000000000)))) (orderedInterval (-3652906941 / 1000000000000) (-3652906900 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (665099014677951 / 4000000000000) 2 (IntervalRat.scale (727 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-32604865466 / 1000000000000) (-32604865465 / 1000000000000), orderedInterval (-52491424594 / 1000000000000) (-52491424593 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2703590569472671 / 4000000000000) 2 (IntervalRat.scale (727 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-29030621985 / 1000000000000) (-29030621967 / 1000000000000), orderedInterval (-9933956452 / 1000000000000) (-9933956434 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1805873205034289 / 4000000000000) 2 (IntervalRat.scale (727 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-5088271286 / 1000000000000) (-5088271283 / 1000000000000), orderedInterval (37210741055 / 1000000000000) (37210741059 / 1000000000000)))) (orderedInterval (-9581841639 / 1000000000000) (-9581841424 / 1000000000000))) = true
  rfl'

theorem compactCertificate492_chunkChecks2 :
    compactCertificate492.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate492.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate492_chunkChecks2_0
    compactCertificate492_chunkChecks2_1 compactCertificate492_chunkChecks2_2

theorem compactCertificate492_chunkChecks3_0 :
    compactCertificate492.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (727 / 2) 3 (IntervalRat.scale (727 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-5827073979 / 1000000000000) (-5827073971 / 1000000000000), orderedInterval (41449636030 / 1000000000000) (41449636037 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1071009819124027 / 4000000000000) 3 (IntervalRat.scale (727 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-48645728605 / 1000000000000) (-48645728563 / 1000000000000), orderedInterval (-3260587262 / 1000000000000) (-3260587220 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (346342570219291 / 800000000000) 3 (IntervalRat.scale (727 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (6621244320 / 1000000000000) (6621244321 / 1000000000000), orderedInterval (37763470977 / 1000000000000) (37763470978 / 1000000000000)))) (orderedInterval (-20166001219 / 1000000000000) (-20166001177 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (312517994083889 / 4000000000000) 3 (IntervalRat.scale (727 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-32934592215 / 1000000000000) (-32934592214 / 1000000000000), orderedInterval (-83835053892 / 1000000000000) (-83835053891 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (839467291401533 / 4000000000000) 3 (IntervalRat.scale (727 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-9041992945 / 1000000000000) (-9041992943 / 1000000000000), orderedInterval (-54307980043 / 1000000000000) (-54307980042 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2279316995799561 / 4000000000000) 3 (IntervalRat.scale (727 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30582653915 / 1000000000000) (-30582596986 / 1000000000000), orderedInterval (13514361331 / 1000000000000) (13514418260 / 1000000000000)))) (orderedInterval (4088008986 / 1000000000000) (4088024707 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1678934582803793 / 4000000000000) 3 (IntervalRat.scale (727 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-17103349609 / 1000000000000) (-17103349157 / 1000000000000), orderedInterval (35008933841 / 1000000000000) (35008934292 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2876883024157589 / 4000000000000) 3 (IntervalRat.scale (727 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-16335946874 / 1000000000000) (-16335946873 / 1000000000000), orderedInterval (-24854061829 / 1000000000000) (-24854061828 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2119099014677951 / 4000000000000) 3 (IntervalRat.scale (727 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (12511006131 / 1000000000000) (12511006198 / 1000000000000), orderedInterval (-32340668173 / 1000000000000) (-32340668106 / 1000000000000)))) (orderedInterval (-3511178642 / 1000000000000) (-3511178521 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate492_chunkChecks3_1 :
    compactCertificate492.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3251242839284273 / 4000000000000) 3 (IntervalRat.scale (727 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (2140065666 / 1000000000000) (2140065667 / 1000000000000), orderedInterval (-27905666934 / 1000000000000) (-27905666933 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1877105928461417 / 4000000000000) 3 (IntervalRat.scale (727 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-34016892102 / 1000000000000) (-34016862419 / 1000000000000), orderedInterval (14158905190 / 1000000000000) (14158934873 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3330957410117053 / 4000000000000) 3 (IntervalRat.scale (727 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-23304135263 / 1000000000000) (-23304135261 / 1000000000000), orderedInterval (-14865720534 / 1000000000000) (-14865720532 / 1000000000000)))) (orderedInterval (-32351767216 / 1000000000000) (-32351761067 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3112212492962257 / 4000000000000) 3 (IntervalRat.scale (727 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-7811997690 / 1000000000000) (-7811997687 / 1000000000000), orderedInterval (27522184109 / 1000000000000) (27522184111 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2221021686821281 / 4000000000000) 3 (IntervalRat.scale (727 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (721341614 / 1000000000000) (721341615 / 1000000000000), orderedInterval (-33853494728 / 1000000000000) (-33853494727 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2518401874204599 / 4000000000000) 3 (IntervalRat.scale (727 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (27961410495 / 1000000000000) (27961498156 / 1000000000000), orderedInterval (-15165090507 / 1000000000000) (-15165002846 / 1000000000000)))) (orderedInterval (15884748120 / 1000000000000) (15884750627 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2099580926117831 / 4000000000000) 3 (IntervalRat.scale (727 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-29935224474 / 1000000000000) (-29935224473 / 1000000000000), orderedInterval (-17768484302 / 1000000000000) (-17768484301 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1855043422126451 / 4000000000000) 3 (IntervalRat.scale (727 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-14759411181 / 1000000000000) (-14759410993 / 1000000000000), orderedInterval (33999632309 / 1000000000000) (33999632496 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (537663887522649 / 800000000000) 3 (IntervalRat.scale (727 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16458953071 / 1000000000000) (16458953072 / 1000000000000), orderedInterval (25994317070 / 1000000000000) (25994317071 / 1000000000000)))) (orderedInterval (457468424 / 1000000000000) (457468562 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate492_chunkChecks3_2 :
    compactCertificate492.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1487206608587803 / 4000000000000) 3 (IntervalRat.scale (727 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (39432349094 / 1000000000000) (39432357182 / 1000000000000), orderedInterval (-12596743753 / 1000000000000) (-12596735665 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1260721512462083 / 4000000000000) 3 (IntervalRat.scale (727 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (43704193835 / 1000000000000) (43704196609 / 1000000000000), orderedInterval (-10547862285 / 1000000000000) (-10547859510 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (788900985322049 / 4000000000000) 3 (IntervalRat.scale (727 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-5087918940 / 1000000000000) (-5087918939 / 1000000000000), orderedInterval (-56573363202 / 1000000000000) (-56573363201 / 1000000000000)))) (orderedInterval (-2273667531 / 1000000000000) (-2273665962 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (424273573672383 / 4000000000000) 3 (IntervalRat.scale (727 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (2979064595 / 1000000000000) (2979064599 / 1000000000000), orderedInterval (77401498016 / 1000000000000) (77401498020 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1151985285486149 / 4000000000000) 3 (IntervalRat.scale (727 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-11414927483 / 1000000000000) (-11414927417 / 1000000000000), orderedInterval (45629201925 / 1000000000000) (45629201990 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1572937421079973 / 4000000000000) 3 (IntervalRat.scale (727 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-38980694361 / 1000000000000) (-38980694354 / 1000000000000), orderedInterval (-9922223645 / 1000000000000) (-9922223638 / 1000000000000)))) (orderedInterval (-402331323 / 1000000000000) (-402331281 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (665099014677951 / 4000000000000) 3 (IntervalRat.scale (727 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-32604865466 / 1000000000000) (-32604865465 / 1000000000000), orderedInterval (-52491424594 / 1000000000000) (-52491424593 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2703590569472671 / 4000000000000) 3 (IntervalRat.scale (727 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-29030621985 / 1000000000000) (-29030621967 / 1000000000000), orderedInterval (-9933956452 / 1000000000000) (-9933956434 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1805873205034289 / 4000000000000) 3 (IntervalRat.scale (727 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-5088271286 / 1000000000000) (-5088271283 / 1000000000000), orderedInterval (37210741055 / 1000000000000) (37210741059 / 1000000000000)))) (orderedInterval (8234148763 / 1000000000000) (8234149096 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate492_chunkChecks3 :
    compactCertificate492.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate492.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate492_chunkChecks3_0
    compactCertificate492_chunkChecks3_1 compactCertificate492_chunkChecks3_2

theorem compactCertificate492_chunkChecks4_0 :
    compactCertificate492.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (727 / 2) 4 (IntervalRat.scale (727 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-5827073979 / 1000000000000) (-5827073971 / 1000000000000), orderedInterval (41449636030 / 1000000000000) (41449636037 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1071009819124027 / 4000000000000) 4 (IntervalRat.scale (727 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-48645728605 / 1000000000000) (-48645728563 / 1000000000000), orderedInterval (-3260587262 / 1000000000000) (-3260587220 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (346342570219291 / 800000000000) 4 (IntervalRat.scale (727 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (6621244320 / 1000000000000) (6621244321 / 1000000000000), orderedInterval (37763470977 / 1000000000000) (37763470978 / 1000000000000)))) (orderedInterval (-1550340192 / 1000000000000) (-1550340144 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (312517994083889 / 4000000000000) 4 (IntervalRat.scale (727 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-32934592215 / 1000000000000) (-32934592214 / 1000000000000), orderedInterval (-83835053892 / 1000000000000) (-83835053891 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (839467291401533 / 4000000000000) 4 (IntervalRat.scale (727 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-9041992945 / 1000000000000) (-9041992943 / 1000000000000), orderedInterval (-54307980043 / 1000000000000) (-54307980042 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2279316995799561 / 4000000000000) 4 (IntervalRat.scale (727 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30582653915 / 1000000000000) (-30582596986 / 1000000000000), orderedInterval (13514361331 / 1000000000000) (13514418260 / 1000000000000)))) (orderedInterval (13070860315 / 1000000000000) (13070884999 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1678934582803793 / 4000000000000) 4 (IntervalRat.scale (727 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-17103349609 / 1000000000000) (-17103349157 / 1000000000000), orderedInterval (35008933841 / 1000000000000) (35008934292 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2876883024157589 / 4000000000000) 4 (IntervalRat.scale (727 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-16335946874 / 1000000000000) (-16335946873 / 1000000000000), orderedInterval (-24854061829 / 1000000000000) (-24854061828 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2119099014677951 / 4000000000000) 4 (IntervalRat.scale (727 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (12511006131 / 1000000000000) (12511006198 / 1000000000000), orderedInterval (-32340668173 / 1000000000000) (-32340668106 / 1000000000000)))) (orderedInterval (9105799305 / 1000000000000) (9105799525 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate492_chunkChecks4_1 :
    compactCertificate492.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3251242839284273 / 4000000000000) 4 (IntervalRat.scale (727 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (2140065666 / 1000000000000) (2140065667 / 1000000000000), orderedInterval (-27905666934 / 1000000000000) (-27905666933 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1877105928461417 / 4000000000000) 4 (IntervalRat.scale (727 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-34016892102 / 1000000000000) (-34016862419 / 1000000000000), orderedInterval (14158905190 / 1000000000000) (14158934873 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3330957410117053 / 4000000000000) 4 (IntervalRat.scale (727 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-23304135263 / 1000000000000) (-23304135261 / 1000000000000), orderedInterval (-14865720534 / 1000000000000) (-14865720532 / 1000000000000)))) (orderedInterval (-107576021599 / 1000000000000) (-107576012338 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3112212492962257 / 4000000000000) 4 (IntervalRat.scale (727 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-7811997690 / 1000000000000) (-7811997687 / 1000000000000), orderedInterval (27522184109 / 1000000000000) (27522184111 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2221021686821281 / 4000000000000) 4 (IntervalRat.scale (727 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (721341614 / 1000000000000) (721341615 / 1000000000000), orderedInterval (-33853494728 / 1000000000000) (-33853494727 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2518401874204599 / 4000000000000) 4 (IntervalRat.scale (727 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (27961410495 / 1000000000000) (27961498156 / 1000000000000), orderedInterval (-15165090507 / 1000000000000) (-15165002846 / 1000000000000)))) (orderedInterval (1970744591 / 1000000000000) (1970748940 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2099580926117831 / 4000000000000) 4 (IntervalRat.scale (727 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-29935224474 / 1000000000000) (-29935224473 / 1000000000000), orderedInterval (-17768484302 / 1000000000000) (-17768484301 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1855043422126451 / 4000000000000) 4 (IntervalRat.scale (727 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-14759411181 / 1000000000000) (-14759410993 / 1000000000000), orderedInterval (33999632309 / 1000000000000) (33999632496 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (537663887522649 / 800000000000) 4 (IntervalRat.scale (727 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16458953071 / 1000000000000) (16458953072 / 1000000000000), orderedInterval (25994317070 / 1000000000000) (25994317071 / 1000000000000)))) (orderedInterval (5656971014 / 1000000000000) (5656971227 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate492_chunkChecks4_2 :
    compactCertificate492.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1487206608587803 / 4000000000000) 4 (IntervalRat.scale (727 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (39432349094 / 1000000000000) (39432357182 / 1000000000000), orderedInterval (-12596743753 / 1000000000000) (-12596735665 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1260721512462083 / 4000000000000) 4 (IntervalRat.scale (727 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (43704193835 / 1000000000000) (43704196609 / 1000000000000), orderedInterval (-10547862285 / 1000000000000) (-10547859510 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (788900985322049 / 4000000000000) 4 (IntervalRat.scale (727 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-5087918940 / 1000000000000) (-5087918939 / 1000000000000), orderedInterval (-56573363202 / 1000000000000) (-56573363201 / 1000000000000)))) (orderedInterval (-8300885422 / 1000000000000) (-8300883832 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (424273573672383 / 4000000000000) 4 (IntervalRat.scale (727 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (2979064595 / 1000000000000) (2979064599 / 1000000000000), orderedInterval (77401498016 / 1000000000000) (77401498020 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1151985285486149 / 4000000000000) 4 (IntervalRat.scale (727 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-11414927483 / 1000000000000) (-11414927417 / 1000000000000), orderedInterval (45629201925 / 1000000000000) (45629201990 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1572937421079973 / 4000000000000) 4 (IntervalRat.scale (727 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-38980694361 / 1000000000000) (-38980694354 / 1000000000000), orderedInterval (-9922223645 / 1000000000000) (-9922223638 / 1000000000000)))) (orderedInterval (4195369030 / 1000000000000) (4195369074 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (665099014677951 / 4000000000000) 4 (IntervalRat.scale (727 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-32604865466 / 1000000000000) (-32604865465 / 1000000000000), orderedInterval (-52491424594 / 1000000000000) (-52491424593 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2703590569472671 / 4000000000000) 4 (IntervalRat.scale (727 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-29030621985 / 1000000000000) (-29030621967 / 1000000000000), orderedInterval (-9933956452 / 1000000000000) (-9933956434 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1805873205034289 / 4000000000000) 4 (IntervalRat.scale (727 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-5088271286 / 1000000000000) (-5088271283 / 1000000000000), orderedInterval (37210741055 / 1000000000000) (37210741059 / 1000000000000)))) (orderedInterval (30466301470 / 1000000000000) (30466302006 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate492_chunkChecks4 :
    compactCertificate492.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate492.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate492_chunkChecks4_0
    compactCertificate492_chunkChecks4_1 compactCertificate492_chunkChecks4_2

theorem compactCertificate492_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate492.chunkCheck r b = true :=
  compactCertificate492.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate492_chunkChecks0
    · exact compactCertificate492_chunkChecks1
    · exact compactCertificate492_chunkChecks2
    · exact compactCertificate492_chunkChecks3
    · exact compactCertificate492_chunkChecks4)

theorem compactCertificate492_coefficient0 :
    compactCertificate492.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate492_coefficient1 :
    compactCertificate492.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate492_coefficient2 :
    compactCertificate492.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate492_coefficient3 :
    compactCertificate492.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate492_coefficient4 :
    compactCertificate492.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate492_coefficients : ∀ r : Fin 5,
    compactCertificate492.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate492_coefficient0
  · exact compactCertificate492_coefficient1
  · exact compactCertificate492_coefficient2
  · exact compactCertificate492_coefficient3
  · exact compactCertificate492_coefficient4

theorem compactCertificate492_lower : (1 : ℚ) ≤ compactCertificate492.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate492, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate492_proves {t : ℝ} (ht : t ∈ compactCertificate492.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate492.proves compactCertificate492_states compactCertificate492_chunks
    compactCertificate492_coefficients compactCertificate492_lower ht

end Erdos232
