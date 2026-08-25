/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate347 : CompactCertificate where
  left := 218
  right := 219
  center := 437 / 2
  grid := fun i =>
    match i.val with
    | 0 => 70
    | 1 => 51
    | 2 => 83
    | 3 => 15
    | 4 => 40
    | 5 => 109
    | 6 => 80
    | 7 => 138
    | 8 => 101
    | 9 => 156
    | 10 => 90
    | 11 => 159
    | 12 => 149
    | 13 => 106
    | 14 => 121
    | 15 => 100
    | 16 => 89
    | 17 => 129
    | 18 => 71
    | 19 => 60
    | 20 => 38
    | 21 => 20
    | 22 => 55
    | 23 => 75
    | 24 => 32
    | 25 => 129
    | _ => 86
  point := fun i =>
    match i.val with
    | 0 => 437 / 2
    | 1 => 643784444232737 / 4000000000000
    | 2 => 208186661878721 / 800000000000
    | 3 => 187854695205859 / 4000000000000
    | 4 => 504604135271623 / 4000000000000
    | 5 => 1370098386746091 / 4000000000000
    | 6 => 1009208270543683 / 4000000000000
    | 7 => 1729295572980559 / 4000000000000
    | 8 => 1273791292179181 / 4000000000000
    | 9 => 1954323412334563 / 4000000000000
    | 10 => 1128329148194827 / 4000000000000
    | 11 => 2002239873756743 / 4000000000000
    | 12 => 1870752213788867 / 4000000000000
    | 13 => 1335057052463411 / 4000000000000
    | 14 => 1513812405814869 / 4000000000000
    | 15 => 1262058961091461 / 4000000000000
    | 16 => 1115067366532681 / 4000000000000
    | 17 => 323189984659419 / 800000000000
    | 18 => 893960506124993 / 4000000000000
    | 19 => 757820221383673 / 4000000000000
    | 20 => 474208707820819 / 4000000000000
    | 21 => 255031020212973 / 4000000000000
    | 22 => 692458830477919 / 4000000000000
    | 23 => 945493332891263 / 4000000000000
    | 24 => 399791292179181 / 4000000000000
    | 25 => 1625129406959501 / 4000000000000
    | _ => 1085511128748259 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-31654772251 / 1000000000000) (-31654762522 / 1000000000000), orderedInterval (43793932778 / 1000000000000) (43793942507 / 1000000000000))
    | 1 => (orderedInterval (-62774401041 / 1000000000000) (-62774401021 / 1000000000000), orderedInterval (-3657213572 / 1000000000000) (-3657213552 / 1000000000000))
    | 2 => (orderedInterval (-13004503141 / 1000000000000) (-13004503140 / 1000000000000), orderedInterval (-47695334435 / 1000000000000) (-47695334434 / 1000000000000))
    | 3 => (orderedInterval (-67885773509 / 1000000000000) (-67885773508 / 1000000000000), orderedInterval (-93867746269 / 1000000000000) (-93867746268 / 1000000000000))
    | 4 => (orderedInterval (67885216731 / 1000000000000) (67885216732 / 1000000000000), orderedInterval (20660664830 / 1000000000000) (20660664831 / 1000000000000))
    | 5 => (orderedInterval (-33118478197 / 1000000000000) (-33118478196 / 1000000000000), orderedInterval (-27551953066 / 1000000000000) (-27551953065 / 1000000000000))
    | 6 => (orderedInterval (49339604448 / 1000000000000) (49339605585 / 1000000000000), orderedInterval (-9523442991 / 1000000000000) (-9523441854 / 1000000000000))
    | 7 => (orderedInterval (-16024273621 / 1000000000000) (-16024273315 / 1000000000000), orderedInterval (34886513993 / 1000000000000) (34886514299 / 1000000000000))
    | 8 => (orderedInterval (-41826966307 / 1000000000000) (-41826955789 / 1000000000000), orderedInterval (15865577687 / 1000000000000) (15865588205 / 1000000000000))
    | 9 => (orderedInterval (-23868493607 / 1000000000000) (-23868487182 / 1000000000000), orderedInterval (27103807064 / 1000000000000) (27103813488 / 1000000000000))
    | 10 => (orderedInterval (5871144320 / 1000000000000) (5871144321 / 1000000000000), orderedInterval (47131840510 / 1000000000000) (47131840511 / 1000000000000))
    | 11 => (orderedInterval (-34453894966 / 1000000000000) (-34453885240 / 1000000000000), orderedInterval (9240065634 / 1000000000000) (9240075360 / 1000000000000))
    | 12 => (orderedInterval (-13543616941 / 1000000000000) (-13543616940 / 1000000000000), orderedInterval (-34304276240 / 1000000000000) (-34304276239 / 1000000000000))
    | 13 => (orderedInterval (43653603837 / 1000000000000) (43653603954 / 1000000000000), orderedInterval (1259062456 / 1000000000000) (1259062573 / 1000000000000))
    | 14 => (orderedInterval (31987832793 / 1000000000000) (31987888565 / 1000000000000), orderedInterval (-25712101655 / 1000000000000) (-25712045883 / 1000000000000))
    | 15 => (orderedInterval (37825043902 / 1000000000000) (37825114884 / 1000000000000), orderedInterval (-24287650929 / 1000000000000) (-24287579946 / 1000000000000))
    | 16 => (orderedInterval (2386247593 / 1000000000000) (2386247597 / 1000000000000), orderedInterval (-47732775134 / 1000000000000) (-47732775130 / 1000000000000))
    | 17 => (orderedInterval (18783252961 / 1000000000000) (18783253760 / 1000000000000), orderedInterval (-34995099318 / 1000000000000) (-34995098519 / 1000000000000))
    | 18 => (orderedInterval (-50155769454 / 1000000000000) (-50155769453 / 1000000000000), orderedInterval (-18134153822 / 1000000000000) (-18134153820 / 1000000000000))
    | 19 => (orderedInterval (57098043448 / 1000000000000) (57098044094 / 1000000000000), orderedInterval (-10154211696 / 1000000000000) (-10154211051 / 1000000000000))
    | 20 => (orderedInterval (-3223269054 / 1000000000000) (-3223269042 / 1000000000000), orderedInterval (73222967815 / 1000000000000) (73222967826 / 1000000000000))
    | 21 => (orderedInterval (98965878637 / 1000000000000) (98965878821 / 1000000000000), orderedInterval (-14575970348 / 1000000000000) (-14575970164 / 1000000000000))
    | 22 => (orderedInterval (-54364912553 / 1000000000000) (-54364912552 / 1000000000000), orderedInterval (-26711024036 / 1000000000000) (-26711024035 / 1000000000000))
    | 23 => (orderedInterval (-51870130941 / 1000000000000) (-51870130885 / 1000000000000), orderedInterval (-1552915693 / 1000000000000) (-1552915636 / 1000000000000))
    | 24 => (orderedInterval (15934213223 / 1000000000000) (15934213224 / 1000000000000), orderedInterval (78123200608 / 1000000000000) (78123200609 / 1000000000000))
    | 25 => (orderedInterval (-38531367560 / 1000000000000) (-38531363191 / 1000000000000), orderedInterval (9117813316 / 1000000000000) (9117817685 / 1000000000000))
    | _ => (orderedInterval (44323836922 / 1000000000000) (44323851040 / 1000000000000), orderedInterval (-19607919226 / 1000000000000) (-19607905107 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-13894898294 / 1000000000000) (-13894894422 / 1000000000000)
      | 1 => orderedInterval (5569501014 / 1000000000000) (5569501041 / 1000000000000)
      | 2 => orderedInterval (-516622555 / 1000000000000) (-516622279 / 1000000000000)
      | 3 => orderedInterval (-221678751 / 1000000000000) (-221676139 / 1000000000000)
      | 4 => orderedInterval (4210636817 / 1000000000000) (4210637137 / 1000000000000)
      | 5 => orderedInterval (781159563 / 1000000000000) (781160425 / 1000000000000)
      | 6 => orderedInterval (4682847250 / 1000000000000) (4682847342 / 1000000000000)
      | 7 => orderedInterval (3381220942 / 1000000000000) (3381220976 / 1000000000000)
      | _ => orderedInterval (-5083752167 / 1000000000000) (-5083749101 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (13999891694 / 1000000000000) (13999895568 / 1000000000000)
      | 1 => orderedInterval (3724848222 / 1000000000000) (3724848252 / 1000000000000)
      | 2 => orderedInterval (-1570215680 / 1000000000000) (-1570215269 / 1000000000000)
      | 3 => orderedInterval (-3251535976 / 1000000000000) (-3251530076 / 1000000000000)
      | 4 => orderedInterval (1732814294 / 1000000000000) (1732814843 / 1000000000000)
      | 5 => orderedInterval (1423373707 / 1000000000000) (1423374960 / 1000000000000)
      | 6 => orderedInterval (4757445299 / 1000000000000) (4757445382 / 1000000000000)
      | 7 => orderedInterval (687402900 / 1000000000000) (687402930 / 1000000000000)
      | _ => orderedInterval (3404641075 / 1000000000000) (3404645112 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (13882605650 / 1000000000000) (13882609545 / 1000000000000)
      | 1 => orderedInterval (-6662994249 / 1000000000000) (-6662994207 / 1000000000000)
      | 2 => orderedInterval (219452297 / 1000000000000) (219452914 / 1000000000000)
      | 3 => orderedInterval (3788852101 / 1000000000000) (3788865477 / 1000000000000)
      | 4 => orderedInterval (-10274523618 / 1000000000000) (-10274522673 / 1000000000000)
      | 5 => orderedInterval (-2339046539 / 1000000000000) (-2339044708 / 1000000000000)
      | 6 => orderedInterval (-5951227624 / 1000000000000) (-5951227548 / 1000000000000)
      | 7 => orderedInterval (-5273981017 / 1000000000000) (-5273980988 / 1000000000000)
      | _ => orderedInterval (1948565220 / 1000000000000) (1948570679 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-12679667128 / 1000000000000) (-12679663230 / 1000000000000)
      | 1 => orderedInterval (-7670071119 / 1000000000000) (-7670071056 / 1000000000000)
      | 2 => orderedInterval (7146867662 / 1000000000000) (7146868595 / 1000000000000)
      | 3 => orderedInterval (30520932557 / 1000000000000) (30520962845 / 1000000000000)
      | 4 => orderedInterval (-7126565609 / 1000000000000) (-7126563980 / 1000000000000)
      | 5 => orderedInterval (845797832 / 1000000000000) (845800508 / 1000000000000)
      | 6 => orderedInterval (-3830810901 / 1000000000000) (-3830810829 / 1000000000000)
      | 7 => orderedInterval (-434588058 / 1000000000000) (-434588028 / 1000000000000)
      | _ => orderedInterval (-2330892050 / 1000000000000) (-2330884470 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-14138148554 / 1000000000000) (-14138144636 / 1000000000000)
      | 1 => orderedInterval (14565022140 / 1000000000000) (14565022236 / 1000000000000)
      | 2 => orderedInterval (2948704278 / 1000000000000) (2948705706 / 1000000000000)
      | 3 => orderedInterval (-27945482355 / 1000000000000) (-27945413591 / 1000000000000)
      | 4 => orderedInterval (26215064705 / 1000000000000) (26215067526 / 1000000000000)
      | 5 => orderedInterval (7149595095 / 1000000000000) (7149599033 / 1000000000000)
      | 6 => orderedInterval (6976804422 / 1000000000000) (6976804490 / 1000000000000)
      | 7 => orderedInterval (5921061578 / 1000000000000) (5921061610 / 1000000000000)
      | _ => orderedInterval (17729971309 / 1000000000000) (17729982242 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-1091586181 / 1000000000000) (-1091575020 / 1000000000000)
    | 1 => orderedInterval (24908665535 / 1000000000000) (24908681702 / 1000000000000)
    | 2 => orderedInterval (-10662297779 / 1000000000000) (-10662271509 / 1000000000000)
    | 3 => orderedInterval (4441003186 / 1000000000000) (4441050355 / 1000000000000)
    | _ => orderedInterval (39422592618 / 1000000000000) (39422684616 / 1000000000000)

theorem compactCertificate347_stateChecks0 :
    compactCertificate347.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (437 / 2)) (orderedInterval (-31654772251 / 1000000000000) (-31654762522 / 1000000000000), orderedInterval (43793932778 / 1000000000000) (43793942507 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (643784444232737 / 4000000000000)) (orderedInterval (-62774401041 / 1000000000000) (-62774401021 / 1000000000000), orderedInterval (-3657213572 / 1000000000000) (-3657213552 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 83 12 (208186661878721 / 800000000000)) (orderedInterval (-13004503141 / 1000000000000) (-13004503140 / 1000000000000), orderedInterval (-47695334435 / 1000000000000) (-47695334434 / 1000000000000))) = true
  rfl'

theorem compactCertificate347_stateChecks1 :
    compactCertificate347.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 15 12 (187854695205859 / 4000000000000)) (orderedInterval (-67885773509 / 1000000000000) (-67885773508 / 1000000000000), orderedInterval (-93867746269 / 1000000000000) (-93867746268 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 40 12 (504604135271623 / 4000000000000)) (orderedInterval (67885216731 / 1000000000000) (67885216732 / 1000000000000), orderedInterval (20660664830 / 1000000000000) (20660664831 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 109 12 (1370098386746091 / 4000000000000)) (orderedInterval (-33118478197 / 1000000000000) (-33118478196 / 1000000000000), orderedInterval (-27551953066 / 1000000000000) (-27551953065 / 1000000000000))) = true
  rfl'

theorem compactCertificate347_stateChecks2 :
    compactCertificate347.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 80 12 (1009208270543683 / 4000000000000)) (orderedInterval (49339604448 / 1000000000000) (49339605585 / 1000000000000), orderedInterval (-9523442991 / 1000000000000) (-9523441854 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 138 12 (1729295572980559 / 4000000000000)) (orderedInterval (-16024273621 / 1000000000000) (-16024273315 / 1000000000000), orderedInterval (34886513993 / 1000000000000) (34886514299 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 101 12 (1273791292179181 / 4000000000000)) (orderedInterval (-41826966307 / 1000000000000) (-41826955789 / 1000000000000), orderedInterval (15865577687 / 1000000000000) (15865588205 / 1000000000000))) = true
  rfl'

theorem compactCertificate347_stateChecks3 :
    compactCertificate347.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 156 12 (1954323412334563 / 4000000000000)) (orderedInterval (-23868493607 / 1000000000000) (-23868487182 / 1000000000000), orderedInterval (27103807064 / 1000000000000) (27103813488 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 90 12 (1128329148194827 / 4000000000000)) (orderedInterval (5871144320 / 1000000000000) (5871144321 / 1000000000000), orderedInterval (47131840510 / 1000000000000) (47131840511 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 159 12 (2002239873756743 / 4000000000000)) (orderedInterval (-34453894966 / 1000000000000) (-34453885240 / 1000000000000), orderedInterval (9240065634 / 1000000000000) (9240075360 / 1000000000000))) = true
  rfl'

theorem compactCertificate347_stateChecks4 :
    compactCertificate347.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 149 12 (1870752213788867 / 4000000000000)) (orderedInterval (-13543616941 / 1000000000000) (-13543616940 / 1000000000000), orderedInterval (-34304276240 / 1000000000000) (-34304276239 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 106 12 (1335057052463411 / 4000000000000)) (orderedInterval (43653603837 / 1000000000000) (43653603954 / 1000000000000), orderedInterval (1259062456 / 1000000000000) (1259062573 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 121 12 (1513812405814869 / 4000000000000)) (orderedInterval (31987832793 / 1000000000000) (31987888565 / 1000000000000), orderedInterval (-25712101655 / 1000000000000) (-25712045883 / 1000000000000))) = true
  rfl'

theorem compactCertificate347_stateChecks5 :
    compactCertificate347.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 100 12 (1262058961091461 / 4000000000000)) (orderedInterval (37825043902 / 1000000000000) (37825114884 / 1000000000000), orderedInterval (-24287650929 / 1000000000000) (-24287579946 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 89 12 (1115067366532681 / 4000000000000)) (orderedInterval (2386247593 / 1000000000000) (2386247597 / 1000000000000), orderedInterval (-47732775134 / 1000000000000) (-47732775130 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 129 12 (323189984659419 / 800000000000)) (orderedInterval (18783252961 / 1000000000000) (18783253760 / 1000000000000), orderedInterval (-34995099318 / 1000000000000) (-34995098519 / 1000000000000))) = true
  rfl'

theorem compactCertificate347_stateChecks6 :
    compactCertificate347.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (893960506124993 / 4000000000000)) (orderedInterval (-50155769454 / 1000000000000) (-50155769453 / 1000000000000), orderedInterval (-18134153822 / 1000000000000) (-18134153820 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 60 12 (757820221383673 / 4000000000000)) (orderedInterval (57098043448 / 1000000000000) (57098044094 / 1000000000000), orderedInterval (-10154211696 / 1000000000000) (-10154211051 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (474208707820819 / 4000000000000)) (orderedInterval (-3223269054 / 1000000000000) (-3223269042 / 1000000000000), orderedInterval (73222967815 / 1000000000000) (73222967826 / 1000000000000))) = true
  rfl'

theorem compactCertificate347_stateChecks7 :
    compactCertificate347.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 20 12 (255031020212973 / 4000000000000)) (orderedInterval (98965878637 / 1000000000000) (98965878821 / 1000000000000), orderedInterval (-14575970348 / 1000000000000) (-14575970164 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (692458830477919 / 4000000000000)) (orderedInterval (-54364912553 / 1000000000000) (-54364912552 / 1000000000000), orderedInterval (-26711024036 / 1000000000000) (-26711024035 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 75 12 (945493332891263 / 4000000000000)) (orderedInterval (-51870130941 / 1000000000000) (-51870130885 / 1000000000000), orderedInterval (-1552915693 / 1000000000000) (-1552915636 / 1000000000000))) = true
  rfl'

theorem compactCertificate347_stateChecks8 :
    compactCertificate347.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (399791292179181 / 4000000000000)) (orderedInterval (15934213223 / 1000000000000) (15934213224 / 1000000000000), orderedInterval (78123200608 / 1000000000000) (78123200609 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 129 12 (1625129406959501 / 4000000000000)) (orderedInterval (-38531367560 / 1000000000000) (-38531363191 / 1000000000000), orderedInterval (9117813316 / 1000000000000) (9117817685 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 86 12 (1085511128748259 / 4000000000000)) (orderedInterval (44323836922 / 1000000000000) (44323851040 / 1000000000000), orderedInterval (-19607919226 / 1000000000000) (-19607905107 / 1000000000000))) = true
  rfl'

theorem compactCertificate347_states : ∀ j,
    BesselStateValid (compactCertificate347.point j) (compactCertificate347.state j) :=
  compactCertificate347.statesValid_of_checks3 compactCertificate347_stateChecks0
    compactCertificate347_stateChecks1 compactCertificate347_stateChecks2
    compactCertificate347_stateChecks3 compactCertificate347_stateChecks4
    compactCertificate347_stateChecks5 compactCertificate347_stateChecks6
    compactCertificate347_stateChecks7 compactCertificate347_stateChecks8

theorem compactCertificate347_chunkChecks0_0 :
    compactCertificate347.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (437 / 2) 0 (IntervalRat.scale (437 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-31654772251 / 1000000000000) (-31654762522 / 1000000000000), orderedInterval (43793932778 / 1000000000000) (43793942507 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (643784444232737 / 4000000000000) 0 (IntervalRat.scale (437 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-62774401041 / 1000000000000) (-62774401021 / 1000000000000), orderedInterval (-3657213572 / 1000000000000) (-3657213552 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (208186661878721 / 800000000000) 0 (IntervalRat.scale (437 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-13004503141 / 1000000000000) (-13004503140 / 1000000000000), orderedInterval (-47695334435 / 1000000000000) (-47695334434 / 1000000000000)))) (orderedInterval (-13894898294 / 1000000000000) (-13894894422 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (187854695205859 / 4000000000000) 0 (IntervalRat.scale (437 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-67885773509 / 1000000000000) (-67885773508 / 1000000000000), orderedInterval (-93867746269 / 1000000000000) (-93867746268 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (504604135271623 / 4000000000000) 0 (IntervalRat.scale (437 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (67885216731 / 1000000000000) (67885216732 / 1000000000000), orderedInterval (20660664830 / 1000000000000) (20660664831 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1370098386746091 / 4000000000000) 0 (IntervalRat.scale (437 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-33118478197 / 1000000000000) (-33118478196 / 1000000000000), orderedInterval (-27551953066 / 1000000000000) (-27551953065 / 1000000000000)))) (orderedInterval (5569501014 / 1000000000000) (5569501041 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1009208270543683 / 4000000000000) 0 (IntervalRat.scale (437 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (49339604448 / 1000000000000) (49339605585 / 1000000000000), orderedInterval (-9523442991 / 1000000000000) (-9523441854 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1729295572980559 / 4000000000000) 0 (IntervalRat.scale (437 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-16024273621 / 1000000000000) (-16024273315 / 1000000000000), orderedInterval (34886513993 / 1000000000000) (34886514299 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1273791292179181 / 4000000000000) 0 (IntervalRat.scale (437 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-41826966307 / 1000000000000) (-41826955789 / 1000000000000), orderedInterval (15865577687 / 1000000000000) (15865588205 / 1000000000000)))) (orderedInterval (-516622555 / 1000000000000) (-516622279 / 1000000000000))) = true
  rfl'

theorem compactCertificate347_chunkChecks0_1 :
    compactCertificate347.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1954323412334563 / 4000000000000) 0 (IntervalRat.scale (437 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-23868493607 / 1000000000000) (-23868487182 / 1000000000000), orderedInterval (27103807064 / 1000000000000) (27103813488 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1128329148194827 / 4000000000000) 0 (IntervalRat.scale (437 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (5871144320 / 1000000000000) (5871144321 / 1000000000000), orderedInterval (47131840510 / 1000000000000) (47131840511 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2002239873756743 / 4000000000000) 0 (IntervalRat.scale (437 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-34453894966 / 1000000000000) (-34453885240 / 1000000000000), orderedInterval (9240065634 / 1000000000000) (9240075360 / 1000000000000)))) (orderedInterval (-221678751 / 1000000000000) (-221676139 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1870752213788867 / 4000000000000) 0 (IntervalRat.scale (437 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-13543616941 / 1000000000000) (-13543616940 / 1000000000000), orderedInterval (-34304276240 / 1000000000000) (-34304276239 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1335057052463411 / 4000000000000) 0 (IntervalRat.scale (437 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (43653603837 / 1000000000000) (43653603954 / 1000000000000), orderedInterval (1259062456 / 1000000000000) (1259062573 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1513812405814869 / 4000000000000) 0 (IntervalRat.scale (437 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (31987832793 / 1000000000000) (31987888565 / 1000000000000), orderedInterval (-25712101655 / 1000000000000) (-25712045883 / 1000000000000)))) (orderedInterval (4210636817 / 1000000000000) (4210637137 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1262058961091461 / 4000000000000) 0 (IntervalRat.scale (437 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (37825043902 / 1000000000000) (37825114884 / 1000000000000), orderedInterval (-24287650929 / 1000000000000) (-24287579946 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1115067366532681 / 4000000000000) 0 (IntervalRat.scale (437 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (2386247593 / 1000000000000) (2386247597 / 1000000000000), orderedInterval (-47732775134 / 1000000000000) (-47732775130 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (323189984659419 / 800000000000) 0 (IntervalRat.scale (437 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (18783252961 / 1000000000000) (18783253760 / 1000000000000), orderedInterval (-34995099318 / 1000000000000) (-34995098519 / 1000000000000)))) (orderedInterval (781159563 / 1000000000000) (781160425 / 1000000000000))) = true
  rfl'

theorem compactCertificate347_chunkChecks0_2 :
    compactCertificate347.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (893960506124993 / 4000000000000) 0 (IntervalRat.scale (437 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-50155769454 / 1000000000000) (-50155769453 / 1000000000000), orderedInterval (-18134153822 / 1000000000000) (-18134153820 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (757820221383673 / 4000000000000) 0 (IntervalRat.scale (437 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (57098043448 / 1000000000000) (57098044094 / 1000000000000), orderedInterval (-10154211696 / 1000000000000) (-10154211051 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (474208707820819 / 4000000000000) 0 (IntervalRat.scale (437 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-3223269054 / 1000000000000) (-3223269042 / 1000000000000), orderedInterval (73222967815 / 1000000000000) (73222967826 / 1000000000000)))) (orderedInterval (4682847250 / 1000000000000) (4682847342 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (255031020212973 / 4000000000000) 0 (IntervalRat.scale (437 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (98965878637 / 1000000000000) (98965878821 / 1000000000000), orderedInterval (-14575970348 / 1000000000000) (-14575970164 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (692458830477919 / 4000000000000) 0 (IntervalRat.scale (437 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-54364912553 / 1000000000000) (-54364912552 / 1000000000000), orderedInterval (-26711024036 / 1000000000000) (-26711024035 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (945493332891263 / 4000000000000) 0 (IntervalRat.scale (437 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-51870130941 / 1000000000000) (-51870130885 / 1000000000000), orderedInterval (-1552915693 / 1000000000000) (-1552915636 / 1000000000000)))) (orderedInterval (3381220942 / 1000000000000) (3381220976 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (399791292179181 / 4000000000000) 0 (IntervalRat.scale (437 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (15934213223 / 1000000000000) (15934213224 / 1000000000000), orderedInterval (78123200608 / 1000000000000) (78123200609 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1625129406959501 / 4000000000000) 0 (IntervalRat.scale (437 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-38531367560 / 1000000000000) (-38531363191 / 1000000000000), orderedInterval (9117813316 / 1000000000000) (9117817685 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1085511128748259 / 4000000000000) 0 (IntervalRat.scale (437 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (44323836922 / 1000000000000) (44323851040 / 1000000000000), orderedInterval (-19607919226 / 1000000000000) (-19607905107 / 1000000000000)))) (orderedInterval (-5083752167 / 1000000000000) (-5083749101 / 1000000000000))) = true
  rfl'

theorem compactCertificate347_chunkChecks0 :
    compactCertificate347.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate347.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate347_chunkChecks0_0
    compactCertificate347_chunkChecks0_1 compactCertificate347_chunkChecks0_2

theorem compactCertificate347_chunkChecks1_0 :
    compactCertificate347.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (437 / 2) 1 (IntervalRat.scale (437 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-31654772251 / 1000000000000) (-31654762522 / 1000000000000), orderedInterval (43793932778 / 1000000000000) (43793942507 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (643784444232737 / 4000000000000) 1 (IntervalRat.scale (437 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-62774401041 / 1000000000000) (-62774401021 / 1000000000000), orderedInterval (-3657213572 / 1000000000000) (-3657213552 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (208186661878721 / 800000000000) 1 (IntervalRat.scale (437 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-13004503141 / 1000000000000) (-13004503140 / 1000000000000), orderedInterval (-47695334435 / 1000000000000) (-47695334434 / 1000000000000)))) (orderedInterval (13999891694 / 1000000000000) (13999895568 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (187854695205859 / 4000000000000) 1 (IntervalRat.scale (437 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-67885773509 / 1000000000000) (-67885773508 / 1000000000000), orderedInterval (-93867746269 / 1000000000000) (-93867746268 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (504604135271623 / 4000000000000) 1 (IntervalRat.scale (437 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (67885216731 / 1000000000000) (67885216732 / 1000000000000), orderedInterval (20660664830 / 1000000000000) (20660664831 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1370098386746091 / 4000000000000) 1 (IntervalRat.scale (437 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-33118478197 / 1000000000000) (-33118478196 / 1000000000000), orderedInterval (-27551953066 / 1000000000000) (-27551953065 / 1000000000000)))) (orderedInterval (3724848222 / 1000000000000) (3724848252 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1009208270543683 / 4000000000000) 1 (IntervalRat.scale (437 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (49339604448 / 1000000000000) (49339605585 / 1000000000000), orderedInterval (-9523442991 / 1000000000000) (-9523441854 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1729295572980559 / 4000000000000) 1 (IntervalRat.scale (437 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-16024273621 / 1000000000000) (-16024273315 / 1000000000000), orderedInterval (34886513993 / 1000000000000) (34886514299 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1273791292179181 / 4000000000000) 1 (IntervalRat.scale (437 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-41826966307 / 1000000000000) (-41826955789 / 1000000000000), orderedInterval (15865577687 / 1000000000000) (15865588205 / 1000000000000)))) (orderedInterval (-1570215680 / 1000000000000) (-1570215269 / 1000000000000))) = true
  rfl'

theorem compactCertificate347_chunkChecks1_1 :
    compactCertificate347.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1954323412334563 / 4000000000000) 1 (IntervalRat.scale (437 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-23868493607 / 1000000000000) (-23868487182 / 1000000000000), orderedInterval (27103807064 / 1000000000000) (27103813488 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1128329148194827 / 4000000000000) 1 (IntervalRat.scale (437 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (5871144320 / 1000000000000) (5871144321 / 1000000000000), orderedInterval (47131840510 / 1000000000000) (47131840511 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2002239873756743 / 4000000000000) 1 (IntervalRat.scale (437 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-34453894966 / 1000000000000) (-34453885240 / 1000000000000), orderedInterval (9240065634 / 1000000000000) (9240075360 / 1000000000000)))) (orderedInterval (-3251535976 / 1000000000000) (-3251530076 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1870752213788867 / 4000000000000) 1 (IntervalRat.scale (437 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-13543616941 / 1000000000000) (-13543616940 / 1000000000000), orderedInterval (-34304276240 / 1000000000000) (-34304276239 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1335057052463411 / 4000000000000) 1 (IntervalRat.scale (437 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (43653603837 / 1000000000000) (43653603954 / 1000000000000), orderedInterval (1259062456 / 1000000000000) (1259062573 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1513812405814869 / 4000000000000) 1 (IntervalRat.scale (437 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (31987832793 / 1000000000000) (31987888565 / 1000000000000), orderedInterval (-25712101655 / 1000000000000) (-25712045883 / 1000000000000)))) (orderedInterval (1732814294 / 1000000000000) (1732814843 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1262058961091461 / 4000000000000) 1 (IntervalRat.scale (437 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (37825043902 / 1000000000000) (37825114884 / 1000000000000), orderedInterval (-24287650929 / 1000000000000) (-24287579946 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1115067366532681 / 4000000000000) 1 (IntervalRat.scale (437 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (2386247593 / 1000000000000) (2386247597 / 1000000000000), orderedInterval (-47732775134 / 1000000000000) (-47732775130 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (323189984659419 / 800000000000) 1 (IntervalRat.scale (437 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (18783252961 / 1000000000000) (18783253760 / 1000000000000), orderedInterval (-34995099318 / 1000000000000) (-34995098519 / 1000000000000)))) (orderedInterval (1423373707 / 1000000000000) (1423374960 / 1000000000000))) = true
  rfl'

theorem compactCertificate347_chunkChecks1_2 :
    compactCertificate347.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (893960506124993 / 4000000000000) 1 (IntervalRat.scale (437 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-50155769454 / 1000000000000) (-50155769453 / 1000000000000), orderedInterval (-18134153822 / 1000000000000) (-18134153820 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (757820221383673 / 4000000000000) 1 (IntervalRat.scale (437 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (57098043448 / 1000000000000) (57098044094 / 1000000000000), orderedInterval (-10154211696 / 1000000000000) (-10154211051 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (474208707820819 / 4000000000000) 1 (IntervalRat.scale (437 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-3223269054 / 1000000000000) (-3223269042 / 1000000000000), orderedInterval (73222967815 / 1000000000000) (73222967826 / 1000000000000)))) (orderedInterval (4757445299 / 1000000000000) (4757445382 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (255031020212973 / 4000000000000) 1 (IntervalRat.scale (437 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (98965878637 / 1000000000000) (98965878821 / 1000000000000), orderedInterval (-14575970348 / 1000000000000) (-14575970164 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (692458830477919 / 4000000000000) 1 (IntervalRat.scale (437 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-54364912553 / 1000000000000) (-54364912552 / 1000000000000), orderedInterval (-26711024036 / 1000000000000) (-26711024035 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (945493332891263 / 4000000000000) 1 (IntervalRat.scale (437 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-51870130941 / 1000000000000) (-51870130885 / 1000000000000), orderedInterval (-1552915693 / 1000000000000) (-1552915636 / 1000000000000)))) (orderedInterval (687402900 / 1000000000000) (687402930 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (399791292179181 / 4000000000000) 1 (IntervalRat.scale (437 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (15934213223 / 1000000000000) (15934213224 / 1000000000000), orderedInterval (78123200608 / 1000000000000) (78123200609 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1625129406959501 / 4000000000000) 1 (IntervalRat.scale (437 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-38531367560 / 1000000000000) (-38531363191 / 1000000000000), orderedInterval (9117813316 / 1000000000000) (9117817685 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1085511128748259 / 4000000000000) 1 (IntervalRat.scale (437 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (44323836922 / 1000000000000) (44323851040 / 1000000000000), orderedInterval (-19607919226 / 1000000000000) (-19607905107 / 1000000000000)))) (orderedInterval (3404641075 / 1000000000000) (3404645112 / 1000000000000))) = true
  rfl'

theorem compactCertificate347_chunkChecks1 :
    compactCertificate347.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate347.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate347_chunkChecks1_0
    compactCertificate347_chunkChecks1_1 compactCertificate347_chunkChecks1_2

theorem compactCertificate347_chunkChecks2_0 :
    compactCertificate347.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (437 / 2) 2 (IntervalRat.scale (437 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-31654772251 / 1000000000000) (-31654762522 / 1000000000000), orderedInterval (43793932778 / 1000000000000) (43793942507 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (643784444232737 / 4000000000000) 2 (IntervalRat.scale (437 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-62774401041 / 1000000000000) (-62774401021 / 1000000000000), orderedInterval (-3657213572 / 1000000000000) (-3657213552 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (208186661878721 / 800000000000) 2 (IntervalRat.scale (437 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-13004503141 / 1000000000000) (-13004503140 / 1000000000000), orderedInterval (-47695334435 / 1000000000000) (-47695334434 / 1000000000000)))) (orderedInterval (13882605650 / 1000000000000) (13882609545 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (187854695205859 / 4000000000000) 2 (IntervalRat.scale (437 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-67885773509 / 1000000000000) (-67885773508 / 1000000000000), orderedInterval (-93867746269 / 1000000000000) (-93867746268 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (504604135271623 / 4000000000000) 2 (IntervalRat.scale (437 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (67885216731 / 1000000000000) (67885216732 / 1000000000000), orderedInterval (20660664830 / 1000000000000) (20660664831 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1370098386746091 / 4000000000000) 2 (IntervalRat.scale (437 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-33118478197 / 1000000000000) (-33118478196 / 1000000000000), orderedInterval (-27551953066 / 1000000000000) (-27551953065 / 1000000000000)))) (orderedInterval (-6662994249 / 1000000000000) (-6662994207 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1009208270543683 / 4000000000000) 2 (IntervalRat.scale (437 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (49339604448 / 1000000000000) (49339605585 / 1000000000000), orderedInterval (-9523442991 / 1000000000000) (-9523441854 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1729295572980559 / 4000000000000) 2 (IntervalRat.scale (437 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-16024273621 / 1000000000000) (-16024273315 / 1000000000000), orderedInterval (34886513993 / 1000000000000) (34886514299 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1273791292179181 / 4000000000000) 2 (IntervalRat.scale (437 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-41826966307 / 1000000000000) (-41826955789 / 1000000000000), orderedInterval (15865577687 / 1000000000000) (15865588205 / 1000000000000)))) (orderedInterval (219452297 / 1000000000000) (219452914 / 1000000000000))) = true
  rfl'

theorem compactCertificate347_chunkChecks2_1 :
    compactCertificate347.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1954323412334563 / 4000000000000) 2 (IntervalRat.scale (437 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-23868493607 / 1000000000000) (-23868487182 / 1000000000000), orderedInterval (27103807064 / 1000000000000) (27103813488 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1128329148194827 / 4000000000000) 2 (IntervalRat.scale (437 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (5871144320 / 1000000000000) (5871144321 / 1000000000000), orderedInterval (47131840510 / 1000000000000) (47131840511 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2002239873756743 / 4000000000000) 2 (IntervalRat.scale (437 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-34453894966 / 1000000000000) (-34453885240 / 1000000000000), orderedInterval (9240065634 / 1000000000000) (9240075360 / 1000000000000)))) (orderedInterval (3788852101 / 1000000000000) (3788865477 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1870752213788867 / 4000000000000) 2 (IntervalRat.scale (437 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-13543616941 / 1000000000000) (-13543616940 / 1000000000000), orderedInterval (-34304276240 / 1000000000000) (-34304276239 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1335057052463411 / 4000000000000) 2 (IntervalRat.scale (437 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (43653603837 / 1000000000000) (43653603954 / 1000000000000), orderedInterval (1259062456 / 1000000000000) (1259062573 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1513812405814869 / 4000000000000) 2 (IntervalRat.scale (437 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (31987832793 / 1000000000000) (31987888565 / 1000000000000), orderedInterval (-25712101655 / 1000000000000) (-25712045883 / 1000000000000)))) (orderedInterval (-10274523618 / 1000000000000) (-10274522673 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1262058961091461 / 4000000000000) 2 (IntervalRat.scale (437 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (37825043902 / 1000000000000) (37825114884 / 1000000000000), orderedInterval (-24287650929 / 1000000000000) (-24287579946 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1115067366532681 / 4000000000000) 2 (IntervalRat.scale (437 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (2386247593 / 1000000000000) (2386247597 / 1000000000000), orderedInterval (-47732775134 / 1000000000000) (-47732775130 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (323189984659419 / 800000000000) 2 (IntervalRat.scale (437 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (18783252961 / 1000000000000) (18783253760 / 1000000000000), orderedInterval (-34995099318 / 1000000000000) (-34995098519 / 1000000000000)))) (orderedInterval (-2339046539 / 1000000000000) (-2339044708 / 1000000000000))) = true
  rfl'

theorem compactCertificate347_chunkChecks2_2 :
    compactCertificate347.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (893960506124993 / 4000000000000) 2 (IntervalRat.scale (437 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-50155769454 / 1000000000000) (-50155769453 / 1000000000000), orderedInterval (-18134153822 / 1000000000000) (-18134153820 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (757820221383673 / 4000000000000) 2 (IntervalRat.scale (437 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (57098043448 / 1000000000000) (57098044094 / 1000000000000), orderedInterval (-10154211696 / 1000000000000) (-10154211051 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (474208707820819 / 4000000000000) 2 (IntervalRat.scale (437 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-3223269054 / 1000000000000) (-3223269042 / 1000000000000), orderedInterval (73222967815 / 1000000000000) (73222967826 / 1000000000000)))) (orderedInterval (-5951227624 / 1000000000000) (-5951227548 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (255031020212973 / 4000000000000) 2 (IntervalRat.scale (437 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (98965878637 / 1000000000000) (98965878821 / 1000000000000), orderedInterval (-14575970348 / 1000000000000) (-14575970164 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (692458830477919 / 4000000000000) 2 (IntervalRat.scale (437 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-54364912553 / 1000000000000) (-54364912552 / 1000000000000), orderedInterval (-26711024036 / 1000000000000) (-26711024035 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (945493332891263 / 4000000000000) 2 (IntervalRat.scale (437 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-51870130941 / 1000000000000) (-51870130885 / 1000000000000), orderedInterval (-1552915693 / 1000000000000) (-1552915636 / 1000000000000)))) (orderedInterval (-5273981017 / 1000000000000) (-5273980988 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (399791292179181 / 4000000000000) 2 (IntervalRat.scale (437 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (15934213223 / 1000000000000) (15934213224 / 1000000000000), orderedInterval (78123200608 / 1000000000000) (78123200609 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1625129406959501 / 4000000000000) 2 (IntervalRat.scale (437 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-38531367560 / 1000000000000) (-38531363191 / 1000000000000), orderedInterval (9117813316 / 1000000000000) (9117817685 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1085511128748259 / 4000000000000) 2 (IntervalRat.scale (437 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (44323836922 / 1000000000000) (44323851040 / 1000000000000), orderedInterval (-19607919226 / 1000000000000) (-19607905107 / 1000000000000)))) (orderedInterval (1948565220 / 1000000000000) (1948570679 / 1000000000000))) = true
  rfl'

theorem compactCertificate347_chunkChecks2 :
    compactCertificate347.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate347.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate347_chunkChecks2_0
    compactCertificate347_chunkChecks2_1 compactCertificate347_chunkChecks2_2

theorem compactCertificate347_chunkChecks3_0 :
    compactCertificate347.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (437 / 2) 3 (IntervalRat.scale (437 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-31654772251 / 1000000000000) (-31654762522 / 1000000000000), orderedInterval (43793932778 / 1000000000000) (43793942507 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (643784444232737 / 4000000000000) 3 (IntervalRat.scale (437 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-62774401041 / 1000000000000) (-62774401021 / 1000000000000), orderedInterval (-3657213572 / 1000000000000) (-3657213552 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (208186661878721 / 800000000000) 3 (IntervalRat.scale (437 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-13004503141 / 1000000000000) (-13004503140 / 1000000000000), orderedInterval (-47695334435 / 1000000000000) (-47695334434 / 1000000000000)))) (orderedInterval (-12679667128 / 1000000000000) (-12679663230 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (187854695205859 / 4000000000000) 3 (IntervalRat.scale (437 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-67885773509 / 1000000000000) (-67885773508 / 1000000000000), orderedInterval (-93867746269 / 1000000000000) (-93867746268 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (504604135271623 / 4000000000000) 3 (IntervalRat.scale (437 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (67885216731 / 1000000000000) (67885216732 / 1000000000000), orderedInterval (20660664830 / 1000000000000) (20660664831 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1370098386746091 / 4000000000000) 3 (IntervalRat.scale (437 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-33118478197 / 1000000000000) (-33118478196 / 1000000000000), orderedInterval (-27551953066 / 1000000000000) (-27551953065 / 1000000000000)))) (orderedInterval (-7670071119 / 1000000000000) (-7670071056 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1009208270543683 / 4000000000000) 3 (IntervalRat.scale (437 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (49339604448 / 1000000000000) (49339605585 / 1000000000000), orderedInterval (-9523442991 / 1000000000000) (-9523441854 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1729295572980559 / 4000000000000) 3 (IntervalRat.scale (437 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-16024273621 / 1000000000000) (-16024273315 / 1000000000000), orderedInterval (34886513993 / 1000000000000) (34886514299 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1273791292179181 / 4000000000000) 3 (IntervalRat.scale (437 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-41826966307 / 1000000000000) (-41826955789 / 1000000000000), orderedInterval (15865577687 / 1000000000000) (15865588205 / 1000000000000)))) (orderedInterval (7146867662 / 1000000000000) (7146868595 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate347_chunkChecks3_1 :
    compactCertificate347.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1954323412334563 / 4000000000000) 3 (IntervalRat.scale (437 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-23868493607 / 1000000000000) (-23868487182 / 1000000000000), orderedInterval (27103807064 / 1000000000000) (27103813488 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1128329148194827 / 4000000000000) 3 (IntervalRat.scale (437 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (5871144320 / 1000000000000) (5871144321 / 1000000000000), orderedInterval (47131840510 / 1000000000000) (47131840511 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2002239873756743 / 4000000000000) 3 (IntervalRat.scale (437 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-34453894966 / 1000000000000) (-34453885240 / 1000000000000), orderedInterval (9240065634 / 1000000000000) (9240075360 / 1000000000000)))) (orderedInterval (30520932557 / 1000000000000) (30520962845 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1870752213788867 / 4000000000000) 3 (IntervalRat.scale (437 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-13543616941 / 1000000000000) (-13543616940 / 1000000000000), orderedInterval (-34304276240 / 1000000000000) (-34304276239 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1335057052463411 / 4000000000000) 3 (IntervalRat.scale (437 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (43653603837 / 1000000000000) (43653603954 / 1000000000000), orderedInterval (1259062456 / 1000000000000) (1259062573 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1513812405814869 / 4000000000000) 3 (IntervalRat.scale (437 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (31987832793 / 1000000000000) (31987888565 / 1000000000000), orderedInterval (-25712101655 / 1000000000000) (-25712045883 / 1000000000000)))) (orderedInterval (-7126565609 / 1000000000000) (-7126563980 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1262058961091461 / 4000000000000) 3 (IntervalRat.scale (437 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (37825043902 / 1000000000000) (37825114884 / 1000000000000), orderedInterval (-24287650929 / 1000000000000) (-24287579946 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1115067366532681 / 4000000000000) 3 (IntervalRat.scale (437 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (2386247593 / 1000000000000) (2386247597 / 1000000000000), orderedInterval (-47732775134 / 1000000000000) (-47732775130 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (323189984659419 / 800000000000) 3 (IntervalRat.scale (437 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (18783252961 / 1000000000000) (18783253760 / 1000000000000), orderedInterval (-34995099318 / 1000000000000) (-34995098519 / 1000000000000)))) (orderedInterval (845797832 / 1000000000000) (845800508 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate347_chunkChecks3_2 :
    compactCertificate347.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (893960506124993 / 4000000000000) 3 (IntervalRat.scale (437 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-50155769454 / 1000000000000) (-50155769453 / 1000000000000), orderedInterval (-18134153822 / 1000000000000) (-18134153820 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (757820221383673 / 4000000000000) 3 (IntervalRat.scale (437 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (57098043448 / 1000000000000) (57098044094 / 1000000000000), orderedInterval (-10154211696 / 1000000000000) (-10154211051 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (474208707820819 / 4000000000000) 3 (IntervalRat.scale (437 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-3223269054 / 1000000000000) (-3223269042 / 1000000000000), orderedInterval (73222967815 / 1000000000000) (73222967826 / 1000000000000)))) (orderedInterval (-3830810901 / 1000000000000) (-3830810829 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (255031020212973 / 4000000000000) 3 (IntervalRat.scale (437 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (98965878637 / 1000000000000) (98965878821 / 1000000000000), orderedInterval (-14575970348 / 1000000000000) (-14575970164 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (692458830477919 / 4000000000000) 3 (IntervalRat.scale (437 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-54364912553 / 1000000000000) (-54364912552 / 1000000000000), orderedInterval (-26711024036 / 1000000000000) (-26711024035 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (945493332891263 / 4000000000000) 3 (IntervalRat.scale (437 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-51870130941 / 1000000000000) (-51870130885 / 1000000000000), orderedInterval (-1552915693 / 1000000000000) (-1552915636 / 1000000000000)))) (orderedInterval (-434588058 / 1000000000000) (-434588028 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (399791292179181 / 4000000000000) 3 (IntervalRat.scale (437 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (15934213223 / 1000000000000) (15934213224 / 1000000000000), orderedInterval (78123200608 / 1000000000000) (78123200609 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1625129406959501 / 4000000000000) 3 (IntervalRat.scale (437 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-38531367560 / 1000000000000) (-38531363191 / 1000000000000), orderedInterval (9117813316 / 1000000000000) (9117817685 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1085511128748259 / 4000000000000) 3 (IntervalRat.scale (437 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (44323836922 / 1000000000000) (44323851040 / 1000000000000), orderedInterval (-19607919226 / 1000000000000) (-19607905107 / 1000000000000)))) (orderedInterval (-2330892050 / 1000000000000) (-2330884470 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate347_chunkChecks3 :
    compactCertificate347.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate347.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate347_chunkChecks3_0
    compactCertificate347_chunkChecks3_1 compactCertificate347_chunkChecks3_2

theorem compactCertificate347_chunkChecks4_0 :
    compactCertificate347.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (437 / 2) 4 (IntervalRat.scale (437 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-31654772251 / 1000000000000) (-31654762522 / 1000000000000), orderedInterval (43793932778 / 1000000000000) (43793942507 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (643784444232737 / 4000000000000) 4 (IntervalRat.scale (437 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-62774401041 / 1000000000000) (-62774401021 / 1000000000000), orderedInterval (-3657213572 / 1000000000000) (-3657213552 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (208186661878721 / 800000000000) 4 (IntervalRat.scale (437 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-13004503141 / 1000000000000) (-13004503140 / 1000000000000), orderedInterval (-47695334435 / 1000000000000) (-47695334434 / 1000000000000)))) (orderedInterval (-14138148554 / 1000000000000) (-14138144636 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (187854695205859 / 4000000000000) 4 (IntervalRat.scale (437 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-67885773509 / 1000000000000) (-67885773508 / 1000000000000), orderedInterval (-93867746269 / 1000000000000) (-93867746268 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (504604135271623 / 4000000000000) 4 (IntervalRat.scale (437 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (67885216731 / 1000000000000) (67885216732 / 1000000000000), orderedInterval (20660664830 / 1000000000000) (20660664831 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1370098386746091 / 4000000000000) 4 (IntervalRat.scale (437 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-33118478197 / 1000000000000) (-33118478196 / 1000000000000), orderedInterval (-27551953066 / 1000000000000) (-27551953065 / 1000000000000)))) (orderedInterval (14565022140 / 1000000000000) (14565022236 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1009208270543683 / 4000000000000) 4 (IntervalRat.scale (437 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (49339604448 / 1000000000000) (49339605585 / 1000000000000), orderedInterval (-9523442991 / 1000000000000) (-9523441854 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1729295572980559 / 4000000000000) 4 (IntervalRat.scale (437 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-16024273621 / 1000000000000) (-16024273315 / 1000000000000), orderedInterval (34886513993 / 1000000000000) (34886514299 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1273791292179181 / 4000000000000) 4 (IntervalRat.scale (437 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-41826966307 / 1000000000000) (-41826955789 / 1000000000000), orderedInterval (15865577687 / 1000000000000) (15865588205 / 1000000000000)))) (orderedInterval (2948704278 / 1000000000000) (2948705706 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate347_chunkChecks4_1 :
    compactCertificate347.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1954323412334563 / 4000000000000) 4 (IntervalRat.scale (437 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-23868493607 / 1000000000000) (-23868487182 / 1000000000000), orderedInterval (27103807064 / 1000000000000) (27103813488 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1128329148194827 / 4000000000000) 4 (IntervalRat.scale (437 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (5871144320 / 1000000000000) (5871144321 / 1000000000000), orderedInterval (47131840510 / 1000000000000) (47131840511 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2002239873756743 / 4000000000000) 4 (IntervalRat.scale (437 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-34453894966 / 1000000000000) (-34453885240 / 1000000000000), orderedInterval (9240065634 / 1000000000000) (9240075360 / 1000000000000)))) (orderedInterval (-27945482355 / 1000000000000) (-27945413591 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1870752213788867 / 4000000000000) 4 (IntervalRat.scale (437 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-13543616941 / 1000000000000) (-13543616940 / 1000000000000), orderedInterval (-34304276240 / 1000000000000) (-34304276239 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1335057052463411 / 4000000000000) 4 (IntervalRat.scale (437 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (43653603837 / 1000000000000) (43653603954 / 1000000000000), orderedInterval (1259062456 / 1000000000000) (1259062573 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1513812405814869 / 4000000000000) 4 (IntervalRat.scale (437 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (31987832793 / 1000000000000) (31987888565 / 1000000000000), orderedInterval (-25712101655 / 1000000000000) (-25712045883 / 1000000000000)))) (orderedInterval (26215064705 / 1000000000000) (26215067526 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1262058961091461 / 4000000000000) 4 (IntervalRat.scale (437 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (37825043902 / 1000000000000) (37825114884 / 1000000000000), orderedInterval (-24287650929 / 1000000000000) (-24287579946 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1115067366532681 / 4000000000000) 4 (IntervalRat.scale (437 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (2386247593 / 1000000000000) (2386247597 / 1000000000000), orderedInterval (-47732775134 / 1000000000000) (-47732775130 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (323189984659419 / 800000000000) 4 (IntervalRat.scale (437 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (18783252961 / 1000000000000) (18783253760 / 1000000000000), orderedInterval (-34995099318 / 1000000000000) (-34995098519 / 1000000000000)))) (orderedInterval (7149595095 / 1000000000000) (7149599033 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate347_chunkChecks4_2 :
    compactCertificate347.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (893960506124993 / 4000000000000) 4 (IntervalRat.scale (437 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-50155769454 / 1000000000000) (-50155769453 / 1000000000000), orderedInterval (-18134153822 / 1000000000000) (-18134153820 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (757820221383673 / 4000000000000) 4 (IntervalRat.scale (437 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (57098043448 / 1000000000000) (57098044094 / 1000000000000), orderedInterval (-10154211696 / 1000000000000) (-10154211051 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (474208707820819 / 4000000000000) 4 (IntervalRat.scale (437 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-3223269054 / 1000000000000) (-3223269042 / 1000000000000), orderedInterval (73222967815 / 1000000000000) (73222967826 / 1000000000000)))) (orderedInterval (6976804422 / 1000000000000) (6976804490 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (255031020212973 / 4000000000000) 4 (IntervalRat.scale (437 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (98965878637 / 1000000000000) (98965878821 / 1000000000000), orderedInterval (-14575970348 / 1000000000000) (-14575970164 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (692458830477919 / 4000000000000) 4 (IntervalRat.scale (437 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-54364912553 / 1000000000000) (-54364912552 / 1000000000000), orderedInterval (-26711024036 / 1000000000000) (-26711024035 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (945493332891263 / 4000000000000) 4 (IntervalRat.scale (437 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-51870130941 / 1000000000000) (-51870130885 / 1000000000000), orderedInterval (-1552915693 / 1000000000000) (-1552915636 / 1000000000000)))) (orderedInterval (5921061578 / 1000000000000) (5921061610 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (399791292179181 / 4000000000000) 4 (IntervalRat.scale (437 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (15934213223 / 1000000000000) (15934213224 / 1000000000000), orderedInterval (78123200608 / 1000000000000) (78123200609 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1625129406959501 / 4000000000000) 4 (IntervalRat.scale (437 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-38531367560 / 1000000000000) (-38531363191 / 1000000000000), orderedInterval (9117813316 / 1000000000000) (9117817685 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1085511128748259 / 4000000000000) 4 (IntervalRat.scale (437 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (44323836922 / 1000000000000) (44323851040 / 1000000000000), orderedInterval (-19607919226 / 1000000000000) (-19607905107 / 1000000000000)))) (orderedInterval (17729971309 / 1000000000000) (17729982242 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate347_chunkChecks4 :
    compactCertificate347.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate347.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate347_chunkChecks4_0
    compactCertificate347_chunkChecks4_1 compactCertificate347_chunkChecks4_2

theorem compactCertificate347_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate347.chunkCheck r b = true :=
  compactCertificate347.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate347_chunkChecks0
    · exact compactCertificate347_chunkChecks1
    · exact compactCertificate347_chunkChecks2
    · exact compactCertificate347_chunkChecks3
    · exact compactCertificate347_chunkChecks4)

theorem compactCertificate347_coefficient0 :
    compactCertificate347.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate347_coefficient1 :
    compactCertificate347.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate347_coefficient2 :
    compactCertificate347.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate347_coefficient3 :
    compactCertificate347.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate347_coefficient4 :
    compactCertificate347.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate347_coefficients : ∀ r : Fin 5,
    compactCertificate347.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate347_coefficient0
  · exact compactCertificate347_coefficient1
  · exact compactCertificate347_coefficient2
  · exact compactCertificate347_coefficient3
  · exact compactCertificate347_coefficient4

theorem compactCertificate347_lower : (1 : ℚ) ≤ compactCertificate347.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate347, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate347_proves {t : ℝ} (ht : t ∈ compactCertificate347.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate347.proves compactCertificate347_states compactCertificate347_chunks
    compactCertificate347_coefficients compactCertificate347_lower ht

end Erdos232
