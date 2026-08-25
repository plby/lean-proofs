/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate406 : CompactCertificate where
  left := 277
  right := 278
  center := 555 / 2
  grid := fun i =>
    match i.val with
    | 0 => 88
    | 1 => 65
    | 2 => 105
    | 3 => 19
    | 4 => 51
    | 5 => 139
    | 6 => 102
    | 7 => 175
    | 8 => 129
    | 9 => 198
    | 10 => 114
    | 11 => 202
    | 12 => 189
    | 13 => 135
    | 14 => 153
    | 15 => 128
    | 16 => 113
    | 17 => 163
    | 18 => 90
    | 19 => 77
    | 20 => 48
    | 21 => 26
    | 22 => 70
    | 23 => 96
    | 24 => 40
    | 25 => 164
    | _ => 110
  point := fun i =>
    match i.val with
    | 0 => 555 / 2
    | 1 => 163524195217011 / 800000000000
    | 2 => 52880364916563 / 160000000000
    | 3 => 47715952329177 / 800000000000
    | 4 => 128171759760069 / 800000000000
    | 5 => 348011260706673 / 800000000000
    | 6 => 256343519520249 / 800000000000
    | 7 => 439248989933277 / 800000000000
    | 8 => 323548817921943 / 800000000000
    | 9 => 496407091004889 / 800000000000
    | 10 => 286600767619281 / 800000000000
    | 11 => 508578091503429 / 800000000000
    | 12 => 475179624097401 / 800000000000
    | 13 => 339110601426633 / 800000000000
    | 14 => 384515279280207 / 800000000000
    | 15 => 320568752130783 / 800000000000
    | 16 => 283232214382443 / 800000000000
    | 17 => 82091735233857 / 160000000000
    | 18 => 227070059908179 / 800000000000
    | 19 => 192489804516219 / 800000000000
    | 20 => 120451182078057 / 800000000000
    | 21 => 64779046324119 / 800000000000
    | 22 => 175887712089357 / 800000000000
    | 23 => 240159633754989 / 800000000000
    | 24 => 101548817921943 / 800000000000
    | 25 => 412790307030903 / 800000000000
    | _ => 275724794716377 / 800000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (46360241285 / 1000000000000) (46360244048 / 1000000000000), orderedInterval (-12118895417 / 1000000000000) (-12118892654 / 1000000000000))
    | 1 => (orderedInterval (-46549401151 / 1000000000000) (-46549401150 / 1000000000000), orderedInterval (-30670024551 / 1000000000000) (-30670024550 / 1000000000000))
    | 2 => (orderedInterval (-43391102155 / 1000000000000) (-43391102136 / 1000000000000), orderedInterval (-6524435551 / 1000000000000) (-6524435532 / 1000000000000))
    | 3 => (orderedInterval (-69507165638 / 1000000000000) (-69507165637 / 1000000000000), orderedInterval (-75852182210 / 1000000000000) (-75852182209 / 1000000000000))
    | 4 => (orderedInterval (-44246268925 / 1000000000000) (-44246268924 / 1000000000000), orderedInterval (-44759684894 / 1000000000000) (-44759684893 / 1000000000000))
    | 5 => (orderedInterval (29537960648 / 1000000000000) (29537999432 / 1000000000000), orderedInterval (-24343512705 / 1000000000000) (-24343473921 / 1000000000000))
    | 6 => (orderedInterval (31091518529 / 1000000000000) (31091518530 / 1000000000000), orderedInterval (31890306472 / 1000000000000) (31890306473 / 1000000000000))
    | 7 => (orderedInterval (-2303271182 / 1000000000000) (-2303271181 / 1000000000000), orderedInterval (-33970905698 / 1000000000000) (-33970905697 / 1000000000000))
    | 8 => (orderedInterval (1758637648 / 1000000000000) (1758637650 / 1000000000000), orderedInterval (-39638029756 / 1000000000000) (-39638029754 / 1000000000000))
    | 9 => (orderedInterval (-21628269762 / 1000000000000) (-21628265886 / 1000000000000), orderedInterval (23643303305 / 1000000000000) (23643307181 / 1000000000000))
    | 10 => (orderedInterval (32874886007 / 1000000000000) (32874886008 / 1000000000000), orderedInterval (26340919540 / 1000000000000) (26340919541 / 1000000000000))
    | 11 => (orderedInterval (29882758505 / 1000000000000) (29882796150 / 1000000000000), orderedInterval (-10436522400 / 1000000000000) (-10436484754 / 1000000000000))
    | 12 => (orderedInterval (-27525419740 / 1000000000000) (-27525419739 / 1000000000000), orderedInterval (-17701036842 / 1000000000000) (-17701036841 / 1000000000000))
    | 13 => (orderedInterval (-20531171137 / 1000000000000) (-20531171136 / 1000000000000), orderedInterval (-32844141353 / 1000000000000) (-32844141352 / 1000000000000))
    | 14 => (orderedInterval (-25218825170 / 1000000000000) (-25218825169 / 1000000000000), orderedInterval (-26213520735 / 1000000000000) (-26213520734 / 1000000000000))
    | 15 => (orderedInterval (-23412770121 / 1000000000000) (-23412766331 / 1000000000000), orderedInterval (32287054096 / 1000000000000) (32287057887 / 1000000000000))
    | 16 => (orderedInterval (7368662895 / 1000000000000) (7368662909 / 1000000000000), orderedInterval (-41769966958 / 1000000000000) (-41769966944 / 1000000000000))
    | 17 => (orderedInterval (-34464963883 / 1000000000000) (-34464957833 / 1000000000000), orderedInterval (7311134261 / 1000000000000) (7311140311 / 1000000000000))
    | 18 => (orderedInterval (45124891124 / 1000000000000) (45124896256 / 1000000000000), orderedInterval (-14454568537 / 1000000000000) (-14454563406 / 1000000000000))
    | 19 => (orderedInterval (24908399962 / 1000000000000) (24908402374 / 1000000000000), orderedInterval (-45056286460 / 1000000000000) (-45056284047 / 1000000000000))
    | 20 => (orderedInterval (34103816594 / 1000000000000) (34103816595 / 1000000000000), orderedInterval (55250765481 / 1000000000000) (55250765482 / 1000000000000))
    | 21 => (orderedInterval (6754643046 / 1000000000000) (6754643048 / 1000000000000), orderedInterval (88369652531 / 1000000000000) (88369652534 / 1000000000000))
    | 22 => (orderedInterval (36004057486 / 1000000000000) (36004057487 / 1000000000000), orderedInterval (39909147780 / 1000000000000) (39909147781 / 1000000000000))
    | 23 => (orderedInterval (-26319329186 / 1000000000000) (-26319323897 / 1000000000000), orderedInterval (37832051807 / 1000000000000) (37832057096 / 1000000000000))
    | 24 => (orderedInterval (62620387905 / 1000000000000) (62620401784 / 1000000000000), orderedInterval (-33321500213 / 1000000000000) (-33321486334 / 1000000000000))
    | 25 => (orderedInterval (35119005330 / 1000000000000) (35119005790 / 1000000000000), orderedInterval (631617930 / 1000000000000) (631618391 / 1000000000000))
    | _ => (orderedInterval (-5748785169 / 1000000000000) (-5748785162 / 1000000000000), orderedInterval (42600238670 / 1000000000000) (42600238678 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (15395587249 / 1000000000000) (15395588365 / 1000000000000)
      | 1 => orderedInterval (-2961250858 / 1000000000000) (-2961248067 / 1000000000000)
      | 2 => orderedInterval (113544893 / 1000000000000) (113544909 / 1000000000000)
      | 3 => orderedInterval (10526850369 / 1000000000000) (10526856520 / 1000000000000)
      | 4 => orderedInterval (-1316945851 / 1000000000000) (-1316945817 / 1000000000000)
      | 5 => orderedInterval (-1574486261 / 1000000000000) (-1574486034 / 1000000000000)
      | 6 => orderedInterval (-7514685379 / 1000000000000) (-7514684352 / 1000000000000)
      | 7 => orderedInterval (1075538868 / 1000000000000) (1075539307 / 1000000000000)
      | _ => orderedInterval (-1402628684 / 1000000000000) (-1402628484 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-5470001466 / 1000000000000) (-5470000347 / 1000000000000)
      | 1 => orderedInterval (1946214733 / 1000000000000) (1946219094 / 1000000000000)
      | 2 => orderedInterval (676997622 / 1000000000000) (676997650 / 1000000000000)
      | 3 => orderedInterval (-10273247462 / 1000000000000) (-10273233434 / 1000000000000)
      | 4 => orderedInterval (-3830478750 / 1000000000000) (-3830478696 / 1000000000000)
      | 5 => orderedInterval (3934154204 / 1000000000000) (3934154593 / 1000000000000)
      | 6 => orderedInterval (5551076935 / 1000000000000) (5551077957 / 1000000000000)
      | 7 => orderedInterval (-4330067506 / 1000000000000) (-4330067037 / 1000000000000)
      | _ => orderedInterval (-10114740056 / 1000000000000) (-10114739837 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-14508737722 / 1000000000000) (-14508736596 / 1000000000000)
      | 1 => orderedInterval (5656862654 / 1000000000000) (5656869498 / 1000000000000)
      | 2 => orderedInterval (-370839052 / 1000000000000) (-370839003 / 1000000000000)
      | 3 => orderedInterval (-45532371386 / 1000000000000) (-45532339319 / 1000000000000)
      | 4 => orderedInterval (1884429316 / 1000000000000) (1884429406 / 1000000000000)
      | 5 => orderedInterval (4252551458 / 1000000000000) (4252552139 / 1000000000000)
      | 6 => orderedInterval (8261520172 / 1000000000000) (8261521198 / 1000000000000)
      | 7 => orderedInterval (-1821619731 / 1000000000000) (-1821619225 / 1000000000000)
      | _ => orderedInterval (8177523016 / 1000000000000) (8177523326 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (5616742222 / 1000000000000) (5616743352 / 1000000000000)
      | 1 => orderedInterval (-6380713187 / 1000000000000) (-6380702462 / 1000000000000)
      | 2 => orderedInterval (-5149218301 / 1000000000000) (-5149218213 / 1000000000000)
      | 3 => orderedInterval (60772195086 / 1000000000000) (60772268313 / 1000000000000)
      | 4 => orderedInterval (7240009384 / 1000000000000) (7240009536 / 1000000000000)
      | 5 => orderedInterval (-7285033274 / 1000000000000) (-7285032071 / 1000000000000)
      | 6 => orderedInterval (-4452567772 / 1000000000000) (-4452566741 / 1000000000000)
      | 7 => orderedInterval (4168052132 / 1000000000000) (4168052678 / 1000000000000)
      | _ => orderedInterval (15633673626 / 1000000000000) (15633674124 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (13083972922 / 1000000000000) (13083974062 / 1000000000000)
      | 1 => orderedInterval (-12812690585 / 1000000000000) (-12812673737 / 1000000000000)
      | 2 => orderedInterval (1317666745 / 1000000000000) (1317666908 / 1000000000000)
      | 3 => orderedInterval (219409400367 / 1000000000000) (219409567879 / 1000000000000)
      | 4 => orderedInterval (956616286 / 1000000000000) (956616549 / 1000000000000)
      | 5 => orderedInterval (-12552355924 / 1000000000000) (-12552353773 / 1000000000000)
      | 6 => orderedInterval (-8565617286 / 1000000000000) (-8565616245 / 1000000000000)
      | 7 => orderedInterval (2409742073 / 1000000000000) (2409742664 / 1000000000000)
      | _ => orderedInterval (-31702346438 / 1000000000000) (-31702345587 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (12341524346 / 1000000000000) (12341536347 / 1000000000000)
    | 1 => orderedInterval (-21910091746 / 1000000000000) (-21910070057 / 1000000000000)
    | 2 => orderedInterval (-34000681275 / 1000000000000) (-34000638576 / 1000000000000)
    | 3 => orderedInterval (70163139916 / 1000000000000) (70163228516 / 1000000000000)
    | _ => orderedInterval (171544388160 / 1000000000000) (171544578720 / 1000000000000)

theorem compactCertificate406_stateChecks0 :
    compactCertificate406.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 88 12 (555 / 2)) (orderedInterval (46360241285 / 1000000000000) (46360244048 / 1000000000000), orderedInterval (-12118895417 / 1000000000000) (-12118892654 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 65 12 (163524195217011 / 800000000000)) (orderedInterval (-46549401151 / 1000000000000) (-46549401150 / 1000000000000), orderedInterval (-30670024551 / 1000000000000) (-30670024550 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 105 12 (52880364916563 / 160000000000)) (orderedInterval (-43391102155 / 1000000000000) (-43391102136 / 1000000000000), orderedInterval (-6524435551 / 1000000000000) (-6524435532 / 1000000000000))) = true
  rfl'

theorem compactCertificate406_stateChecks1 :
    compactCertificate406.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 19 12 (47715952329177 / 800000000000)) (orderedInterval (-69507165638 / 1000000000000) (-69507165637 / 1000000000000), orderedInterval (-75852182210 / 1000000000000) (-75852182209 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (128171759760069 / 800000000000)) (orderedInterval (-44246268925 / 1000000000000) (-44246268924 / 1000000000000), orderedInterval (-44759684894 / 1000000000000) (-44759684893 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 139 12 (348011260706673 / 800000000000)) (orderedInterval (29537960648 / 1000000000000) (29537999432 / 1000000000000), orderedInterval (-24343512705 / 1000000000000) (-24343473921 / 1000000000000))) = true
  rfl'

theorem compactCertificate406_stateChecks2 :
    compactCertificate406.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 102 12 (256343519520249 / 800000000000)) (orderedInterval (31091518529 / 1000000000000) (31091518530 / 1000000000000), orderedInterval (31890306472 / 1000000000000) (31890306473 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 175 12 (439248989933277 / 800000000000)) (orderedInterval (-2303271182 / 1000000000000) (-2303271181 / 1000000000000), orderedInterval (-33970905698 / 1000000000000) (-33970905697 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 129 12 (323548817921943 / 800000000000)) (orderedInterval (1758637648 / 1000000000000) (1758637650 / 1000000000000), orderedInterval (-39638029756 / 1000000000000) (-39638029754 / 1000000000000))) = true
  rfl'

theorem compactCertificate406_stateChecks3 :
    compactCertificate406.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 198 12 (496407091004889 / 800000000000)) (orderedInterval (-21628269762 / 1000000000000) (-21628265886 / 1000000000000), orderedInterval (23643303305 / 1000000000000) (23643307181 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 114 12 (286600767619281 / 800000000000)) (orderedInterval (32874886007 / 1000000000000) (32874886008 / 1000000000000), orderedInterval (26340919540 / 1000000000000) (26340919541 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 202 12 (508578091503429 / 800000000000)) (orderedInterval (29882758505 / 1000000000000) (29882796150 / 1000000000000), orderedInterval (-10436522400 / 1000000000000) (-10436484754 / 1000000000000))) = true
  rfl'

theorem compactCertificate406_stateChecks4 :
    compactCertificate406.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 189 12 (475179624097401 / 800000000000)) (orderedInterval (-27525419740 / 1000000000000) (-27525419739 / 1000000000000), orderedInterval (-17701036842 / 1000000000000) (-17701036841 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 135 12 (339110601426633 / 800000000000)) (orderedInterval (-20531171137 / 1000000000000) (-20531171136 / 1000000000000), orderedInterval (-32844141353 / 1000000000000) (-32844141352 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 153 12 (384515279280207 / 800000000000)) (orderedInterval (-25218825170 / 1000000000000) (-25218825169 / 1000000000000), orderedInterval (-26213520735 / 1000000000000) (-26213520734 / 1000000000000))) = true
  rfl'

theorem compactCertificate406_stateChecks5 :
    compactCertificate406.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 128 12 (320568752130783 / 800000000000)) (orderedInterval (-23412770121 / 1000000000000) (-23412766331 / 1000000000000), orderedInterval (32287054096 / 1000000000000) (32287057887 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 113 12 (283232214382443 / 800000000000)) (orderedInterval (7368662895 / 1000000000000) (7368662909 / 1000000000000), orderedInterval (-41769966958 / 1000000000000) (-41769966944 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 163 12 (82091735233857 / 160000000000)) (orderedInterval (-34464963883 / 1000000000000) (-34464957833 / 1000000000000), orderedInterval (7311134261 / 1000000000000) (7311140311 / 1000000000000))) = true
  rfl'

theorem compactCertificate406_stateChecks6 :
    compactCertificate406.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 90 12 (227070059908179 / 800000000000)) (orderedInterval (45124891124 / 1000000000000) (45124896256 / 1000000000000), orderedInterval (-14454568537 / 1000000000000) (-14454563406 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 77 12 (192489804516219 / 800000000000)) (orderedInterval (24908399962 / 1000000000000) (24908402374 / 1000000000000), orderedInterval (-45056286460 / 1000000000000) (-45056284047 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 48 12 (120451182078057 / 800000000000)) (orderedInterval (34103816594 / 1000000000000) (34103816595 / 1000000000000), orderedInterval (55250765481 / 1000000000000) (55250765482 / 1000000000000))) = true
  rfl'

theorem compactCertificate406_stateChecks7 :
    compactCertificate406.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 26 12 (64779046324119 / 800000000000)) (orderedInterval (6754643046 / 1000000000000) (6754643048 / 1000000000000), orderedInterval (88369652531 / 1000000000000) (88369652534 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (175887712089357 / 800000000000)) (orderedInterval (36004057486 / 1000000000000) (36004057487 / 1000000000000), orderedInterval (39909147780 / 1000000000000) (39909147781 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 96 12 (240159633754989 / 800000000000)) (orderedInterval (-26319329186 / 1000000000000) (-26319323897 / 1000000000000), orderedInterval (37832051807 / 1000000000000) (37832057096 / 1000000000000))) = true
  rfl'

theorem compactCertificate406_stateChecks8 :
    compactCertificate406.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 40 12 (101548817921943 / 800000000000)) (orderedInterval (62620387905 / 1000000000000) (62620401784 / 1000000000000), orderedInterval (-33321500213 / 1000000000000) (-33321486334 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 164 12 (412790307030903 / 800000000000)) (orderedInterval (35119005330 / 1000000000000) (35119005790 / 1000000000000), orderedInterval (631617930 / 1000000000000) (631618391 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 110 12 (275724794716377 / 800000000000)) (orderedInterval (-5748785169 / 1000000000000) (-5748785162 / 1000000000000), orderedInterval (42600238670 / 1000000000000) (42600238678 / 1000000000000))) = true
  rfl'

theorem compactCertificate406_states : ∀ j,
    BesselStateValid (compactCertificate406.point j) (compactCertificate406.state j) :=
  compactCertificate406.statesValid_of_checks3 compactCertificate406_stateChecks0
    compactCertificate406_stateChecks1 compactCertificate406_stateChecks2
    compactCertificate406_stateChecks3 compactCertificate406_stateChecks4
    compactCertificate406_stateChecks5 compactCertificate406_stateChecks6
    compactCertificate406_stateChecks7 compactCertificate406_stateChecks8

theorem compactCertificate406_chunkChecks0_0 :
    compactCertificate406.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (555 / 2) 0 (IntervalRat.scale (555 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (46360241285 / 1000000000000) (46360244048 / 1000000000000), orderedInterval (-12118895417 / 1000000000000) (-12118892654 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (163524195217011 / 800000000000) 0 (IntervalRat.scale (555 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-46549401151 / 1000000000000) (-46549401150 / 1000000000000), orderedInterval (-30670024551 / 1000000000000) (-30670024550 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (52880364916563 / 160000000000) 0 (IntervalRat.scale (555 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-43391102155 / 1000000000000) (-43391102136 / 1000000000000), orderedInterval (-6524435551 / 1000000000000) (-6524435532 / 1000000000000)))) (orderedInterval (15395587249 / 1000000000000) (15395588365 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (47715952329177 / 800000000000) 0 (IntervalRat.scale (555 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-69507165638 / 1000000000000) (-69507165637 / 1000000000000), orderedInterval (-75852182210 / 1000000000000) (-75852182209 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (128171759760069 / 800000000000) 0 (IntervalRat.scale (555 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-44246268925 / 1000000000000) (-44246268924 / 1000000000000), orderedInterval (-44759684894 / 1000000000000) (-44759684893 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (348011260706673 / 800000000000) 0 (IntervalRat.scale (555 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29537960648 / 1000000000000) (29537999432 / 1000000000000), orderedInterval (-24343512705 / 1000000000000) (-24343473921 / 1000000000000)))) (orderedInterval (-2961250858 / 1000000000000) (-2961248067 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (256343519520249 / 800000000000) 0 (IntervalRat.scale (555 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (31091518529 / 1000000000000) (31091518530 / 1000000000000), orderedInterval (31890306472 / 1000000000000) (31890306473 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (439248989933277 / 800000000000) 0 (IntervalRat.scale (555 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-2303271182 / 1000000000000) (-2303271181 / 1000000000000), orderedInterval (-33970905698 / 1000000000000) (-33970905697 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (323548817921943 / 800000000000) 0 (IntervalRat.scale (555 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (1758637648 / 1000000000000) (1758637650 / 1000000000000), orderedInterval (-39638029756 / 1000000000000) (-39638029754 / 1000000000000)))) (orderedInterval (113544893 / 1000000000000) (113544909 / 1000000000000))) = true
  rfl'

theorem compactCertificate406_chunkChecks0_1 :
    compactCertificate406.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (496407091004889 / 800000000000) 0 (IntervalRat.scale (555 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-21628269762 / 1000000000000) (-21628265886 / 1000000000000), orderedInterval (23643303305 / 1000000000000) (23643307181 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (286600767619281 / 800000000000) 0 (IntervalRat.scale (555 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (32874886007 / 1000000000000) (32874886008 / 1000000000000), orderedInterval (26340919540 / 1000000000000) (26340919541 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (508578091503429 / 800000000000) 0 (IntervalRat.scale (555 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (29882758505 / 1000000000000) (29882796150 / 1000000000000), orderedInterval (-10436522400 / 1000000000000) (-10436484754 / 1000000000000)))) (orderedInterval (10526850369 / 1000000000000) (10526856520 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (475179624097401 / 800000000000) 0 (IntervalRat.scale (555 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-27525419740 / 1000000000000) (-27525419739 / 1000000000000), orderedInterval (-17701036842 / 1000000000000) (-17701036841 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (339110601426633 / 800000000000) 0 (IntervalRat.scale (555 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-20531171137 / 1000000000000) (-20531171136 / 1000000000000), orderedInterval (-32844141353 / 1000000000000) (-32844141352 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (384515279280207 / 800000000000) 0 (IntervalRat.scale (555 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-25218825170 / 1000000000000) (-25218825169 / 1000000000000), orderedInterval (-26213520735 / 1000000000000) (-26213520734 / 1000000000000)))) (orderedInterval (-1316945851 / 1000000000000) (-1316945817 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (320568752130783 / 800000000000) 0 (IntervalRat.scale (555 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-23412770121 / 1000000000000) (-23412766331 / 1000000000000), orderedInterval (32287054096 / 1000000000000) (32287057887 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (283232214382443 / 800000000000) 0 (IntervalRat.scale (555 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (7368662895 / 1000000000000) (7368662909 / 1000000000000), orderedInterval (-41769966958 / 1000000000000) (-41769966944 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (82091735233857 / 160000000000) 0 (IntervalRat.scale (555 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-34464963883 / 1000000000000) (-34464957833 / 1000000000000), orderedInterval (7311134261 / 1000000000000) (7311140311 / 1000000000000)))) (orderedInterval (-1574486261 / 1000000000000) (-1574486034 / 1000000000000))) = true
  rfl'

theorem compactCertificate406_chunkChecks0_2 :
    compactCertificate406.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (227070059908179 / 800000000000) 0 (IntervalRat.scale (555 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (45124891124 / 1000000000000) (45124896256 / 1000000000000), orderedInterval (-14454568537 / 1000000000000) (-14454563406 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (192489804516219 / 800000000000) 0 (IntervalRat.scale (555 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (24908399962 / 1000000000000) (24908402374 / 1000000000000), orderedInterval (-45056286460 / 1000000000000) (-45056284047 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (120451182078057 / 800000000000) 0 (IntervalRat.scale (555 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (34103816594 / 1000000000000) (34103816595 / 1000000000000), orderedInterval (55250765481 / 1000000000000) (55250765482 / 1000000000000)))) (orderedInterval (-7514685379 / 1000000000000) (-7514684352 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (64779046324119 / 800000000000) 0 (IntervalRat.scale (555 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (6754643046 / 1000000000000) (6754643048 / 1000000000000), orderedInterval (88369652531 / 1000000000000) (88369652534 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (175887712089357 / 800000000000) 0 (IntervalRat.scale (555 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (36004057486 / 1000000000000) (36004057487 / 1000000000000), orderedInterval (39909147780 / 1000000000000) (39909147781 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (240159633754989 / 800000000000) 0 (IntervalRat.scale (555 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-26319329186 / 1000000000000) (-26319323897 / 1000000000000), orderedInterval (37832051807 / 1000000000000) (37832057096 / 1000000000000)))) (orderedInterval (1075538868 / 1000000000000) (1075539307 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (101548817921943 / 800000000000) 0 (IntervalRat.scale (555 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (62620387905 / 1000000000000) (62620401784 / 1000000000000), orderedInterval (-33321500213 / 1000000000000) (-33321486334 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (412790307030903 / 800000000000) 0 (IntervalRat.scale (555 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (35119005330 / 1000000000000) (35119005790 / 1000000000000), orderedInterval (631617930 / 1000000000000) (631618391 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (275724794716377 / 800000000000) 0 (IntervalRat.scale (555 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-5748785169 / 1000000000000) (-5748785162 / 1000000000000), orderedInterval (42600238670 / 1000000000000) (42600238678 / 1000000000000)))) (orderedInterval (-1402628684 / 1000000000000) (-1402628484 / 1000000000000))) = true
  rfl'

theorem compactCertificate406_chunkChecks0 :
    compactCertificate406.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate406.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate406_chunkChecks0_0
    compactCertificate406_chunkChecks0_1 compactCertificate406_chunkChecks0_2

theorem compactCertificate406_chunkChecks1_0 :
    compactCertificate406.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (555 / 2) 1 (IntervalRat.scale (555 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (46360241285 / 1000000000000) (46360244048 / 1000000000000), orderedInterval (-12118895417 / 1000000000000) (-12118892654 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (163524195217011 / 800000000000) 1 (IntervalRat.scale (555 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-46549401151 / 1000000000000) (-46549401150 / 1000000000000), orderedInterval (-30670024551 / 1000000000000) (-30670024550 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (52880364916563 / 160000000000) 1 (IntervalRat.scale (555 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-43391102155 / 1000000000000) (-43391102136 / 1000000000000), orderedInterval (-6524435551 / 1000000000000) (-6524435532 / 1000000000000)))) (orderedInterval (-5470001466 / 1000000000000) (-5470000347 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (47715952329177 / 800000000000) 1 (IntervalRat.scale (555 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-69507165638 / 1000000000000) (-69507165637 / 1000000000000), orderedInterval (-75852182210 / 1000000000000) (-75852182209 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (128171759760069 / 800000000000) 1 (IntervalRat.scale (555 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-44246268925 / 1000000000000) (-44246268924 / 1000000000000), orderedInterval (-44759684894 / 1000000000000) (-44759684893 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (348011260706673 / 800000000000) 1 (IntervalRat.scale (555 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29537960648 / 1000000000000) (29537999432 / 1000000000000), orderedInterval (-24343512705 / 1000000000000) (-24343473921 / 1000000000000)))) (orderedInterval (1946214733 / 1000000000000) (1946219094 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (256343519520249 / 800000000000) 1 (IntervalRat.scale (555 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (31091518529 / 1000000000000) (31091518530 / 1000000000000), orderedInterval (31890306472 / 1000000000000) (31890306473 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (439248989933277 / 800000000000) 1 (IntervalRat.scale (555 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-2303271182 / 1000000000000) (-2303271181 / 1000000000000), orderedInterval (-33970905698 / 1000000000000) (-33970905697 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (323548817921943 / 800000000000) 1 (IntervalRat.scale (555 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (1758637648 / 1000000000000) (1758637650 / 1000000000000), orderedInterval (-39638029756 / 1000000000000) (-39638029754 / 1000000000000)))) (orderedInterval (676997622 / 1000000000000) (676997650 / 1000000000000))) = true
  rfl'

theorem compactCertificate406_chunkChecks1_1 :
    compactCertificate406.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (496407091004889 / 800000000000) 1 (IntervalRat.scale (555 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-21628269762 / 1000000000000) (-21628265886 / 1000000000000), orderedInterval (23643303305 / 1000000000000) (23643307181 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (286600767619281 / 800000000000) 1 (IntervalRat.scale (555 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (32874886007 / 1000000000000) (32874886008 / 1000000000000), orderedInterval (26340919540 / 1000000000000) (26340919541 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (508578091503429 / 800000000000) 1 (IntervalRat.scale (555 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (29882758505 / 1000000000000) (29882796150 / 1000000000000), orderedInterval (-10436522400 / 1000000000000) (-10436484754 / 1000000000000)))) (orderedInterval (-10273247462 / 1000000000000) (-10273233434 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (475179624097401 / 800000000000) 1 (IntervalRat.scale (555 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-27525419740 / 1000000000000) (-27525419739 / 1000000000000), orderedInterval (-17701036842 / 1000000000000) (-17701036841 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (339110601426633 / 800000000000) 1 (IntervalRat.scale (555 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-20531171137 / 1000000000000) (-20531171136 / 1000000000000), orderedInterval (-32844141353 / 1000000000000) (-32844141352 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (384515279280207 / 800000000000) 1 (IntervalRat.scale (555 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-25218825170 / 1000000000000) (-25218825169 / 1000000000000), orderedInterval (-26213520735 / 1000000000000) (-26213520734 / 1000000000000)))) (orderedInterval (-3830478750 / 1000000000000) (-3830478696 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (320568752130783 / 800000000000) 1 (IntervalRat.scale (555 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-23412770121 / 1000000000000) (-23412766331 / 1000000000000), orderedInterval (32287054096 / 1000000000000) (32287057887 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (283232214382443 / 800000000000) 1 (IntervalRat.scale (555 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (7368662895 / 1000000000000) (7368662909 / 1000000000000), orderedInterval (-41769966958 / 1000000000000) (-41769966944 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (82091735233857 / 160000000000) 1 (IntervalRat.scale (555 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-34464963883 / 1000000000000) (-34464957833 / 1000000000000), orderedInterval (7311134261 / 1000000000000) (7311140311 / 1000000000000)))) (orderedInterval (3934154204 / 1000000000000) (3934154593 / 1000000000000))) = true
  rfl'

theorem compactCertificate406_chunkChecks1_2 :
    compactCertificate406.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (227070059908179 / 800000000000) 1 (IntervalRat.scale (555 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (45124891124 / 1000000000000) (45124896256 / 1000000000000), orderedInterval (-14454568537 / 1000000000000) (-14454563406 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (192489804516219 / 800000000000) 1 (IntervalRat.scale (555 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (24908399962 / 1000000000000) (24908402374 / 1000000000000), orderedInterval (-45056286460 / 1000000000000) (-45056284047 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (120451182078057 / 800000000000) 1 (IntervalRat.scale (555 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (34103816594 / 1000000000000) (34103816595 / 1000000000000), orderedInterval (55250765481 / 1000000000000) (55250765482 / 1000000000000)))) (orderedInterval (5551076935 / 1000000000000) (5551077957 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (64779046324119 / 800000000000) 1 (IntervalRat.scale (555 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (6754643046 / 1000000000000) (6754643048 / 1000000000000), orderedInterval (88369652531 / 1000000000000) (88369652534 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (175887712089357 / 800000000000) 1 (IntervalRat.scale (555 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (36004057486 / 1000000000000) (36004057487 / 1000000000000), orderedInterval (39909147780 / 1000000000000) (39909147781 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (240159633754989 / 800000000000) 1 (IntervalRat.scale (555 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-26319329186 / 1000000000000) (-26319323897 / 1000000000000), orderedInterval (37832051807 / 1000000000000) (37832057096 / 1000000000000)))) (orderedInterval (-4330067506 / 1000000000000) (-4330067037 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (101548817921943 / 800000000000) 1 (IntervalRat.scale (555 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (62620387905 / 1000000000000) (62620401784 / 1000000000000), orderedInterval (-33321500213 / 1000000000000) (-33321486334 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (412790307030903 / 800000000000) 1 (IntervalRat.scale (555 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (35119005330 / 1000000000000) (35119005790 / 1000000000000), orderedInterval (631617930 / 1000000000000) (631618391 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (275724794716377 / 800000000000) 1 (IntervalRat.scale (555 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-5748785169 / 1000000000000) (-5748785162 / 1000000000000), orderedInterval (42600238670 / 1000000000000) (42600238678 / 1000000000000)))) (orderedInterval (-10114740056 / 1000000000000) (-10114739837 / 1000000000000))) = true
  rfl'

theorem compactCertificate406_chunkChecks1 :
    compactCertificate406.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate406.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate406_chunkChecks1_0
    compactCertificate406_chunkChecks1_1 compactCertificate406_chunkChecks1_2

theorem compactCertificate406_chunkChecks2_0 :
    compactCertificate406.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (555 / 2) 2 (IntervalRat.scale (555 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (46360241285 / 1000000000000) (46360244048 / 1000000000000), orderedInterval (-12118895417 / 1000000000000) (-12118892654 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (163524195217011 / 800000000000) 2 (IntervalRat.scale (555 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-46549401151 / 1000000000000) (-46549401150 / 1000000000000), orderedInterval (-30670024551 / 1000000000000) (-30670024550 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (52880364916563 / 160000000000) 2 (IntervalRat.scale (555 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-43391102155 / 1000000000000) (-43391102136 / 1000000000000), orderedInterval (-6524435551 / 1000000000000) (-6524435532 / 1000000000000)))) (orderedInterval (-14508737722 / 1000000000000) (-14508736596 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (47715952329177 / 800000000000) 2 (IntervalRat.scale (555 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-69507165638 / 1000000000000) (-69507165637 / 1000000000000), orderedInterval (-75852182210 / 1000000000000) (-75852182209 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (128171759760069 / 800000000000) 2 (IntervalRat.scale (555 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-44246268925 / 1000000000000) (-44246268924 / 1000000000000), orderedInterval (-44759684894 / 1000000000000) (-44759684893 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (348011260706673 / 800000000000) 2 (IntervalRat.scale (555 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29537960648 / 1000000000000) (29537999432 / 1000000000000), orderedInterval (-24343512705 / 1000000000000) (-24343473921 / 1000000000000)))) (orderedInterval (5656862654 / 1000000000000) (5656869498 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (256343519520249 / 800000000000) 2 (IntervalRat.scale (555 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (31091518529 / 1000000000000) (31091518530 / 1000000000000), orderedInterval (31890306472 / 1000000000000) (31890306473 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (439248989933277 / 800000000000) 2 (IntervalRat.scale (555 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-2303271182 / 1000000000000) (-2303271181 / 1000000000000), orderedInterval (-33970905698 / 1000000000000) (-33970905697 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (323548817921943 / 800000000000) 2 (IntervalRat.scale (555 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (1758637648 / 1000000000000) (1758637650 / 1000000000000), orderedInterval (-39638029756 / 1000000000000) (-39638029754 / 1000000000000)))) (orderedInterval (-370839052 / 1000000000000) (-370839003 / 1000000000000))) = true
  rfl'

theorem compactCertificate406_chunkChecks2_1 :
    compactCertificate406.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (496407091004889 / 800000000000) 2 (IntervalRat.scale (555 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-21628269762 / 1000000000000) (-21628265886 / 1000000000000), orderedInterval (23643303305 / 1000000000000) (23643307181 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (286600767619281 / 800000000000) 2 (IntervalRat.scale (555 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (32874886007 / 1000000000000) (32874886008 / 1000000000000), orderedInterval (26340919540 / 1000000000000) (26340919541 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (508578091503429 / 800000000000) 2 (IntervalRat.scale (555 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (29882758505 / 1000000000000) (29882796150 / 1000000000000), orderedInterval (-10436522400 / 1000000000000) (-10436484754 / 1000000000000)))) (orderedInterval (-45532371386 / 1000000000000) (-45532339319 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (475179624097401 / 800000000000) 2 (IntervalRat.scale (555 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-27525419740 / 1000000000000) (-27525419739 / 1000000000000), orderedInterval (-17701036842 / 1000000000000) (-17701036841 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (339110601426633 / 800000000000) 2 (IntervalRat.scale (555 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-20531171137 / 1000000000000) (-20531171136 / 1000000000000), orderedInterval (-32844141353 / 1000000000000) (-32844141352 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (384515279280207 / 800000000000) 2 (IntervalRat.scale (555 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-25218825170 / 1000000000000) (-25218825169 / 1000000000000), orderedInterval (-26213520735 / 1000000000000) (-26213520734 / 1000000000000)))) (orderedInterval (1884429316 / 1000000000000) (1884429406 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (320568752130783 / 800000000000) 2 (IntervalRat.scale (555 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-23412770121 / 1000000000000) (-23412766331 / 1000000000000), orderedInterval (32287054096 / 1000000000000) (32287057887 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (283232214382443 / 800000000000) 2 (IntervalRat.scale (555 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (7368662895 / 1000000000000) (7368662909 / 1000000000000), orderedInterval (-41769966958 / 1000000000000) (-41769966944 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (82091735233857 / 160000000000) 2 (IntervalRat.scale (555 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-34464963883 / 1000000000000) (-34464957833 / 1000000000000), orderedInterval (7311134261 / 1000000000000) (7311140311 / 1000000000000)))) (orderedInterval (4252551458 / 1000000000000) (4252552139 / 1000000000000))) = true
  rfl'

theorem compactCertificate406_chunkChecks2_2 :
    compactCertificate406.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (227070059908179 / 800000000000) 2 (IntervalRat.scale (555 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (45124891124 / 1000000000000) (45124896256 / 1000000000000), orderedInterval (-14454568537 / 1000000000000) (-14454563406 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (192489804516219 / 800000000000) 2 (IntervalRat.scale (555 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (24908399962 / 1000000000000) (24908402374 / 1000000000000), orderedInterval (-45056286460 / 1000000000000) (-45056284047 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (120451182078057 / 800000000000) 2 (IntervalRat.scale (555 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (34103816594 / 1000000000000) (34103816595 / 1000000000000), orderedInterval (55250765481 / 1000000000000) (55250765482 / 1000000000000)))) (orderedInterval (8261520172 / 1000000000000) (8261521198 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (64779046324119 / 800000000000) 2 (IntervalRat.scale (555 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (6754643046 / 1000000000000) (6754643048 / 1000000000000), orderedInterval (88369652531 / 1000000000000) (88369652534 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (175887712089357 / 800000000000) 2 (IntervalRat.scale (555 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (36004057486 / 1000000000000) (36004057487 / 1000000000000), orderedInterval (39909147780 / 1000000000000) (39909147781 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (240159633754989 / 800000000000) 2 (IntervalRat.scale (555 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-26319329186 / 1000000000000) (-26319323897 / 1000000000000), orderedInterval (37832051807 / 1000000000000) (37832057096 / 1000000000000)))) (orderedInterval (-1821619731 / 1000000000000) (-1821619225 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (101548817921943 / 800000000000) 2 (IntervalRat.scale (555 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (62620387905 / 1000000000000) (62620401784 / 1000000000000), orderedInterval (-33321500213 / 1000000000000) (-33321486334 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (412790307030903 / 800000000000) 2 (IntervalRat.scale (555 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (35119005330 / 1000000000000) (35119005790 / 1000000000000), orderedInterval (631617930 / 1000000000000) (631618391 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (275724794716377 / 800000000000) 2 (IntervalRat.scale (555 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-5748785169 / 1000000000000) (-5748785162 / 1000000000000), orderedInterval (42600238670 / 1000000000000) (42600238678 / 1000000000000)))) (orderedInterval (8177523016 / 1000000000000) (8177523326 / 1000000000000))) = true
  rfl'

theorem compactCertificate406_chunkChecks2 :
    compactCertificate406.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate406.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate406_chunkChecks2_0
    compactCertificate406_chunkChecks2_1 compactCertificate406_chunkChecks2_2

theorem compactCertificate406_chunkChecks3_0 :
    compactCertificate406.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (555 / 2) 3 (IntervalRat.scale (555 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (46360241285 / 1000000000000) (46360244048 / 1000000000000), orderedInterval (-12118895417 / 1000000000000) (-12118892654 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (163524195217011 / 800000000000) 3 (IntervalRat.scale (555 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-46549401151 / 1000000000000) (-46549401150 / 1000000000000), orderedInterval (-30670024551 / 1000000000000) (-30670024550 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (52880364916563 / 160000000000) 3 (IntervalRat.scale (555 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-43391102155 / 1000000000000) (-43391102136 / 1000000000000), orderedInterval (-6524435551 / 1000000000000) (-6524435532 / 1000000000000)))) (orderedInterval (5616742222 / 1000000000000) (5616743352 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (47715952329177 / 800000000000) 3 (IntervalRat.scale (555 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-69507165638 / 1000000000000) (-69507165637 / 1000000000000), orderedInterval (-75852182210 / 1000000000000) (-75852182209 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (128171759760069 / 800000000000) 3 (IntervalRat.scale (555 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-44246268925 / 1000000000000) (-44246268924 / 1000000000000), orderedInterval (-44759684894 / 1000000000000) (-44759684893 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (348011260706673 / 800000000000) 3 (IntervalRat.scale (555 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29537960648 / 1000000000000) (29537999432 / 1000000000000), orderedInterval (-24343512705 / 1000000000000) (-24343473921 / 1000000000000)))) (orderedInterval (-6380713187 / 1000000000000) (-6380702462 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (256343519520249 / 800000000000) 3 (IntervalRat.scale (555 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (31091518529 / 1000000000000) (31091518530 / 1000000000000), orderedInterval (31890306472 / 1000000000000) (31890306473 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (439248989933277 / 800000000000) 3 (IntervalRat.scale (555 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-2303271182 / 1000000000000) (-2303271181 / 1000000000000), orderedInterval (-33970905698 / 1000000000000) (-33970905697 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (323548817921943 / 800000000000) 3 (IntervalRat.scale (555 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (1758637648 / 1000000000000) (1758637650 / 1000000000000), orderedInterval (-39638029756 / 1000000000000) (-39638029754 / 1000000000000)))) (orderedInterval (-5149218301 / 1000000000000) (-5149218213 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate406_chunkChecks3_1 :
    compactCertificate406.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (496407091004889 / 800000000000) 3 (IntervalRat.scale (555 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-21628269762 / 1000000000000) (-21628265886 / 1000000000000), orderedInterval (23643303305 / 1000000000000) (23643307181 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (286600767619281 / 800000000000) 3 (IntervalRat.scale (555 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (32874886007 / 1000000000000) (32874886008 / 1000000000000), orderedInterval (26340919540 / 1000000000000) (26340919541 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (508578091503429 / 800000000000) 3 (IntervalRat.scale (555 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (29882758505 / 1000000000000) (29882796150 / 1000000000000), orderedInterval (-10436522400 / 1000000000000) (-10436484754 / 1000000000000)))) (orderedInterval (60772195086 / 1000000000000) (60772268313 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (475179624097401 / 800000000000) 3 (IntervalRat.scale (555 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-27525419740 / 1000000000000) (-27525419739 / 1000000000000), orderedInterval (-17701036842 / 1000000000000) (-17701036841 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (339110601426633 / 800000000000) 3 (IntervalRat.scale (555 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-20531171137 / 1000000000000) (-20531171136 / 1000000000000), orderedInterval (-32844141353 / 1000000000000) (-32844141352 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (384515279280207 / 800000000000) 3 (IntervalRat.scale (555 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-25218825170 / 1000000000000) (-25218825169 / 1000000000000), orderedInterval (-26213520735 / 1000000000000) (-26213520734 / 1000000000000)))) (orderedInterval (7240009384 / 1000000000000) (7240009536 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (320568752130783 / 800000000000) 3 (IntervalRat.scale (555 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-23412770121 / 1000000000000) (-23412766331 / 1000000000000), orderedInterval (32287054096 / 1000000000000) (32287057887 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (283232214382443 / 800000000000) 3 (IntervalRat.scale (555 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (7368662895 / 1000000000000) (7368662909 / 1000000000000), orderedInterval (-41769966958 / 1000000000000) (-41769966944 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (82091735233857 / 160000000000) 3 (IntervalRat.scale (555 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-34464963883 / 1000000000000) (-34464957833 / 1000000000000), orderedInterval (7311134261 / 1000000000000) (7311140311 / 1000000000000)))) (orderedInterval (-7285033274 / 1000000000000) (-7285032071 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate406_chunkChecks3_2 :
    compactCertificate406.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (227070059908179 / 800000000000) 3 (IntervalRat.scale (555 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (45124891124 / 1000000000000) (45124896256 / 1000000000000), orderedInterval (-14454568537 / 1000000000000) (-14454563406 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (192489804516219 / 800000000000) 3 (IntervalRat.scale (555 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (24908399962 / 1000000000000) (24908402374 / 1000000000000), orderedInterval (-45056286460 / 1000000000000) (-45056284047 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (120451182078057 / 800000000000) 3 (IntervalRat.scale (555 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (34103816594 / 1000000000000) (34103816595 / 1000000000000), orderedInterval (55250765481 / 1000000000000) (55250765482 / 1000000000000)))) (orderedInterval (-4452567772 / 1000000000000) (-4452566741 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (64779046324119 / 800000000000) 3 (IntervalRat.scale (555 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (6754643046 / 1000000000000) (6754643048 / 1000000000000), orderedInterval (88369652531 / 1000000000000) (88369652534 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (175887712089357 / 800000000000) 3 (IntervalRat.scale (555 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (36004057486 / 1000000000000) (36004057487 / 1000000000000), orderedInterval (39909147780 / 1000000000000) (39909147781 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (240159633754989 / 800000000000) 3 (IntervalRat.scale (555 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-26319329186 / 1000000000000) (-26319323897 / 1000000000000), orderedInterval (37832051807 / 1000000000000) (37832057096 / 1000000000000)))) (orderedInterval (4168052132 / 1000000000000) (4168052678 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (101548817921943 / 800000000000) 3 (IntervalRat.scale (555 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (62620387905 / 1000000000000) (62620401784 / 1000000000000), orderedInterval (-33321500213 / 1000000000000) (-33321486334 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (412790307030903 / 800000000000) 3 (IntervalRat.scale (555 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (35119005330 / 1000000000000) (35119005790 / 1000000000000), orderedInterval (631617930 / 1000000000000) (631618391 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (275724794716377 / 800000000000) 3 (IntervalRat.scale (555 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-5748785169 / 1000000000000) (-5748785162 / 1000000000000), orderedInterval (42600238670 / 1000000000000) (42600238678 / 1000000000000)))) (orderedInterval (15633673626 / 1000000000000) (15633674124 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate406_chunkChecks3 :
    compactCertificate406.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate406.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate406_chunkChecks3_0
    compactCertificate406_chunkChecks3_1 compactCertificate406_chunkChecks3_2

theorem compactCertificate406_chunkChecks4_0 :
    compactCertificate406.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (555 / 2) 4 (IntervalRat.scale (555 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (46360241285 / 1000000000000) (46360244048 / 1000000000000), orderedInterval (-12118895417 / 1000000000000) (-12118892654 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (163524195217011 / 800000000000) 4 (IntervalRat.scale (555 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-46549401151 / 1000000000000) (-46549401150 / 1000000000000), orderedInterval (-30670024551 / 1000000000000) (-30670024550 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (52880364916563 / 160000000000) 4 (IntervalRat.scale (555 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-43391102155 / 1000000000000) (-43391102136 / 1000000000000), orderedInterval (-6524435551 / 1000000000000) (-6524435532 / 1000000000000)))) (orderedInterval (13083972922 / 1000000000000) (13083974062 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (47715952329177 / 800000000000) 4 (IntervalRat.scale (555 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-69507165638 / 1000000000000) (-69507165637 / 1000000000000), orderedInterval (-75852182210 / 1000000000000) (-75852182209 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (128171759760069 / 800000000000) 4 (IntervalRat.scale (555 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-44246268925 / 1000000000000) (-44246268924 / 1000000000000), orderedInterval (-44759684894 / 1000000000000) (-44759684893 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (348011260706673 / 800000000000) 4 (IntervalRat.scale (555 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29537960648 / 1000000000000) (29537999432 / 1000000000000), orderedInterval (-24343512705 / 1000000000000) (-24343473921 / 1000000000000)))) (orderedInterval (-12812690585 / 1000000000000) (-12812673737 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (256343519520249 / 800000000000) 4 (IntervalRat.scale (555 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (31091518529 / 1000000000000) (31091518530 / 1000000000000), orderedInterval (31890306472 / 1000000000000) (31890306473 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (439248989933277 / 800000000000) 4 (IntervalRat.scale (555 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-2303271182 / 1000000000000) (-2303271181 / 1000000000000), orderedInterval (-33970905698 / 1000000000000) (-33970905697 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (323548817921943 / 800000000000) 4 (IntervalRat.scale (555 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (1758637648 / 1000000000000) (1758637650 / 1000000000000), orderedInterval (-39638029756 / 1000000000000) (-39638029754 / 1000000000000)))) (orderedInterval (1317666745 / 1000000000000) (1317666908 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate406_chunkChecks4_1 :
    compactCertificate406.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (496407091004889 / 800000000000) 4 (IntervalRat.scale (555 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-21628269762 / 1000000000000) (-21628265886 / 1000000000000), orderedInterval (23643303305 / 1000000000000) (23643307181 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (286600767619281 / 800000000000) 4 (IntervalRat.scale (555 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (32874886007 / 1000000000000) (32874886008 / 1000000000000), orderedInterval (26340919540 / 1000000000000) (26340919541 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (508578091503429 / 800000000000) 4 (IntervalRat.scale (555 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (29882758505 / 1000000000000) (29882796150 / 1000000000000), orderedInterval (-10436522400 / 1000000000000) (-10436484754 / 1000000000000)))) (orderedInterval (219409400367 / 1000000000000) (219409567879 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (475179624097401 / 800000000000) 4 (IntervalRat.scale (555 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-27525419740 / 1000000000000) (-27525419739 / 1000000000000), orderedInterval (-17701036842 / 1000000000000) (-17701036841 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (339110601426633 / 800000000000) 4 (IntervalRat.scale (555 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-20531171137 / 1000000000000) (-20531171136 / 1000000000000), orderedInterval (-32844141353 / 1000000000000) (-32844141352 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (384515279280207 / 800000000000) 4 (IntervalRat.scale (555 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-25218825170 / 1000000000000) (-25218825169 / 1000000000000), orderedInterval (-26213520735 / 1000000000000) (-26213520734 / 1000000000000)))) (orderedInterval (956616286 / 1000000000000) (956616549 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (320568752130783 / 800000000000) 4 (IntervalRat.scale (555 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-23412770121 / 1000000000000) (-23412766331 / 1000000000000), orderedInterval (32287054096 / 1000000000000) (32287057887 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (283232214382443 / 800000000000) 4 (IntervalRat.scale (555 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (7368662895 / 1000000000000) (7368662909 / 1000000000000), orderedInterval (-41769966958 / 1000000000000) (-41769966944 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (82091735233857 / 160000000000) 4 (IntervalRat.scale (555 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-34464963883 / 1000000000000) (-34464957833 / 1000000000000), orderedInterval (7311134261 / 1000000000000) (7311140311 / 1000000000000)))) (orderedInterval (-12552355924 / 1000000000000) (-12552353773 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate406_chunkChecks4_2 :
    compactCertificate406.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (227070059908179 / 800000000000) 4 (IntervalRat.scale (555 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (45124891124 / 1000000000000) (45124896256 / 1000000000000), orderedInterval (-14454568537 / 1000000000000) (-14454563406 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (192489804516219 / 800000000000) 4 (IntervalRat.scale (555 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (24908399962 / 1000000000000) (24908402374 / 1000000000000), orderedInterval (-45056286460 / 1000000000000) (-45056284047 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (120451182078057 / 800000000000) 4 (IntervalRat.scale (555 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (34103816594 / 1000000000000) (34103816595 / 1000000000000), orderedInterval (55250765481 / 1000000000000) (55250765482 / 1000000000000)))) (orderedInterval (-8565617286 / 1000000000000) (-8565616245 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (64779046324119 / 800000000000) 4 (IntervalRat.scale (555 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (6754643046 / 1000000000000) (6754643048 / 1000000000000), orderedInterval (88369652531 / 1000000000000) (88369652534 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (175887712089357 / 800000000000) 4 (IntervalRat.scale (555 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (36004057486 / 1000000000000) (36004057487 / 1000000000000), orderedInterval (39909147780 / 1000000000000) (39909147781 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (240159633754989 / 800000000000) 4 (IntervalRat.scale (555 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-26319329186 / 1000000000000) (-26319323897 / 1000000000000), orderedInterval (37832051807 / 1000000000000) (37832057096 / 1000000000000)))) (orderedInterval (2409742073 / 1000000000000) (2409742664 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (101548817921943 / 800000000000) 4 (IntervalRat.scale (555 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (62620387905 / 1000000000000) (62620401784 / 1000000000000), orderedInterval (-33321500213 / 1000000000000) (-33321486334 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (412790307030903 / 800000000000) 4 (IntervalRat.scale (555 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (35119005330 / 1000000000000) (35119005790 / 1000000000000), orderedInterval (631617930 / 1000000000000) (631618391 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (275724794716377 / 800000000000) 4 (IntervalRat.scale (555 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-5748785169 / 1000000000000) (-5748785162 / 1000000000000), orderedInterval (42600238670 / 1000000000000) (42600238678 / 1000000000000)))) (orderedInterval (-31702346438 / 1000000000000) (-31702345587 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate406_chunkChecks4 :
    compactCertificate406.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate406.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate406_chunkChecks4_0
    compactCertificate406_chunkChecks4_1 compactCertificate406_chunkChecks4_2

theorem compactCertificate406_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate406.chunkCheck r b = true :=
  compactCertificate406.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate406_chunkChecks0
    · exact compactCertificate406_chunkChecks1
    · exact compactCertificate406_chunkChecks2
    · exact compactCertificate406_chunkChecks3
    · exact compactCertificate406_chunkChecks4)

theorem compactCertificate406_coefficient0 :
    compactCertificate406.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate406_coefficient1 :
    compactCertificate406.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate406_coefficient2 :
    compactCertificate406.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate406_coefficient3 :
    compactCertificate406.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate406_coefficient4 :
    compactCertificate406.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate406_coefficients : ∀ r : Fin 5,
    compactCertificate406.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate406_coefficient0
  · exact compactCertificate406_coefficient1
  · exact compactCertificate406_coefficient2
  · exact compactCertificate406_coefficient3
  · exact compactCertificate406_coefficient4

theorem compactCertificate406_lower : (1 : ℚ) ≤ compactCertificate406.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate406, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate406_proves {t : ℝ} (ht : t ∈ compactCertificate406.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate406.proves compactCertificate406_states compactCertificate406_chunks
    compactCertificate406_coefficients compactCertificate406_lower ht

end Erdos232
