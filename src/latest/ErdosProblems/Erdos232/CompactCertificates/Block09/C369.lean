/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate369 : CompactCertificate where
  left := 240
  right := 241
  center := 481 / 2
  grid := fun i =>
    match i.val with
    | 0 => 77
    | 1 => 56
    | 2 => 91
    | 3 => 16
    | 4 => 44
    | 5 => 120
    | 6 => 88
    | 7 => 152
    | 8 => 112
    | 9 => 171
    | 10 => 99
    | 11 => 175
    | 12 => 164
    | 13 => 117
    | 14 => 133
    | 15 => 111
    | 16 => 98
    | 17 => 142
    | 18 => 78
    | 19 => 66
    | 20 => 42
    | 21 => 22
    | 22 => 61
    | 23 => 83
    | 24 => 35
    | 25 => 142
    | _ => 95
  point := fun i =>
    match i.val with
    | 0 => 481 / 2
    | 1 => 708604845940381 / 4000000000000
    | 2 => 229148247971773 / 800000000000
    | 3 => 206769126759767 / 4000000000000
    | 4 => 555410958960299 / 4000000000000
    | 5 => 1508048796395583 / 4000000000000
    | 6 => 1110821917921079 / 4000000000000
    | 7 => 1903412289710867 / 4000000000000
    | 8 => 1402044877661753 / 4000000000000
    | 9 => 2151097394354519 / 4000000000000
    | 10 => 1241936659683551 / 4000000000000
    | 11 => 2203838396514859 / 4000000000000
    | 12 => 2059111704422071 / 4000000000000
    | 13 => 1469479272848743 / 4000000000000
    | 14 => 1666232876880897 / 4000000000000
    | 15 => 1389131259233393 / 4000000000000
    | 16 => 1227339595657253 / 4000000000000
    | 17 => 355730852680047 / 800000000000
    | 18 => 983970259602109 / 4000000000000
    | 19 => 834122486236949 / 4000000000000
    | 20 => 521955122338247 / 4000000000000
    | 21 => 280709200737849 / 4000000000000
    | 22 => 762180085720547 / 4000000000000
    | 23 => 1040691746271619 / 4000000000000
    | 24 => 440044877661753 / 4000000000000
    | 25 => 1788757997133913 / 4000000000000
    | _ => 1194807443770967 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (29799982188 / 1000000000000) (29799990141 / 1000000000000), orderedInterval (-42002753688 / 1000000000000) (-42002745735 / 1000000000000))
    | 1 => (orderedInterval (54340850580 / 1000000000000) (54340861457 / 1000000000000), orderedInterval (-25465706159 / 1000000000000) (-25465695282 / 1000000000000))
    | 2 => (orderedInterval (-45843207675 / 1000000000000) (-45843207671 / 1000000000000), orderedInterval (-10918052603 / 1000000000000) (-10918052599 / 1000000000000))
    | 3 => (orderedInterval (89078223476 / 1000000000000) (89078264536 / 1000000000000), orderedInterval (-67046657260 / 1000000000000) (-67046616199 / 1000000000000))
    | 4 => (orderedInterval (66806826132 / 1000000000000) (66806826136 / 1000000000000), orderedInterval (10790098464 / 1000000000000) (10790098468 / 1000000000000))
    | 5 => (orderedInterval (29653363148 / 1000000000000) (29653363149 / 1000000000000), orderedInterval (28408343887 / 1000000000000) (28408343888 / 1000000000000))
    | 6 => (orderedInterval (42913420859 / 1000000000000) (42913443121 / 1000000000000), orderedInterval (-21310807418 / 1000000000000) (-21310785156 / 1000000000000))
    | 7 => (orderedInterval (-28281139049 / 1000000000000) (-28281106391 / 1000000000000), orderedInterval (23225116733 / 1000000000000) (23225149391 / 1000000000000))
    | 8 => (orderedInterval (-22714238856 / 1000000000000) (-22714236415 / 1000000000000), orderedInterval (36092419139 / 1000000000000) (36092421579 / 1000000000000))
    | 9 => (orderedInterval (-33549726703 / 1000000000000) (-33549726671 / 1000000000000), orderedInterval (-7599011623 / 1000000000000) (-7599011592 / 1000000000000))
    | 10 => (orderedInterval (-11268065180 / 1000000000000) (-11268065179 / 1000000000000), orderedInterval (-43838926833 / 1000000000000) (-43838926832 / 1000000000000))
    | 11 => (orderedInterval (-31371366289 / 1000000000000) (-31371322456 / 1000000000000), orderedInterval (13117102327 / 1000000000000) (13117146159 / 1000000000000))
    | 12 => (orderedInterval (11790111938 / 1000000000000) (11790111939 / 1000000000000), orderedInterval (33119830929 / 1000000000000) (33119830930 / 1000000000000))
    | 13 => (orderedInterval (-23109656579 / 1000000000000) (-23109656578 / 1000000000000), orderedInterval (-34593060910 / 1000000000000) (-34593060909 / 1000000000000))
    | 14 => (orderedInterval (18346740199 / 1000000000000) (18346740900 / 1000000000000), orderedInterval (-34542783322 / 1000000000000) (-34542782621 / 1000000000000))
    | 15 => (orderedInterval (25874752784 / 1000000000000) (25874759080 / 1000000000000), orderedInterval (-34149461591 / 1000000000000) (-34149455295 / 1000000000000))
    | 16 => (orderedInterval (-11542211503 / 1000000000000) (-11542211436 / 1000000000000), orderedInterval (44082121926 / 1000000000000) (44082121992 / 1000000000000))
    | 17 => (orderedInterval (-23123320071 / 1000000000000) (-23123315969 / 1000000000000), orderedInterval (29975974116 / 1000000000000) (29975978218 / 1000000000000))
    | 18 => (orderedInterval (50202347742 / 1000000000000) (50202348542 / 1000000000000), orderedInterval (-8328986644 / 1000000000000) (-8328985845 / 1000000000000))
    | 19 => (orderedInterval (50901782933 / 1000000000000) (50901791788 / 1000000000000), orderedInterval (-21613580429 / 1000000000000) (-21613571574 / 1000000000000))
    | 20 => (orderedInterval (-43575097525 / 1000000000000) (-43575074033 / 1000000000000), orderedInterval (54755887399 / 1000000000000) (54755910890 / 1000000000000))
    | 21 => (orderedInterval (91662791566 / 1000000000000) (91662792641 / 1000000000000), orderedInterval (-26524410756 / 1000000000000) (-26524409681 / 1000000000000))
    | 22 => (orderedInterval (17489077500 / 1000000000000) (17489077802 / 1000000000000), orderedInterval (-55138432720 / 1000000000000) (-55138432419 / 1000000000000))
    | 23 => (orderedInterval (-10101852446 / 1000000000000) (-10101852445 / 1000000000000), orderedInterval (-48404410704 / 1000000000000) (-48404410703 / 1000000000000))
    | 24 => (orderedInterval (-56632494157 / 1000000000000) (-56632494156 / 1000000000000), orderedInterval (-50532535049 / 1000000000000) (-50532535048 / 1000000000000))
    | 25 => (orderedInterval (36071387635 / 1000000000000) (36071398329 / 1000000000000), orderedInterval (-11106304569 / 1000000000000) (-11106293875 / 1000000000000))
    | _ => (orderedInterval (-39708959656 / 1000000000000) (-39708959655 / 1000000000000), orderedInterval (-23481043798 / 1000000000000) (-23481043797 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (9627889341 / 1000000000000) (9627892612 / 1000000000000)
      | 1 => orderedInterval (-635249102 / 1000000000000) (-635248627 / 1000000000000)
      | 2 => orderedInterval (323344129 / 1000000000000) (323345209 / 1000000000000)
      | 3 => orderedInterval (666885839 / 1000000000000) (666892172 / 1000000000000)
      | 4 => orderedInterval (-2491008354 / 1000000000000) (-2491008322 / 1000000000000)
      | 5 => orderedInterval (367267169 / 1000000000000) (367267375 / 1000000000000)
      | 6 => orderedInterval (-12326614417 / 1000000000000) (-12326612962 / 1000000000000)
      | 7 => orderedInterval (-1315141944 / 1000000000000) (-1315141888 / 1000000000000)
      | _ => orderedInterval (4172778984 / 1000000000000) (4172779922 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-17586262509 / 1000000000000) (-17586259263 / 1000000000000)
      | 1 => orderedInterval (-2782063507 / 1000000000000) (-2782063378 / 1000000000000)
      | 2 => orderedInterval (-146094118 / 1000000000000) (-146092014 / 1000000000000)
      | 3 => orderedInterval (3097738541 / 1000000000000) (3097753026 / 1000000000000)
      | 4 => orderedInterval (-5973902786 / 1000000000000) (-5973902732 / 1000000000000)
      | 5 => orderedInterval (-2368870237 / 1000000000000) (-2368869899 / 1000000000000)
      | 6 => orderedInterval (3390054601 / 1000000000000) (3390055638 / 1000000000000)
      | 7 => orderedInterval (5147111599 / 1000000000000) (5147111637 / 1000000000000)
      | _ => orderedInterval (7013555120 / 1000000000000) (7013556833 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-8197386080 / 1000000000000) (-8197382837 / 1000000000000)
      | 1 => orderedInterval (4423508741 / 1000000000000) (4423508808 / 1000000000000)
      | 2 => orderedInterval (-2248294667 / 1000000000000) (-2248290548 / 1000000000000)
      | 3 => orderedInterval (-5023422576 / 1000000000000) (-5023389362 / 1000000000000)
      | 4 => orderedInterval (6377610983 / 1000000000000) (6377611071 / 1000000000000)
      | 5 => orderedInterval (335582242 / 1000000000000) (335582811 / 1000000000000)
      | 6 => orderedInterval (10967323978 / 1000000000000) (10967324771 / 1000000000000)
      | 7 => orderedInterval (-534259007 / 1000000000000) (-534258975 / 1000000000000)
      | _ => orderedInterval (-1298639947 / 1000000000000) (-1298636792 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (17859409584 / 1000000000000) (17859412816 / 1000000000000)
      | 1 => orderedInterval (7678402841 / 1000000000000) (7678402915 / 1000000000000)
      | 2 => orderedInterval (2857847683 / 1000000000000) (2857855761 / 1000000000000)
      | 3 => orderedInterval (-30505639855 / 1000000000000) (-30505563814 / 1000000000000)
      | 4 => orderedInterval (16587881534 / 1000000000000) (16587881684 / 1000000000000)
      | 5 => orderedInterval (1573720428 / 1000000000000) (1573721398 / 1000000000000)
      | 6 => orderedInterval (-2552811003 / 1000000000000) (-2552810362 / 1000000000000)
      | 7 => orderedInterval (-5328490306 / 1000000000000) (-5328490275 / 1000000000000)
      | _ => orderedInterval (-14218155228 / 1000000000000) (-14218149405 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (6399304377 / 1000000000000) (6399307616 / 1000000000000)
      | 1 => orderedInterval (-12525199490 / 1000000000000) (-12525199383 / 1000000000000)
      | 2 => orderedInterval (10868399538 / 1000000000000) (10868415449 / 1000000000000)
      | 3 => orderedInterval (24135497740 / 1000000000000) (24135672191 / 1000000000000)
      | 4 => orderedInterval (-17339016662 / 1000000000000) (-17339016402 / 1000000000000)
      | 5 => orderedInterval (-3882622107 / 1000000000000) (-3882620424 / 1000000000000)
      | 6 => orderedInterval (-10515712501 / 1000000000000) (-10515711955 / 1000000000000)
      | 7 => orderedInterval (936014114 / 1000000000000) (936014145 / 1000000000000)
      | _ => orderedInterval (-17267805683 / 1000000000000) (-17267794887 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-1609848355 / 1000000000000) (-1609834509 / 1000000000000)
    | 1 => orderedInterval (-10208733296 / 1000000000000) (-10208710152 / 1000000000000)
    | 2 => orderedInterval (4802023667 / 1000000000000) (4802068947 / 1000000000000)
    | 3 => orderedInterval (-6047834322 / 1000000000000) (-6047739282 / 1000000000000)
    | _ => orderedInterval (-19191140674 / 1000000000000) (-19190933650 / 1000000000000)

theorem compactCertificate369_stateChecks0 :
    compactCertificate369.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 77 12 (481 / 2)) (orderedInterval (29799982188 / 1000000000000) (29799990141 / 1000000000000), orderedInterval (-42002753688 / 1000000000000) (-42002745735 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 56 12 (708604845940381 / 4000000000000)) (orderedInterval (54340850580 / 1000000000000) (54340861457 / 1000000000000), orderedInterval (-25465706159 / 1000000000000) (-25465695282 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 91 12 (229148247971773 / 800000000000)) (orderedInterval (-45843207675 / 1000000000000) (-45843207671 / 1000000000000), orderedInterval (-10918052603 / 1000000000000) (-10918052599 / 1000000000000))) = true
  rfl'

theorem compactCertificate369_stateChecks1 :
    compactCertificate369.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 16 12 (206769126759767 / 4000000000000)) (orderedInterval (89078223476 / 1000000000000) (89078264536 / 1000000000000), orderedInterval (-67046657260 / 1000000000000) (-67046616199 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 44 12 (555410958960299 / 4000000000000)) (orderedInterval (66806826132 / 1000000000000) (66806826136 / 1000000000000), orderedInterval (10790098464 / 1000000000000) (10790098468 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 120 12 (1508048796395583 / 4000000000000)) (orderedInterval (29653363148 / 1000000000000) (29653363149 / 1000000000000), orderedInterval (28408343887 / 1000000000000) (28408343888 / 1000000000000))) = true
  rfl'

theorem compactCertificate369_stateChecks2 :
    compactCertificate369.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 88 12 (1110821917921079 / 4000000000000)) (orderedInterval (42913420859 / 1000000000000) (42913443121 / 1000000000000), orderedInterval (-21310807418 / 1000000000000) (-21310785156 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 152 12 (1903412289710867 / 4000000000000)) (orderedInterval (-28281139049 / 1000000000000) (-28281106391 / 1000000000000), orderedInterval (23225116733 / 1000000000000) (23225149391 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 112 12 (1402044877661753 / 4000000000000)) (orderedInterval (-22714238856 / 1000000000000) (-22714236415 / 1000000000000), orderedInterval (36092419139 / 1000000000000) (36092421579 / 1000000000000))) = true
  rfl'

theorem compactCertificate369_stateChecks3 :
    compactCertificate369.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 171 12 (2151097394354519 / 4000000000000)) (orderedInterval (-33549726703 / 1000000000000) (-33549726671 / 1000000000000), orderedInterval (-7599011623 / 1000000000000) (-7599011592 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 99 12 (1241936659683551 / 4000000000000)) (orderedInterval (-11268065180 / 1000000000000) (-11268065179 / 1000000000000), orderedInterval (-43838926833 / 1000000000000) (-43838926832 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 175 12 (2203838396514859 / 4000000000000)) (orderedInterval (-31371366289 / 1000000000000) (-31371322456 / 1000000000000), orderedInterval (13117102327 / 1000000000000) (13117146159 / 1000000000000))) = true
  rfl'

theorem compactCertificate369_stateChecks4 :
    compactCertificate369.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 164 12 (2059111704422071 / 4000000000000)) (orderedInterval (11790111938 / 1000000000000) (11790111939 / 1000000000000), orderedInterval (33119830929 / 1000000000000) (33119830930 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 117 12 (1469479272848743 / 4000000000000)) (orderedInterval (-23109656579 / 1000000000000) (-23109656578 / 1000000000000), orderedInterval (-34593060910 / 1000000000000) (-34593060909 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 133 12 (1666232876880897 / 4000000000000)) (orderedInterval (18346740199 / 1000000000000) (18346740900 / 1000000000000), orderedInterval (-34542783322 / 1000000000000) (-34542782621 / 1000000000000))) = true
  rfl'

theorem compactCertificate369_stateChecks5 :
    compactCertificate369.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 111 12 (1389131259233393 / 4000000000000)) (orderedInterval (25874752784 / 1000000000000) (25874759080 / 1000000000000), orderedInterval (-34149461591 / 1000000000000) (-34149455295 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 98 12 (1227339595657253 / 4000000000000)) (orderedInterval (-11542211503 / 1000000000000) (-11542211436 / 1000000000000), orderedInterval (44082121926 / 1000000000000) (44082121992 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 142 12 (355730852680047 / 800000000000)) (orderedInterval (-23123320071 / 1000000000000) (-23123315969 / 1000000000000), orderedInterval (29975974116 / 1000000000000) (29975978218 / 1000000000000))) = true
  rfl'

theorem compactCertificate369_stateChecks6 :
    compactCertificate369.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 78 12 (983970259602109 / 4000000000000)) (orderedInterval (50202347742 / 1000000000000) (50202348542 / 1000000000000), orderedInterval (-8328986644 / 1000000000000) (-8328985845 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (834122486236949 / 4000000000000)) (orderedInterval (50901782933 / 1000000000000) (50901791788 / 1000000000000), orderedInterval (-21613580429 / 1000000000000) (-21613571574 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 42 12 (521955122338247 / 4000000000000)) (orderedInterval (-43575097525 / 1000000000000) (-43575074033 / 1000000000000), orderedInterval (54755887399 / 1000000000000) (54755910890 / 1000000000000))) = true
  rfl'

theorem compactCertificate369_stateChecks7 :
    compactCertificate369.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 22 12 (280709200737849 / 4000000000000)) (orderedInterval (91662791566 / 1000000000000) (91662792641 / 1000000000000), orderedInterval (-26524410756 / 1000000000000) (-26524409681 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 61 12 (762180085720547 / 4000000000000)) (orderedInterval (17489077500 / 1000000000000) (17489077802 / 1000000000000), orderedInterval (-55138432720 / 1000000000000) (-55138432419 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 83 12 (1040691746271619 / 4000000000000)) (orderedInterval (-10101852446 / 1000000000000) (-10101852445 / 1000000000000), orderedInterval (-48404410704 / 1000000000000) (-48404410703 / 1000000000000))) = true
  rfl'

theorem compactCertificate369_stateChecks8 :
    compactCertificate369.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 35 12 (440044877661753 / 4000000000000)) (orderedInterval (-56632494157 / 1000000000000) (-56632494156 / 1000000000000), orderedInterval (-50532535049 / 1000000000000) (-50532535048 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 142 12 (1788757997133913 / 4000000000000)) (orderedInterval (36071387635 / 1000000000000) (36071398329 / 1000000000000), orderedInterval (-11106304569 / 1000000000000) (-11106293875 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 95 12 (1194807443770967 / 4000000000000)) (orderedInterval (-39708959656 / 1000000000000) (-39708959655 / 1000000000000), orderedInterval (-23481043798 / 1000000000000) (-23481043797 / 1000000000000))) = true
  rfl'

theorem compactCertificate369_states : ∀ j,
    BesselStateValid (compactCertificate369.point j) (compactCertificate369.state j) :=
  compactCertificate369.statesValid_of_checks3 compactCertificate369_stateChecks0
    compactCertificate369_stateChecks1 compactCertificate369_stateChecks2
    compactCertificate369_stateChecks3 compactCertificate369_stateChecks4
    compactCertificate369_stateChecks5 compactCertificate369_stateChecks6
    compactCertificate369_stateChecks7 compactCertificate369_stateChecks8

theorem compactCertificate369_chunkChecks0_0 :
    compactCertificate369.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (481 / 2) 0 (IntervalRat.scale (481 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (29799982188 / 1000000000000) (29799990141 / 1000000000000), orderedInterval (-42002753688 / 1000000000000) (-42002745735 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (708604845940381 / 4000000000000) 0 (IntervalRat.scale (481 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (54340850580 / 1000000000000) (54340861457 / 1000000000000), orderedInterval (-25465706159 / 1000000000000) (-25465695282 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (229148247971773 / 800000000000) 0 (IntervalRat.scale (481 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-45843207675 / 1000000000000) (-45843207671 / 1000000000000), orderedInterval (-10918052603 / 1000000000000) (-10918052599 / 1000000000000)))) (orderedInterval (9627889341 / 1000000000000) (9627892612 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (206769126759767 / 4000000000000) 0 (IntervalRat.scale (481 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (89078223476 / 1000000000000) (89078264536 / 1000000000000), orderedInterval (-67046657260 / 1000000000000) (-67046616199 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (555410958960299 / 4000000000000) 0 (IntervalRat.scale (481 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (66806826132 / 1000000000000) (66806826136 / 1000000000000), orderedInterval (10790098464 / 1000000000000) (10790098468 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1508048796395583 / 4000000000000) 0 (IntervalRat.scale (481 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29653363148 / 1000000000000) (29653363149 / 1000000000000), orderedInterval (28408343887 / 1000000000000) (28408343888 / 1000000000000)))) (orderedInterval (-635249102 / 1000000000000) (-635248627 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1110821917921079 / 4000000000000) 0 (IntervalRat.scale (481 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (42913420859 / 1000000000000) (42913443121 / 1000000000000), orderedInterval (-21310807418 / 1000000000000) (-21310785156 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1903412289710867 / 4000000000000) 0 (IntervalRat.scale (481 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-28281139049 / 1000000000000) (-28281106391 / 1000000000000), orderedInterval (23225116733 / 1000000000000) (23225149391 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1402044877661753 / 4000000000000) 0 (IntervalRat.scale (481 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-22714238856 / 1000000000000) (-22714236415 / 1000000000000), orderedInterval (36092419139 / 1000000000000) (36092421579 / 1000000000000)))) (orderedInterval (323344129 / 1000000000000) (323345209 / 1000000000000))) = true
  rfl'

theorem compactCertificate369_chunkChecks0_1 :
    compactCertificate369.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2151097394354519 / 4000000000000) 0 (IntervalRat.scale (481 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-33549726703 / 1000000000000) (-33549726671 / 1000000000000), orderedInterval (-7599011623 / 1000000000000) (-7599011592 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1241936659683551 / 4000000000000) 0 (IntervalRat.scale (481 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-11268065180 / 1000000000000) (-11268065179 / 1000000000000), orderedInterval (-43838926833 / 1000000000000) (-43838926832 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2203838396514859 / 4000000000000) 0 (IntervalRat.scale (481 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-31371366289 / 1000000000000) (-31371322456 / 1000000000000), orderedInterval (13117102327 / 1000000000000) (13117146159 / 1000000000000)))) (orderedInterval (666885839 / 1000000000000) (666892172 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2059111704422071 / 4000000000000) 0 (IntervalRat.scale (481 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (11790111938 / 1000000000000) (11790111939 / 1000000000000), orderedInterval (33119830929 / 1000000000000) (33119830930 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1469479272848743 / 4000000000000) 0 (IntervalRat.scale (481 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-23109656579 / 1000000000000) (-23109656578 / 1000000000000), orderedInterval (-34593060910 / 1000000000000) (-34593060909 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1666232876880897 / 4000000000000) 0 (IntervalRat.scale (481 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (18346740199 / 1000000000000) (18346740900 / 1000000000000), orderedInterval (-34542783322 / 1000000000000) (-34542782621 / 1000000000000)))) (orderedInterval (-2491008354 / 1000000000000) (-2491008322 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1389131259233393 / 4000000000000) 0 (IntervalRat.scale (481 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (25874752784 / 1000000000000) (25874759080 / 1000000000000), orderedInterval (-34149461591 / 1000000000000) (-34149455295 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1227339595657253 / 4000000000000) 0 (IntervalRat.scale (481 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-11542211503 / 1000000000000) (-11542211436 / 1000000000000), orderedInterval (44082121926 / 1000000000000) (44082121992 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (355730852680047 / 800000000000) 0 (IntervalRat.scale (481 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-23123320071 / 1000000000000) (-23123315969 / 1000000000000), orderedInterval (29975974116 / 1000000000000) (29975978218 / 1000000000000)))) (orderedInterval (367267169 / 1000000000000) (367267375 / 1000000000000))) = true
  rfl'

theorem compactCertificate369_chunkChecks0_2 :
    compactCertificate369.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (983970259602109 / 4000000000000) 0 (IntervalRat.scale (481 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (50202347742 / 1000000000000) (50202348542 / 1000000000000), orderedInterval (-8328986644 / 1000000000000) (-8328985845 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (834122486236949 / 4000000000000) 0 (IntervalRat.scale (481 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (50901782933 / 1000000000000) (50901791788 / 1000000000000), orderedInterval (-21613580429 / 1000000000000) (-21613571574 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (521955122338247 / 4000000000000) 0 (IntervalRat.scale (481 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-43575097525 / 1000000000000) (-43575074033 / 1000000000000), orderedInterval (54755887399 / 1000000000000) (54755910890 / 1000000000000)))) (orderedInterval (-12326614417 / 1000000000000) (-12326612962 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (280709200737849 / 4000000000000) 0 (IntervalRat.scale (481 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (91662791566 / 1000000000000) (91662792641 / 1000000000000), orderedInterval (-26524410756 / 1000000000000) (-26524409681 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (762180085720547 / 4000000000000) 0 (IntervalRat.scale (481 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (17489077500 / 1000000000000) (17489077802 / 1000000000000), orderedInterval (-55138432720 / 1000000000000) (-55138432419 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1040691746271619 / 4000000000000) 0 (IntervalRat.scale (481 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-10101852446 / 1000000000000) (-10101852445 / 1000000000000), orderedInterval (-48404410704 / 1000000000000) (-48404410703 / 1000000000000)))) (orderedInterval (-1315141944 / 1000000000000) (-1315141888 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (440044877661753 / 4000000000000) 0 (IntervalRat.scale (481 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-56632494157 / 1000000000000) (-56632494156 / 1000000000000), orderedInterval (-50532535049 / 1000000000000) (-50532535048 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1788757997133913 / 4000000000000) 0 (IntervalRat.scale (481 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (36071387635 / 1000000000000) (36071398329 / 1000000000000), orderedInterval (-11106304569 / 1000000000000) (-11106293875 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1194807443770967 / 4000000000000) 0 (IntervalRat.scale (481 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-39708959656 / 1000000000000) (-39708959655 / 1000000000000), orderedInterval (-23481043798 / 1000000000000) (-23481043797 / 1000000000000)))) (orderedInterval (4172778984 / 1000000000000) (4172779922 / 1000000000000))) = true
  rfl'

theorem compactCertificate369_chunkChecks0 :
    compactCertificate369.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate369.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate369_chunkChecks0_0
    compactCertificate369_chunkChecks0_1 compactCertificate369_chunkChecks0_2

theorem compactCertificate369_chunkChecks1_0 :
    compactCertificate369.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (481 / 2) 1 (IntervalRat.scale (481 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (29799982188 / 1000000000000) (29799990141 / 1000000000000), orderedInterval (-42002753688 / 1000000000000) (-42002745735 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (708604845940381 / 4000000000000) 1 (IntervalRat.scale (481 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (54340850580 / 1000000000000) (54340861457 / 1000000000000), orderedInterval (-25465706159 / 1000000000000) (-25465695282 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (229148247971773 / 800000000000) 1 (IntervalRat.scale (481 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-45843207675 / 1000000000000) (-45843207671 / 1000000000000), orderedInterval (-10918052603 / 1000000000000) (-10918052599 / 1000000000000)))) (orderedInterval (-17586262509 / 1000000000000) (-17586259263 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (206769126759767 / 4000000000000) 1 (IntervalRat.scale (481 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (89078223476 / 1000000000000) (89078264536 / 1000000000000), orderedInterval (-67046657260 / 1000000000000) (-67046616199 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (555410958960299 / 4000000000000) 1 (IntervalRat.scale (481 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (66806826132 / 1000000000000) (66806826136 / 1000000000000), orderedInterval (10790098464 / 1000000000000) (10790098468 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1508048796395583 / 4000000000000) 1 (IntervalRat.scale (481 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29653363148 / 1000000000000) (29653363149 / 1000000000000), orderedInterval (28408343887 / 1000000000000) (28408343888 / 1000000000000)))) (orderedInterval (-2782063507 / 1000000000000) (-2782063378 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1110821917921079 / 4000000000000) 1 (IntervalRat.scale (481 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (42913420859 / 1000000000000) (42913443121 / 1000000000000), orderedInterval (-21310807418 / 1000000000000) (-21310785156 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1903412289710867 / 4000000000000) 1 (IntervalRat.scale (481 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-28281139049 / 1000000000000) (-28281106391 / 1000000000000), orderedInterval (23225116733 / 1000000000000) (23225149391 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1402044877661753 / 4000000000000) 1 (IntervalRat.scale (481 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-22714238856 / 1000000000000) (-22714236415 / 1000000000000), orderedInterval (36092419139 / 1000000000000) (36092421579 / 1000000000000)))) (orderedInterval (-146094118 / 1000000000000) (-146092014 / 1000000000000))) = true
  rfl'

theorem compactCertificate369_chunkChecks1_1 :
    compactCertificate369.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2151097394354519 / 4000000000000) 1 (IntervalRat.scale (481 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-33549726703 / 1000000000000) (-33549726671 / 1000000000000), orderedInterval (-7599011623 / 1000000000000) (-7599011592 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1241936659683551 / 4000000000000) 1 (IntervalRat.scale (481 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-11268065180 / 1000000000000) (-11268065179 / 1000000000000), orderedInterval (-43838926833 / 1000000000000) (-43838926832 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2203838396514859 / 4000000000000) 1 (IntervalRat.scale (481 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-31371366289 / 1000000000000) (-31371322456 / 1000000000000), orderedInterval (13117102327 / 1000000000000) (13117146159 / 1000000000000)))) (orderedInterval (3097738541 / 1000000000000) (3097753026 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2059111704422071 / 4000000000000) 1 (IntervalRat.scale (481 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (11790111938 / 1000000000000) (11790111939 / 1000000000000), orderedInterval (33119830929 / 1000000000000) (33119830930 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1469479272848743 / 4000000000000) 1 (IntervalRat.scale (481 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-23109656579 / 1000000000000) (-23109656578 / 1000000000000), orderedInterval (-34593060910 / 1000000000000) (-34593060909 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1666232876880897 / 4000000000000) 1 (IntervalRat.scale (481 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (18346740199 / 1000000000000) (18346740900 / 1000000000000), orderedInterval (-34542783322 / 1000000000000) (-34542782621 / 1000000000000)))) (orderedInterval (-5973902786 / 1000000000000) (-5973902732 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1389131259233393 / 4000000000000) 1 (IntervalRat.scale (481 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (25874752784 / 1000000000000) (25874759080 / 1000000000000), orderedInterval (-34149461591 / 1000000000000) (-34149455295 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1227339595657253 / 4000000000000) 1 (IntervalRat.scale (481 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-11542211503 / 1000000000000) (-11542211436 / 1000000000000), orderedInterval (44082121926 / 1000000000000) (44082121992 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (355730852680047 / 800000000000) 1 (IntervalRat.scale (481 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-23123320071 / 1000000000000) (-23123315969 / 1000000000000), orderedInterval (29975974116 / 1000000000000) (29975978218 / 1000000000000)))) (orderedInterval (-2368870237 / 1000000000000) (-2368869899 / 1000000000000))) = true
  rfl'

theorem compactCertificate369_chunkChecks1_2 :
    compactCertificate369.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (983970259602109 / 4000000000000) 1 (IntervalRat.scale (481 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (50202347742 / 1000000000000) (50202348542 / 1000000000000), orderedInterval (-8328986644 / 1000000000000) (-8328985845 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (834122486236949 / 4000000000000) 1 (IntervalRat.scale (481 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (50901782933 / 1000000000000) (50901791788 / 1000000000000), orderedInterval (-21613580429 / 1000000000000) (-21613571574 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (521955122338247 / 4000000000000) 1 (IntervalRat.scale (481 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-43575097525 / 1000000000000) (-43575074033 / 1000000000000), orderedInterval (54755887399 / 1000000000000) (54755910890 / 1000000000000)))) (orderedInterval (3390054601 / 1000000000000) (3390055638 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (280709200737849 / 4000000000000) 1 (IntervalRat.scale (481 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (91662791566 / 1000000000000) (91662792641 / 1000000000000), orderedInterval (-26524410756 / 1000000000000) (-26524409681 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (762180085720547 / 4000000000000) 1 (IntervalRat.scale (481 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (17489077500 / 1000000000000) (17489077802 / 1000000000000), orderedInterval (-55138432720 / 1000000000000) (-55138432419 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1040691746271619 / 4000000000000) 1 (IntervalRat.scale (481 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-10101852446 / 1000000000000) (-10101852445 / 1000000000000), orderedInterval (-48404410704 / 1000000000000) (-48404410703 / 1000000000000)))) (orderedInterval (5147111599 / 1000000000000) (5147111637 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (440044877661753 / 4000000000000) 1 (IntervalRat.scale (481 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-56632494157 / 1000000000000) (-56632494156 / 1000000000000), orderedInterval (-50532535049 / 1000000000000) (-50532535048 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1788757997133913 / 4000000000000) 1 (IntervalRat.scale (481 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (36071387635 / 1000000000000) (36071398329 / 1000000000000), orderedInterval (-11106304569 / 1000000000000) (-11106293875 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1194807443770967 / 4000000000000) 1 (IntervalRat.scale (481 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-39708959656 / 1000000000000) (-39708959655 / 1000000000000), orderedInterval (-23481043798 / 1000000000000) (-23481043797 / 1000000000000)))) (orderedInterval (7013555120 / 1000000000000) (7013556833 / 1000000000000))) = true
  rfl'

theorem compactCertificate369_chunkChecks1 :
    compactCertificate369.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate369.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate369_chunkChecks1_0
    compactCertificate369_chunkChecks1_1 compactCertificate369_chunkChecks1_2

theorem compactCertificate369_chunkChecks2_0 :
    compactCertificate369.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (481 / 2) 2 (IntervalRat.scale (481 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (29799982188 / 1000000000000) (29799990141 / 1000000000000), orderedInterval (-42002753688 / 1000000000000) (-42002745735 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (708604845940381 / 4000000000000) 2 (IntervalRat.scale (481 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (54340850580 / 1000000000000) (54340861457 / 1000000000000), orderedInterval (-25465706159 / 1000000000000) (-25465695282 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (229148247971773 / 800000000000) 2 (IntervalRat.scale (481 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-45843207675 / 1000000000000) (-45843207671 / 1000000000000), orderedInterval (-10918052603 / 1000000000000) (-10918052599 / 1000000000000)))) (orderedInterval (-8197386080 / 1000000000000) (-8197382837 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (206769126759767 / 4000000000000) 2 (IntervalRat.scale (481 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (89078223476 / 1000000000000) (89078264536 / 1000000000000), orderedInterval (-67046657260 / 1000000000000) (-67046616199 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (555410958960299 / 4000000000000) 2 (IntervalRat.scale (481 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (66806826132 / 1000000000000) (66806826136 / 1000000000000), orderedInterval (10790098464 / 1000000000000) (10790098468 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1508048796395583 / 4000000000000) 2 (IntervalRat.scale (481 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29653363148 / 1000000000000) (29653363149 / 1000000000000), orderedInterval (28408343887 / 1000000000000) (28408343888 / 1000000000000)))) (orderedInterval (4423508741 / 1000000000000) (4423508808 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1110821917921079 / 4000000000000) 2 (IntervalRat.scale (481 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (42913420859 / 1000000000000) (42913443121 / 1000000000000), orderedInterval (-21310807418 / 1000000000000) (-21310785156 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1903412289710867 / 4000000000000) 2 (IntervalRat.scale (481 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-28281139049 / 1000000000000) (-28281106391 / 1000000000000), orderedInterval (23225116733 / 1000000000000) (23225149391 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1402044877661753 / 4000000000000) 2 (IntervalRat.scale (481 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-22714238856 / 1000000000000) (-22714236415 / 1000000000000), orderedInterval (36092419139 / 1000000000000) (36092421579 / 1000000000000)))) (orderedInterval (-2248294667 / 1000000000000) (-2248290548 / 1000000000000))) = true
  rfl'

theorem compactCertificate369_chunkChecks2_1 :
    compactCertificate369.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2151097394354519 / 4000000000000) 2 (IntervalRat.scale (481 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-33549726703 / 1000000000000) (-33549726671 / 1000000000000), orderedInterval (-7599011623 / 1000000000000) (-7599011592 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1241936659683551 / 4000000000000) 2 (IntervalRat.scale (481 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-11268065180 / 1000000000000) (-11268065179 / 1000000000000), orderedInterval (-43838926833 / 1000000000000) (-43838926832 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2203838396514859 / 4000000000000) 2 (IntervalRat.scale (481 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-31371366289 / 1000000000000) (-31371322456 / 1000000000000), orderedInterval (13117102327 / 1000000000000) (13117146159 / 1000000000000)))) (orderedInterval (-5023422576 / 1000000000000) (-5023389362 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2059111704422071 / 4000000000000) 2 (IntervalRat.scale (481 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (11790111938 / 1000000000000) (11790111939 / 1000000000000), orderedInterval (33119830929 / 1000000000000) (33119830930 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1469479272848743 / 4000000000000) 2 (IntervalRat.scale (481 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-23109656579 / 1000000000000) (-23109656578 / 1000000000000), orderedInterval (-34593060910 / 1000000000000) (-34593060909 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1666232876880897 / 4000000000000) 2 (IntervalRat.scale (481 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (18346740199 / 1000000000000) (18346740900 / 1000000000000), orderedInterval (-34542783322 / 1000000000000) (-34542782621 / 1000000000000)))) (orderedInterval (6377610983 / 1000000000000) (6377611071 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1389131259233393 / 4000000000000) 2 (IntervalRat.scale (481 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (25874752784 / 1000000000000) (25874759080 / 1000000000000), orderedInterval (-34149461591 / 1000000000000) (-34149455295 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1227339595657253 / 4000000000000) 2 (IntervalRat.scale (481 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-11542211503 / 1000000000000) (-11542211436 / 1000000000000), orderedInterval (44082121926 / 1000000000000) (44082121992 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (355730852680047 / 800000000000) 2 (IntervalRat.scale (481 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-23123320071 / 1000000000000) (-23123315969 / 1000000000000), orderedInterval (29975974116 / 1000000000000) (29975978218 / 1000000000000)))) (orderedInterval (335582242 / 1000000000000) (335582811 / 1000000000000))) = true
  rfl'

theorem compactCertificate369_chunkChecks2_2 :
    compactCertificate369.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (983970259602109 / 4000000000000) 2 (IntervalRat.scale (481 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (50202347742 / 1000000000000) (50202348542 / 1000000000000), orderedInterval (-8328986644 / 1000000000000) (-8328985845 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (834122486236949 / 4000000000000) 2 (IntervalRat.scale (481 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (50901782933 / 1000000000000) (50901791788 / 1000000000000), orderedInterval (-21613580429 / 1000000000000) (-21613571574 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (521955122338247 / 4000000000000) 2 (IntervalRat.scale (481 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-43575097525 / 1000000000000) (-43575074033 / 1000000000000), orderedInterval (54755887399 / 1000000000000) (54755910890 / 1000000000000)))) (orderedInterval (10967323978 / 1000000000000) (10967324771 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (280709200737849 / 4000000000000) 2 (IntervalRat.scale (481 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (91662791566 / 1000000000000) (91662792641 / 1000000000000), orderedInterval (-26524410756 / 1000000000000) (-26524409681 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (762180085720547 / 4000000000000) 2 (IntervalRat.scale (481 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (17489077500 / 1000000000000) (17489077802 / 1000000000000), orderedInterval (-55138432720 / 1000000000000) (-55138432419 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1040691746271619 / 4000000000000) 2 (IntervalRat.scale (481 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-10101852446 / 1000000000000) (-10101852445 / 1000000000000), orderedInterval (-48404410704 / 1000000000000) (-48404410703 / 1000000000000)))) (orderedInterval (-534259007 / 1000000000000) (-534258975 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (440044877661753 / 4000000000000) 2 (IntervalRat.scale (481 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-56632494157 / 1000000000000) (-56632494156 / 1000000000000), orderedInterval (-50532535049 / 1000000000000) (-50532535048 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1788757997133913 / 4000000000000) 2 (IntervalRat.scale (481 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (36071387635 / 1000000000000) (36071398329 / 1000000000000), orderedInterval (-11106304569 / 1000000000000) (-11106293875 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1194807443770967 / 4000000000000) 2 (IntervalRat.scale (481 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-39708959656 / 1000000000000) (-39708959655 / 1000000000000), orderedInterval (-23481043798 / 1000000000000) (-23481043797 / 1000000000000)))) (orderedInterval (-1298639947 / 1000000000000) (-1298636792 / 1000000000000))) = true
  rfl'

theorem compactCertificate369_chunkChecks2 :
    compactCertificate369.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate369.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate369_chunkChecks2_0
    compactCertificate369_chunkChecks2_1 compactCertificate369_chunkChecks2_2

theorem compactCertificate369_chunkChecks3_0 :
    compactCertificate369.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (481 / 2) 3 (IntervalRat.scale (481 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (29799982188 / 1000000000000) (29799990141 / 1000000000000), orderedInterval (-42002753688 / 1000000000000) (-42002745735 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (708604845940381 / 4000000000000) 3 (IntervalRat.scale (481 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (54340850580 / 1000000000000) (54340861457 / 1000000000000), orderedInterval (-25465706159 / 1000000000000) (-25465695282 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (229148247971773 / 800000000000) 3 (IntervalRat.scale (481 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-45843207675 / 1000000000000) (-45843207671 / 1000000000000), orderedInterval (-10918052603 / 1000000000000) (-10918052599 / 1000000000000)))) (orderedInterval (17859409584 / 1000000000000) (17859412816 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (206769126759767 / 4000000000000) 3 (IntervalRat.scale (481 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (89078223476 / 1000000000000) (89078264536 / 1000000000000), orderedInterval (-67046657260 / 1000000000000) (-67046616199 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (555410958960299 / 4000000000000) 3 (IntervalRat.scale (481 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (66806826132 / 1000000000000) (66806826136 / 1000000000000), orderedInterval (10790098464 / 1000000000000) (10790098468 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1508048796395583 / 4000000000000) 3 (IntervalRat.scale (481 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29653363148 / 1000000000000) (29653363149 / 1000000000000), orderedInterval (28408343887 / 1000000000000) (28408343888 / 1000000000000)))) (orderedInterval (7678402841 / 1000000000000) (7678402915 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1110821917921079 / 4000000000000) 3 (IntervalRat.scale (481 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (42913420859 / 1000000000000) (42913443121 / 1000000000000), orderedInterval (-21310807418 / 1000000000000) (-21310785156 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1903412289710867 / 4000000000000) 3 (IntervalRat.scale (481 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-28281139049 / 1000000000000) (-28281106391 / 1000000000000), orderedInterval (23225116733 / 1000000000000) (23225149391 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1402044877661753 / 4000000000000) 3 (IntervalRat.scale (481 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-22714238856 / 1000000000000) (-22714236415 / 1000000000000), orderedInterval (36092419139 / 1000000000000) (36092421579 / 1000000000000)))) (orderedInterval (2857847683 / 1000000000000) (2857855761 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate369_chunkChecks3_1 :
    compactCertificate369.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2151097394354519 / 4000000000000) 3 (IntervalRat.scale (481 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-33549726703 / 1000000000000) (-33549726671 / 1000000000000), orderedInterval (-7599011623 / 1000000000000) (-7599011592 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1241936659683551 / 4000000000000) 3 (IntervalRat.scale (481 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-11268065180 / 1000000000000) (-11268065179 / 1000000000000), orderedInterval (-43838926833 / 1000000000000) (-43838926832 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2203838396514859 / 4000000000000) 3 (IntervalRat.scale (481 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-31371366289 / 1000000000000) (-31371322456 / 1000000000000), orderedInterval (13117102327 / 1000000000000) (13117146159 / 1000000000000)))) (orderedInterval (-30505639855 / 1000000000000) (-30505563814 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2059111704422071 / 4000000000000) 3 (IntervalRat.scale (481 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (11790111938 / 1000000000000) (11790111939 / 1000000000000), orderedInterval (33119830929 / 1000000000000) (33119830930 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1469479272848743 / 4000000000000) 3 (IntervalRat.scale (481 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-23109656579 / 1000000000000) (-23109656578 / 1000000000000), orderedInterval (-34593060910 / 1000000000000) (-34593060909 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1666232876880897 / 4000000000000) 3 (IntervalRat.scale (481 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (18346740199 / 1000000000000) (18346740900 / 1000000000000), orderedInterval (-34542783322 / 1000000000000) (-34542782621 / 1000000000000)))) (orderedInterval (16587881534 / 1000000000000) (16587881684 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1389131259233393 / 4000000000000) 3 (IntervalRat.scale (481 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (25874752784 / 1000000000000) (25874759080 / 1000000000000), orderedInterval (-34149461591 / 1000000000000) (-34149455295 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1227339595657253 / 4000000000000) 3 (IntervalRat.scale (481 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-11542211503 / 1000000000000) (-11542211436 / 1000000000000), orderedInterval (44082121926 / 1000000000000) (44082121992 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (355730852680047 / 800000000000) 3 (IntervalRat.scale (481 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-23123320071 / 1000000000000) (-23123315969 / 1000000000000), orderedInterval (29975974116 / 1000000000000) (29975978218 / 1000000000000)))) (orderedInterval (1573720428 / 1000000000000) (1573721398 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate369_chunkChecks3_2 :
    compactCertificate369.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (983970259602109 / 4000000000000) 3 (IntervalRat.scale (481 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (50202347742 / 1000000000000) (50202348542 / 1000000000000), orderedInterval (-8328986644 / 1000000000000) (-8328985845 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (834122486236949 / 4000000000000) 3 (IntervalRat.scale (481 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (50901782933 / 1000000000000) (50901791788 / 1000000000000), orderedInterval (-21613580429 / 1000000000000) (-21613571574 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (521955122338247 / 4000000000000) 3 (IntervalRat.scale (481 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-43575097525 / 1000000000000) (-43575074033 / 1000000000000), orderedInterval (54755887399 / 1000000000000) (54755910890 / 1000000000000)))) (orderedInterval (-2552811003 / 1000000000000) (-2552810362 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (280709200737849 / 4000000000000) 3 (IntervalRat.scale (481 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (91662791566 / 1000000000000) (91662792641 / 1000000000000), orderedInterval (-26524410756 / 1000000000000) (-26524409681 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (762180085720547 / 4000000000000) 3 (IntervalRat.scale (481 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (17489077500 / 1000000000000) (17489077802 / 1000000000000), orderedInterval (-55138432720 / 1000000000000) (-55138432419 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1040691746271619 / 4000000000000) 3 (IntervalRat.scale (481 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-10101852446 / 1000000000000) (-10101852445 / 1000000000000), orderedInterval (-48404410704 / 1000000000000) (-48404410703 / 1000000000000)))) (orderedInterval (-5328490306 / 1000000000000) (-5328490275 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (440044877661753 / 4000000000000) 3 (IntervalRat.scale (481 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-56632494157 / 1000000000000) (-56632494156 / 1000000000000), orderedInterval (-50532535049 / 1000000000000) (-50532535048 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1788757997133913 / 4000000000000) 3 (IntervalRat.scale (481 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (36071387635 / 1000000000000) (36071398329 / 1000000000000), orderedInterval (-11106304569 / 1000000000000) (-11106293875 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1194807443770967 / 4000000000000) 3 (IntervalRat.scale (481 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-39708959656 / 1000000000000) (-39708959655 / 1000000000000), orderedInterval (-23481043798 / 1000000000000) (-23481043797 / 1000000000000)))) (orderedInterval (-14218155228 / 1000000000000) (-14218149405 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate369_chunkChecks3 :
    compactCertificate369.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate369.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate369_chunkChecks3_0
    compactCertificate369_chunkChecks3_1 compactCertificate369_chunkChecks3_2

theorem compactCertificate369_chunkChecks4_0 :
    compactCertificate369.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (481 / 2) 4 (IntervalRat.scale (481 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (29799982188 / 1000000000000) (29799990141 / 1000000000000), orderedInterval (-42002753688 / 1000000000000) (-42002745735 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (708604845940381 / 4000000000000) 4 (IntervalRat.scale (481 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (54340850580 / 1000000000000) (54340861457 / 1000000000000), orderedInterval (-25465706159 / 1000000000000) (-25465695282 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (229148247971773 / 800000000000) 4 (IntervalRat.scale (481 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-45843207675 / 1000000000000) (-45843207671 / 1000000000000), orderedInterval (-10918052603 / 1000000000000) (-10918052599 / 1000000000000)))) (orderedInterval (6399304377 / 1000000000000) (6399307616 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (206769126759767 / 4000000000000) 4 (IntervalRat.scale (481 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (89078223476 / 1000000000000) (89078264536 / 1000000000000), orderedInterval (-67046657260 / 1000000000000) (-67046616199 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (555410958960299 / 4000000000000) 4 (IntervalRat.scale (481 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (66806826132 / 1000000000000) (66806826136 / 1000000000000), orderedInterval (10790098464 / 1000000000000) (10790098468 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1508048796395583 / 4000000000000) 4 (IntervalRat.scale (481 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29653363148 / 1000000000000) (29653363149 / 1000000000000), orderedInterval (28408343887 / 1000000000000) (28408343888 / 1000000000000)))) (orderedInterval (-12525199490 / 1000000000000) (-12525199383 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1110821917921079 / 4000000000000) 4 (IntervalRat.scale (481 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (42913420859 / 1000000000000) (42913443121 / 1000000000000), orderedInterval (-21310807418 / 1000000000000) (-21310785156 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1903412289710867 / 4000000000000) 4 (IntervalRat.scale (481 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-28281139049 / 1000000000000) (-28281106391 / 1000000000000), orderedInterval (23225116733 / 1000000000000) (23225149391 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1402044877661753 / 4000000000000) 4 (IntervalRat.scale (481 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-22714238856 / 1000000000000) (-22714236415 / 1000000000000), orderedInterval (36092419139 / 1000000000000) (36092421579 / 1000000000000)))) (orderedInterval (10868399538 / 1000000000000) (10868415449 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate369_chunkChecks4_1 :
    compactCertificate369.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2151097394354519 / 4000000000000) 4 (IntervalRat.scale (481 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-33549726703 / 1000000000000) (-33549726671 / 1000000000000), orderedInterval (-7599011623 / 1000000000000) (-7599011592 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1241936659683551 / 4000000000000) 4 (IntervalRat.scale (481 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-11268065180 / 1000000000000) (-11268065179 / 1000000000000), orderedInterval (-43838926833 / 1000000000000) (-43838926832 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2203838396514859 / 4000000000000) 4 (IntervalRat.scale (481 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-31371366289 / 1000000000000) (-31371322456 / 1000000000000), orderedInterval (13117102327 / 1000000000000) (13117146159 / 1000000000000)))) (orderedInterval (24135497740 / 1000000000000) (24135672191 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2059111704422071 / 4000000000000) 4 (IntervalRat.scale (481 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (11790111938 / 1000000000000) (11790111939 / 1000000000000), orderedInterval (33119830929 / 1000000000000) (33119830930 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1469479272848743 / 4000000000000) 4 (IntervalRat.scale (481 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-23109656579 / 1000000000000) (-23109656578 / 1000000000000), orderedInterval (-34593060910 / 1000000000000) (-34593060909 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1666232876880897 / 4000000000000) 4 (IntervalRat.scale (481 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (18346740199 / 1000000000000) (18346740900 / 1000000000000), orderedInterval (-34542783322 / 1000000000000) (-34542782621 / 1000000000000)))) (orderedInterval (-17339016662 / 1000000000000) (-17339016402 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1389131259233393 / 4000000000000) 4 (IntervalRat.scale (481 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (25874752784 / 1000000000000) (25874759080 / 1000000000000), orderedInterval (-34149461591 / 1000000000000) (-34149455295 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1227339595657253 / 4000000000000) 4 (IntervalRat.scale (481 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-11542211503 / 1000000000000) (-11542211436 / 1000000000000), orderedInterval (44082121926 / 1000000000000) (44082121992 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (355730852680047 / 800000000000) 4 (IntervalRat.scale (481 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-23123320071 / 1000000000000) (-23123315969 / 1000000000000), orderedInterval (29975974116 / 1000000000000) (29975978218 / 1000000000000)))) (orderedInterval (-3882622107 / 1000000000000) (-3882620424 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate369_chunkChecks4_2 :
    compactCertificate369.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (983970259602109 / 4000000000000) 4 (IntervalRat.scale (481 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (50202347742 / 1000000000000) (50202348542 / 1000000000000), orderedInterval (-8328986644 / 1000000000000) (-8328985845 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (834122486236949 / 4000000000000) 4 (IntervalRat.scale (481 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (50901782933 / 1000000000000) (50901791788 / 1000000000000), orderedInterval (-21613580429 / 1000000000000) (-21613571574 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (521955122338247 / 4000000000000) 4 (IntervalRat.scale (481 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-43575097525 / 1000000000000) (-43575074033 / 1000000000000), orderedInterval (54755887399 / 1000000000000) (54755910890 / 1000000000000)))) (orderedInterval (-10515712501 / 1000000000000) (-10515711955 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (280709200737849 / 4000000000000) 4 (IntervalRat.scale (481 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (91662791566 / 1000000000000) (91662792641 / 1000000000000), orderedInterval (-26524410756 / 1000000000000) (-26524409681 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (762180085720547 / 4000000000000) 4 (IntervalRat.scale (481 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (17489077500 / 1000000000000) (17489077802 / 1000000000000), orderedInterval (-55138432720 / 1000000000000) (-55138432419 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1040691746271619 / 4000000000000) 4 (IntervalRat.scale (481 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-10101852446 / 1000000000000) (-10101852445 / 1000000000000), orderedInterval (-48404410704 / 1000000000000) (-48404410703 / 1000000000000)))) (orderedInterval (936014114 / 1000000000000) (936014145 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (440044877661753 / 4000000000000) 4 (IntervalRat.scale (481 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-56632494157 / 1000000000000) (-56632494156 / 1000000000000), orderedInterval (-50532535049 / 1000000000000) (-50532535048 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1788757997133913 / 4000000000000) 4 (IntervalRat.scale (481 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (36071387635 / 1000000000000) (36071398329 / 1000000000000), orderedInterval (-11106304569 / 1000000000000) (-11106293875 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1194807443770967 / 4000000000000) 4 (IntervalRat.scale (481 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-39708959656 / 1000000000000) (-39708959655 / 1000000000000), orderedInterval (-23481043798 / 1000000000000) (-23481043797 / 1000000000000)))) (orderedInterval (-17267805683 / 1000000000000) (-17267794887 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate369_chunkChecks4 :
    compactCertificate369.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate369.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate369_chunkChecks4_0
    compactCertificate369_chunkChecks4_1 compactCertificate369_chunkChecks4_2

theorem compactCertificate369_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate369.chunkCheck r b = true :=
  compactCertificate369.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate369_chunkChecks0
    · exact compactCertificate369_chunkChecks1
    · exact compactCertificate369_chunkChecks2
    · exact compactCertificate369_chunkChecks3
    · exact compactCertificate369_chunkChecks4)

theorem compactCertificate369_coefficient0 :
    compactCertificate369.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate369_coefficient1 :
    compactCertificate369.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate369_coefficient2 :
    compactCertificate369.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate369_coefficient3 :
    compactCertificate369.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate369_coefficient4 :
    compactCertificate369.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate369_coefficients : ∀ r : Fin 5,
    compactCertificate369.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate369_coefficient0
  · exact compactCertificate369_coefficient1
  · exact compactCertificate369_coefficient2
  · exact compactCertificate369_coefficient3
  · exact compactCertificate369_coefficient4

theorem compactCertificate369_lower : (1 : ℚ) ≤ compactCertificate369.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate369, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate369_proves {t : ℝ} (ht : t ∈ compactCertificate369.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate369.proves compactCertificate369_states compactCertificate369_chunks
    compactCertificate369_coefficients compactCertificate369_lower ht

end Erdos232
