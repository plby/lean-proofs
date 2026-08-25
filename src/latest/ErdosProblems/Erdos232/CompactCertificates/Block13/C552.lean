/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate552 : CompactCertificate where
  left := 423
  right := 424
  center := 847 / 2
  grid := fun i =>
    match i.val with
    | 0 => 135
    | 1 => 99
    | 2 => 161
    | 3 => 29
    | 4 => 78
    | 5 => 211
    | 6 => 156
    | 7 => 267
    | 8 => 197
    | 9 => 302
    | 10 => 174
    | 11 => 309
    | 12 => 289
    | 13 => 206
    | 14 => 234
    | 15 => 195
    | 16 => 172
    | 17 => 249
    | 18 => 138
    | 19 => 117
    | 20 => 73
    | 21 => 39
    | 22 => 107
    | 23 => 146
    | 24 => 62
    | 25 => 251
    | _ => 168
  point := fun i =>
    match i.val with
    | 0 => 847 / 2
    | 1 => 1247792732872147 / 4000000000000
    | 2 => 403510532291251 / 800000000000
    | 3 => 364102807412729 / 4000000000000
    | 4 => 978031356007013 / 4000000000000
    | 5 => 2655545385752721 / 4000000000000
    | 6 => 1956062712014873 / 4000000000000
    | 7 => 3351746797058429 / 4000000000000
    | 8 => 2468881520539511 / 4000000000000
    | 9 => 3787899153884153 / 4000000000000
    | 10 => 2186944596157937 / 4000000000000
    | 11 => 3880771563093733 / 4000000000000
    | 12 => 3625920194689177 / 4000000000000
    | 13 => 2587627742417641 / 4000000000000
    | 14 => 2934094068021039 / 4000000000000
    | 15 => 2446141739232191 / 4000000000000
    | 16 => 2161240410648011 / 4000000000000
    | 17 => 626411709397089 / 800000000000
    | 18 => 1732687754434483 / 4000000000000
    | 19 => 1468818598425563 / 4000000000000
    | 20 => 919118479460489 / 4000000000000
    | 21 => 494304975103863 / 4000000000000
    | 22 => 1342134163420589 / 4000000000000
    | 23 => 1832569457571853 / 4000000000000
    | 24 => 774881520539511 / 4000000000000
    | 25 => 3149850360857431 / 4000000000000
    | _ => 2103954064187129 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-6563083894 / 1000000000000) (-6563083893 / 1000000000000), orderedInterval (-38204308737 / 1000000000000) (-38204308736 / 1000000000000))
    | 1 => (orderedInterval (-44702850381 / 1000000000000) (-44702849416 / 1000000000000), orderedInterval (6586220086 / 1000000000000) (6586221051 / 1000000000000))
    | 2 => (orderedInterval (20731966279 / 1000000000000) (20731968298 / 1000000000000), orderedInterval (-28870996572 / 1000000000000) (-28870994554 / 1000000000000))
    | 3 => (orderedInterval (-54101100130 / 1000000000000) (-54101100129 / 1000000000000), orderedInterval (-63475355662 / 1000000000000) (-63475355661 / 1000000000000))
    | 4 => (orderedInterval (12549857964 / 1000000000000) (12549857965 / 1000000000000), orderedInterval (49433251093 / 1000000000000) (49433251094 / 1000000000000))
    | 5 => (orderedInterval (-30188041082 / 1000000000000) (-30188025742 / 1000000000000), orderedInterval (6922817463 / 1000000000000) (6922832802 / 1000000000000))
    | 6 => (orderedInterval (-10235589717 / 1000000000000) (-10235589690 / 1000000000000), orderedInterval (34609200436 / 1000000000000) (34609200463 / 1000000000000))
    | 7 => (orderedInterval (2293117787 / 1000000000000) (2293117788 / 1000000000000), orderedInterval (-27469324182 / 1000000000000) (-27469324181 / 1000000000000))
    | 8 => (orderedInterval (24919443818 / 1000000000000) (24919461244 / 1000000000000), orderedInterval (-20279787131 / 1000000000000) (-20279769705 / 1000000000000))
    | 9 => (orderedInterval (-21830728825 / 1000000000000) (-21830718577 / 1000000000000), orderedInterval (14000314168 / 1000000000000) (14000324416 / 1000000000000))
    | 10 => (orderedInterval (26391171870 / 1000000000000) (26391171871 / 1000000000000), orderedInterval (21607007146 / 1000000000000) (21607007147 / 1000000000000))
    | 11 => (orderedInterval (-5740808092 / 1000000000000) (-5740808091 / 1000000000000), orderedInterval (-24961451260 / 1000000000000) (-24961451259 / 1000000000000))
    | 12 => (orderedInterval (16142604845 / 1000000000000) (16142605093 / 1000000000000), orderedInterval (-21025922138 / 1000000000000) (-21025921891 / 1000000000000))
    | 13 => (orderedInterval (15697528211 / 1000000000000) (15697528212 / 1000000000000), orderedInterval (27148236888 / 1000000000000) (27148236889 / 1000000000000))
    | 14 => (orderedInterval (-21618514174 / 1000000000000) (-21618509101 / 1000000000000), orderedInterval (20028047247 / 1000000000000) (20028052320 / 1000000000000))
    | 15 => (orderedInterval (9224305913 / 1000000000000) (9224305923 / 1000000000000), orderedInterval (-30925677184 / 1000000000000) (-30925677174 / 1000000000000))
    | 16 => (orderedInterval (23179122792 / 1000000000000) (23179122793 / 1000000000000), orderedInterval (25296077497 / 1000000000000) (25296077498 / 1000000000000))
    | 17 => (orderedInterval (-28503024897 / 1000000000000) (-28503022814 / 1000000000000), orderedInterval (-765597309 / 1000000000000) (-765595226 / 1000000000000))
    | 18 => (orderedInterval (15536111109 / 1000000000000) (15536111110 / 1000000000000), orderedInterval (35029175906 / 1000000000000) (35029175907 / 1000000000000))
    | 19 => (orderedInterval (-17106078820 / 1000000000000) (-17106078819 / 1000000000000), orderedInterval (-37938203457 / 1000000000000) (-37938203456 / 1000000000000))
    | 20 => (orderedInterval (-49577380011 / 1000000000000) (-49577380010 / 1000000000000), orderedInterval (-17573891995 / 1000000000000) (-17573891994 / 1000000000000))
    | 21 => (orderedInterval (-69217730183 / 1000000000000) (-69217728840 / 1000000000000), orderedInterval (19267030515 / 1000000000000) (19267031858 / 1000000000000))
    | 22 => (orderedInterval (-7289986605 / 1000000000000) (-7289986604 / 1000000000000), orderedInterval (-42933214385 / 1000000000000) (-42933214384 / 1000000000000))
    | 23 => (orderedInterval (9401564887 / 1000000000000) (9401564888 / 1000000000000), orderedInterval (36061596529 / 1000000000000) (36061596530 / 1000000000000))
    | 24 => (orderedInterval (-15490078668 / 1000000000000) (-15490078479 / 1000000000000), orderedInterval (55233717827 / 1000000000000) (55233718016 / 1000000000000))
    | 25 => (orderedInterval (8182995603 / 1000000000000) (8182995606 / 1000000000000), orderedInterval (-27235384631 / 1000000000000) (-27235384628 / 1000000000000))
    | _ => (orderedInterval (-29532884261 / 1000000000000) (-29532802374 / 1000000000000), orderedInterval (18416643327 / 1000000000000) (18416725214 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-1801345143 / 1000000000000) (-1801344985 / 1000000000000)
      | 1 => orderedInterval (3191231692 / 1000000000000) (3191232834 / 1000000000000)
      | 2 => orderedInterval (531524852 / 1000000000000) (531525297 / 1000000000000)
      | 3 => orderedInterval (5018333991 / 1000000000000) (5018335980 / 1000000000000)
      | 4 => orderedInterval (1302381502 / 1000000000000) (1302381583 / 1000000000000)
      | 5 => orderedInterval (-1949734977 / 1000000000000) (-1949734883 / 1000000000000)
      | 6 => orderedInterval (-3129908531 / 1000000000000) (-3129908424 / 1000000000000)
      | 7 => orderedInterval (722975047 / 1000000000000) (722975123 / 1000000000000)
      | _ => orderedInterval (4781647425 / 1000000000000) (4781662908 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-17115415737 / 1000000000000) (-17115415556 / 1000000000000)
      | 1 => orderedInterval (418584740 / 1000000000000) (418586507 / 1000000000000)
      | 2 => orderedInterval (962077721 / 1000000000000) (962078377 / 1000000000000)
      | 3 => orderedInterval (-11624928200 / 1000000000000) (-11624923780 / 1000000000000)
      | 4 => orderedInterval (4558413882 / 1000000000000) (4558414019 / 1000000000000)
      | 5 => orderedInterval (-2398816303 / 1000000000000) (-2398816145 / 1000000000000)
      | 6 => orderedInterval (-4177370296 / 1000000000000) (-4177370197 / 1000000000000)
      | 7 => orderedInterval (-2321901659 / 1000000000000) (-2321901605 / 1000000000000)
      | _ => orderedInterval (-17052333 / 1000000000000) (-17033085 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (1142109288 / 1000000000000) (1142109500 / 1000000000000)
      | 1 => orderedInterval (-5454622359 / 1000000000000) (-5454619595 / 1000000000000)
      | 2 => orderedInterval (-1004622752 / 1000000000000) (-1004621782 / 1000000000000)
      | 3 => orderedInterval (-18343791365 / 1000000000000) (-18343781504 / 1000000000000)
      | 4 => orderedInterval (-2467413360 / 1000000000000) (-2467413126 / 1000000000000)
      | 5 => orderedInterval (4437438360 / 1000000000000) (4437438631 / 1000000000000)
      | 6 => orderedInterval (2355962997 / 1000000000000) (2355963091 / 1000000000000)
      | 7 => orderedInterval (636064886 / 1000000000000) (636064934 / 1000000000000)
      | _ => orderedInterval (-6225024816 / 1000000000000) (-6225000826 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (17977696291 / 1000000000000) (17977696540 / 1000000000000)
      | 1 => orderedInterval (1554568960 / 1000000000000) (1554573287 / 1000000000000)
      | 2 => orderedInterval (-5043189864 / 1000000000000) (-5043188424 / 1000000000000)
      | 3 => orderedInterval (67074578716 / 1000000000000) (67074600732 / 1000000000000)
      | 4 => orderedInterval (-12340016628 / 1000000000000) (-12340016221 / 1000000000000)
      | 5 => orderedInterval (4194895571 / 1000000000000) (4194896044 / 1000000000000)
      | 6 => orderedInterval (4679497799 / 1000000000000) (4679497890 / 1000000000000)
      | 7 => orderedInterval (3021840921 / 1000000000000) (3021840968 / 1000000000000)
      | _ => orderedInterval (-7649631014 / 1000000000000) (-7649601146 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-361044389 / 1000000000000) (-361044094 / 1000000000000)
      | 1 => orderedInterval (13004713712 / 1000000000000) (13004720502 / 1000000000000)
      | 2 => orderedInterval (1657046739 / 1000000000000) (1657048893 / 1000000000000)
      | 3 => orderedInterval (79613146078 / 1000000000000) (79613195329 / 1000000000000)
      | 4 => orderedInterval (3007548792 / 1000000000000) (3007549517 / 1000000000000)
      | 5 => orderedInterval (-11599408421 / 1000000000000) (-11599407582 / 1000000000000)
      | 6 => orderedInterval (-2333639249 / 1000000000000) (-2333639159 / 1000000000000)
      | 7 => orderedInterval (-926652391 / 1000000000000) (-926652342 / 1000000000000)
      | _ => orderedInterval (5254758903 / 1000000000000) (5254796206 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (8667105858 / 1000000000000) (8667125433 / 1000000000000)
    | 1 => orderedInterval (-31716408185 / 1000000000000) (-31716381465 / 1000000000000)
    | 2 => orderedInterval (-24923899121 / 1000000000000) (-24923860677 / 1000000000000)
    | 3 => orderedInterval (73470240752 / 1000000000000) (73470299670 / 1000000000000)
    | _ => orderedInterval (87316469774 / 1000000000000) (87316567270 / 1000000000000)

theorem compactCertificate552_stateChecks0 :
    compactCertificate552.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 135 12 (847 / 2)) (orderedInterval (-6563083894 / 1000000000000) (-6563083893 / 1000000000000), orderedInterval (-38204308737 / 1000000000000) (-38204308736 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 99 12 (1247792732872147 / 4000000000000)) (orderedInterval (-44702850381 / 1000000000000) (-44702849416 / 1000000000000), orderedInterval (6586220086 / 1000000000000) (6586221051 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 161 12 (403510532291251 / 800000000000)) (orderedInterval (20731966279 / 1000000000000) (20731968298 / 1000000000000), orderedInterval (-28870996572 / 1000000000000) (-28870994554 / 1000000000000))) = true
  rfl'

theorem compactCertificate552_stateChecks1 :
    compactCertificate552.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 29 12 (364102807412729 / 4000000000000)) (orderedInterval (-54101100130 / 1000000000000) (-54101100129 / 1000000000000), orderedInterval (-63475355662 / 1000000000000) (-63475355661 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 78 12 (978031356007013 / 4000000000000)) (orderedInterval (12549857964 / 1000000000000) (12549857965 / 1000000000000), orderedInterval (49433251093 / 1000000000000) (49433251094 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 211 12 (2655545385752721 / 4000000000000)) (orderedInterval (-30188041082 / 1000000000000) (-30188025742 / 1000000000000), orderedInterval (6922817463 / 1000000000000) (6922832802 / 1000000000000))) = true
  rfl'

theorem compactCertificate552_stateChecks2 :
    compactCertificate552.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 156 12 (1956062712014873 / 4000000000000)) (orderedInterval (-10235589717 / 1000000000000) (-10235589690 / 1000000000000), orderedInterval (34609200436 / 1000000000000) (34609200463 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 267 12 (3351746797058429 / 4000000000000)) (orderedInterval (2293117787 / 1000000000000) (2293117788 / 1000000000000), orderedInterval (-27469324182 / 1000000000000) (-27469324181 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 197 12 (2468881520539511 / 4000000000000)) (orderedInterval (24919443818 / 1000000000000) (24919461244 / 1000000000000), orderedInterval (-20279787131 / 1000000000000) (-20279769705 / 1000000000000))) = true
  rfl'

theorem compactCertificate552_stateChecks3 :
    compactCertificate552.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 302 12 (3787899153884153 / 4000000000000)) (orderedInterval (-21830728825 / 1000000000000) (-21830718577 / 1000000000000), orderedInterval (14000314168 / 1000000000000) (14000324416 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 174 12 (2186944596157937 / 4000000000000)) (orderedInterval (26391171870 / 1000000000000) (26391171871 / 1000000000000), orderedInterval (21607007146 / 1000000000000) (21607007147 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 309 12 (3880771563093733 / 4000000000000)) (orderedInterval (-5740808092 / 1000000000000) (-5740808091 / 1000000000000), orderedInterval (-24961451260 / 1000000000000) (-24961451259 / 1000000000000))) = true
  rfl'

theorem compactCertificate552_stateChecks4 :
    compactCertificate552.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 289 12 (3625920194689177 / 4000000000000)) (orderedInterval (16142604845 / 1000000000000) (16142605093 / 1000000000000), orderedInterval (-21025922138 / 1000000000000) (-21025921891 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 206 12 (2587627742417641 / 4000000000000)) (orderedInterval (15697528211 / 1000000000000) (15697528212 / 1000000000000), orderedInterval (27148236888 / 1000000000000) (27148236889 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 234 12 (2934094068021039 / 4000000000000)) (orderedInterval (-21618514174 / 1000000000000) (-21618509101 / 1000000000000), orderedInterval (20028047247 / 1000000000000) (20028052320 / 1000000000000))) = true
  rfl'

theorem compactCertificate552_stateChecks5 :
    compactCertificate552.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 195 12 (2446141739232191 / 4000000000000)) (orderedInterval (9224305913 / 1000000000000) (9224305923 / 1000000000000), orderedInterval (-30925677184 / 1000000000000) (-30925677174 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 172 12 (2161240410648011 / 4000000000000)) (orderedInterval (23179122792 / 1000000000000) (23179122793 / 1000000000000), orderedInterval (25296077497 / 1000000000000) (25296077498 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 249 12 (626411709397089 / 800000000000)) (orderedInterval (-28503024897 / 1000000000000) (-28503022814 / 1000000000000), orderedInterval (-765597309 / 1000000000000) (-765595226 / 1000000000000))) = true
  rfl'

theorem compactCertificate552_stateChecks6 :
    compactCertificate552.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 138 12 (1732687754434483 / 4000000000000)) (orderedInterval (15536111109 / 1000000000000) (15536111110 / 1000000000000), orderedInterval (35029175906 / 1000000000000) (35029175907 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 117 12 (1468818598425563 / 4000000000000)) (orderedInterval (-17106078820 / 1000000000000) (-17106078819 / 1000000000000), orderedInterval (-37938203457 / 1000000000000) (-37938203456 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 73 12 (919118479460489 / 4000000000000)) (orderedInterval (-49577380011 / 1000000000000) (-49577380010 / 1000000000000), orderedInterval (-17573891995 / 1000000000000) (-17573891994 / 1000000000000))) = true
  rfl'

theorem compactCertificate552_stateChecks7 :
    compactCertificate552.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 39 12 (494304975103863 / 4000000000000)) (orderedInterval (-69217730183 / 1000000000000) (-69217728840 / 1000000000000), orderedInterval (19267030515 / 1000000000000) (19267031858 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 107 12 (1342134163420589 / 4000000000000)) (orderedInterval (-7289986605 / 1000000000000) (-7289986604 / 1000000000000), orderedInterval (-42933214385 / 1000000000000) (-42933214384 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 146 12 (1832569457571853 / 4000000000000)) (orderedInterval (9401564887 / 1000000000000) (9401564888 / 1000000000000), orderedInterval (36061596529 / 1000000000000) (36061596530 / 1000000000000))) = true
  rfl'

theorem compactCertificate552_stateChecks8 :
    compactCertificate552.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (774881520539511 / 4000000000000)) (orderedInterval (-15490078668 / 1000000000000) (-15490078479 / 1000000000000), orderedInterval (55233717827 / 1000000000000) (55233718016 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 251 12 (3149850360857431 / 4000000000000)) (orderedInterval (8182995603 / 1000000000000) (8182995606 / 1000000000000), orderedInterval (-27235384631 / 1000000000000) (-27235384628 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 168 12 (2103954064187129 / 4000000000000)) (orderedInterval (-29532884261 / 1000000000000) (-29532802374 / 1000000000000), orderedInterval (18416643327 / 1000000000000) (18416725214 / 1000000000000))) = true
  rfl'

theorem compactCertificate552_states : ∀ j,
    BesselStateValid (compactCertificate552.point j) (compactCertificate552.state j) :=
  compactCertificate552.statesValid_of_checks3 compactCertificate552_stateChecks0
    compactCertificate552_stateChecks1 compactCertificate552_stateChecks2
    compactCertificate552_stateChecks3 compactCertificate552_stateChecks4
    compactCertificate552_stateChecks5 compactCertificate552_stateChecks6
    compactCertificate552_stateChecks7 compactCertificate552_stateChecks8

theorem compactCertificate552_chunkChecks0_0 :
    compactCertificate552.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (847 / 2) 0 (IntervalRat.scale (847 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-6563083894 / 1000000000000) (-6563083893 / 1000000000000), orderedInterval (-38204308737 / 1000000000000) (-38204308736 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1247792732872147 / 4000000000000) 0 (IntervalRat.scale (847 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-44702850381 / 1000000000000) (-44702849416 / 1000000000000), orderedInterval (6586220086 / 1000000000000) (6586221051 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (403510532291251 / 800000000000) 0 (IntervalRat.scale (847 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (20731966279 / 1000000000000) (20731968298 / 1000000000000), orderedInterval (-28870996572 / 1000000000000) (-28870994554 / 1000000000000)))) (orderedInterval (-1801345143 / 1000000000000) (-1801344985 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (364102807412729 / 4000000000000) 0 (IntervalRat.scale (847 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-54101100130 / 1000000000000) (-54101100129 / 1000000000000), orderedInterval (-63475355662 / 1000000000000) (-63475355661 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (978031356007013 / 4000000000000) 0 (IntervalRat.scale (847 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (12549857964 / 1000000000000) (12549857965 / 1000000000000), orderedInterval (49433251093 / 1000000000000) (49433251094 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2655545385752721 / 4000000000000) 0 (IntervalRat.scale (847 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30188041082 / 1000000000000) (-30188025742 / 1000000000000), orderedInterval (6922817463 / 1000000000000) (6922832802 / 1000000000000)))) (orderedInterval (3191231692 / 1000000000000) (3191232834 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1956062712014873 / 4000000000000) 0 (IntervalRat.scale (847 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-10235589717 / 1000000000000) (-10235589690 / 1000000000000), orderedInterval (34609200436 / 1000000000000) (34609200463 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3351746797058429 / 4000000000000) 0 (IntervalRat.scale (847 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (2293117787 / 1000000000000) (2293117788 / 1000000000000), orderedInterval (-27469324182 / 1000000000000) (-27469324181 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2468881520539511 / 4000000000000) 0 (IntervalRat.scale (847 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (24919443818 / 1000000000000) (24919461244 / 1000000000000), orderedInterval (-20279787131 / 1000000000000) (-20279769705 / 1000000000000)))) (orderedInterval (531524852 / 1000000000000) (531525297 / 1000000000000))) = true
  rfl'

theorem compactCertificate552_chunkChecks0_1 :
    compactCertificate552.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3787899153884153 / 4000000000000) 0 (IntervalRat.scale (847 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-21830728825 / 1000000000000) (-21830718577 / 1000000000000), orderedInterval (14000314168 / 1000000000000) (14000324416 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2186944596157937 / 4000000000000) 0 (IntervalRat.scale (847 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (26391171870 / 1000000000000) (26391171871 / 1000000000000), orderedInterval (21607007146 / 1000000000000) (21607007147 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3880771563093733 / 4000000000000) 0 (IntervalRat.scale (847 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-5740808092 / 1000000000000) (-5740808091 / 1000000000000), orderedInterval (-24961451260 / 1000000000000) (-24961451259 / 1000000000000)))) (orderedInterval (5018333991 / 1000000000000) (5018335980 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3625920194689177 / 4000000000000) 0 (IntervalRat.scale (847 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (16142604845 / 1000000000000) (16142605093 / 1000000000000), orderedInterval (-21025922138 / 1000000000000) (-21025921891 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2587627742417641 / 4000000000000) 0 (IntervalRat.scale (847 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (15697528211 / 1000000000000) (15697528212 / 1000000000000), orderedInterval (27148236888 / 1000000000000) (27148236889 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2934094068021039 / 4000000000000) 0 (IntervalRat.scale (847 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-21618514174 / 1000000000000) (-21618509101 / 1000000000000), orderedInterval (20028047247 / 1000000000000) (20028052320 / 1000000000000)))) (orderedInterval (1302381502 / 1000000000000) (1302381583 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2446141739232191 / 4000000000000) 0 (IntervalRat.scale (847 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (9224305913 / 1000000000000) (9224305923 / 1000000000000), orderedInterval (-30925677184 / 1000000000000) (-30925677174 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2161240410648011 / 4000000000000) 0 (IntervalRat.scale (847 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (23179122792 / 1000000000000) (23179122793 / 1000000000000), orderedInterval (25296077497 / 1000000000000) (25296077498 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (626411709397089 / 800000000000) 0 (IntervalRat.scale (847 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-28503024897 / 1000000000000) (-28503022814 / 1000000000000), orderedInterval (-765597309 / 1000000000000) (-765595226 / 1000000000000)))) (orderedInterval (-1949734977 / 1000000000000) (-1949734883 / 1000000000000))) = true
  rfl'

theorem compactCertificate552_chunkChecks0_2 :
    compactCertificate552.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1732687754434483 / 4000000000000) 0 (IntervalRat.scale (847 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (15536111109 / 1000000000000) (15536111110 / 1000000000000), orderedInterval (35029175906 / 1000000000000) (35029175907 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1468818598425563 / 4000000000000) 0 (IntervalRat.scale (847 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-17106078820 / 1000000000000) (-17106078819 / 1000000000000), orderedInterval (-37938203457 / 1000000000000) (-37938203456 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (919118479460489 / 4000000000000) 0 (IntervalRat.scale (847 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-49577380011 / 1000000000000) (-49577380010 / 1000000000000), orderedInterval (-17573891995 / 1000000000000) (-17573891994 / 1000000000000)))) (orderedInterval (-3129908531 / 1000000000000) (-3129908424 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (494304975103863 / 4000000000000) 0 (IntervalRat.scale (847 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-69217730183 / 1000000000000) (-69217728840 / 1000000000000), orderedInterval (19267030515 / 1000000000000) (19267031858 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1342134163420589 / 4000000000000) 0 (IntervalRat.scale (847 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-7289986605 / 1000000000000) (-7289986604 / 1000000000000), orderedInterval (-42933214385 / 1000000000000) (-42933214384 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1832569457571853 / 4000000000000) 0 (IntervalRat.scale (847 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (9401564887 / 1000000000000) (9401564888 / 1000000000000), orderedInterval (36061596529 / 1000000000000) (36061596530 / 1000000000000)))) (orderedInterval (722975047 / 1000000000000) (722975123 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (774881520539511 / 4000000000000) 0 (IntervalRat.scale (847 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-15490078668 / 1000000000000) (-15490078479 / 1000000000000), orderedInterval (55233717827 / 1000000000000) (55233718016 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3149850360857431 / 4000000000000) 0 (IntervalRat.scale (847 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (8182995603 / 1000000000000) (8182995606 / 1000000000000), orderedInterval (-27235384631 / 1000000000000) (-27235384628 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2103954064187129 / 4000000000000) 0 (IntervalRat.scale (847 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-29532884261 / 1000000000000) (-29532802374 / 1000000000000), orderedInterval (18416643327 / 1000000000000) (18416725214 / 1000000000000)))) (orderedInterval (4781647425 / 1000000000000) (4781662908 / 1000000000000))) = true
  rfl'

theorem compactCertificate552_chunkChecks0 :
    compactCertificate552.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate552.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate552_chunkChecks0_0
    compactCertificate552_chunkChecks0_1 compactCertificate552_chunkChecks0_2

theorem compactCertificate552_chunkChecks1_0 :
    compactCertificate552.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (847 / 2) 1 (IntervalRat.scale (847 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-6563083894 / 1000000000000) (-6563083893 / 1000000000000), orderedInterval (-38204308737 / 1000000000000) (-38204308736 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1247792732872147 / 4000000000000) 1 (IntervalRat.scale (847 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-44702850381 / 1000000000000) (-44702849416 / 1000000000000), orderedInterval (6586220086 / 1000000000000) (6586221051 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (403510532291251 / 800000000000) 1 (IntervalRat.scale (847 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (20731966279 / 1000000000000) (20731968298 / 1000000000000), orderedInterval (-28870996572 / 1000000000000) (-28870994554 / 1000000000000)))) (orderedInterval (-17115415737 / 1000000000000) (-17115415556 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (364102807412729 / 4000000000000) 1 (IntervalRat.scale (847 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-54101100130 / 1000000000000) (-54101100129 / 1000000000000), orderedInterval (-63475355662 / 1000000000000) (-63475355661 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (978031356007013 / 4000000000000) 1 (IntervalRat.scale (847 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (12549857964 / 1000000000000) (12549857965 / 1000000000000), orderedInterval (49433251093 / 1000000000000) (49433251094 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2655545385752721 / 4000000000000) 1 (IntervalRat.scale (847 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30188041082 / 1000000000000) (-30188025742 / 1000000000000), orderedInterval (6922817463 / 1000000000000) (6922832802 / 1000000000000)))) (orderedInterval (418584740 / 1000000000000) (418586507 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1956062712014873 / 4000000000000) 1 (IntervalRat.scale (847 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-10235589717 / 1000000000000) (-10235589690 / 1000000000000), orderedInterval (34609200436 / 1000000000000) (34609200463 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3351746797058429 / 4000000000000) 1 (IntervalRat.scale (847 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (2293117787 / 1000000000000) (2293117788 / 1000000000000), orderedInterval (-27469324182 / 1000000000000) (-27469324181 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2468881520539511 / 4000000000000) 1 (IntervalRat.scale (847 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (24919443818 / 1000000000000) (24919461244 / 1000000000000), orderedInterval (-20279787131 / 1000000000000) (-20279769705 / 1000000000000)))) (orderedInterval (962077721 / 1000000000000) (962078377 / 1000000000000))) = true
  rfl'

theorem compactCertificate552_chunkChecks1_1 :
    compactCertificate552.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3787899153884153 / 4000000000000) 1 (IntervalRat.scale (847 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-21830728825 / 1000000000000) (-21830718577 / 1000000000000), orderedInterval (14000314168 / 1000000000000) (14000324416 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2186944596157937 / 4000000000000) 1 (IntervalRat.scale (847 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (26391171870 / 1000000000000) (26391171871 / 1000000000000), orderedInterval (21607007146 / 1000000000000) (21607007147 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3880771563093733 / 4000000000000) 1 (IntervalRat.scale (847 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-5740808092 / 1000000000000) (-5740808091 / 1000000000000), orderedInterval (-24961451260 / 1000000000000) (-24961451259 / 1000000000000)))) (orderedInterval (-11624928200 / 1000000000000) (-11624923780 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3625920194689177 / 4000000000000) 1 (IntervalRat.scale (847 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (16142604845 / 1000000000000) (16142605093 / 1000000000000), orderedInterval (-21025922138 / 1000000000000) (-21025921891 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2587627742417641 / 4000000000000) 1 (IntervalRat.scale (847 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (15697528211 / 1000000000000) (15697528212 / 1000000000000), orderedInterval (27148236888 / 1000000000000) (27148236889 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2934094068021039 / 4000000000000) 1 (IntervalRat.scale (847 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-21618514174 / 1000000000000) (-21618509101 / 1000000000000), orderedInterval (20028047247 / 1000000000000) (20028052320 / 1000000000000)))) (orderedInterval (4558413882 / 1000000000000) (4558414019 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2446141739232191 / 4000000000000) 1 (IntervalRat.scale (847 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (9224305913 / 1000000000000) (9224305923 / 1000000000000), orderedInterval (-30925677184 / 1000000000000) (-30925677174 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2161240410648011 / 4000000000000) 1 (IntervalRat.scale (847 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (23179122792 / 1000000000000) (23179122793 / 1000000000000), orderedInterval (25296077497 / 1000000000000) (25296077498 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (626411709397089 / 800000000000) 1 (IntervalRat.scale (847 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-28503024897 / 1000000000000) (-28503022814 / 1000000000000), orderedInterval (-765597309 / 1000000000000) (-765595226 / 1000000000000)))) (orderedInterval (-2398816303 / 1000000000000) (-2398816145 / 1000000000000))) = true
  rfl'

theorem compactCertificate552_chunkChecks1_2 :
    compactCertificate552.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1732687754434483 / 4000000000000) 1 (IntervalRat.scale (847 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (15536111109 / 1000000000000) (15536111110 / 1000000000000), orderedInterval (35029175906 / 1000000000000) (35029175907 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1468818598425563 / 4000000000000) 1 (IntervalRat.scale (847 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-17106078820 / 1000000000000) (-17106078819 / 1000000000000), orderedInterval (-37938203457 / 1000000000000) (-37938203456 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (919118479460489 / 4000000000000) 1 (IntervalRat.scale (847 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-49577380011 / 1000000000000) (-49577380010 / 1000000000000), orderedInterval (-17573891995 / 1000000000000) (-17573891994 / 1000000000000)))) (orderedInterval (-4177370296 / 1000000000000) (-4177370197 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (494304975103863 / 4000000000000) 1 (IntervalRat.scale (847 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-69217730183 / 1000000000000) (-69217728840 / 1000000000000), orderedInterval (19267030515 / 1000000000000) (19267031858 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1342134163420589 / 4000000000000) 1 (IntervalRat.scale (847 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-7289986605 / 1000000000000) (-7289986604 / 1000000000000), orderedInterval (-42933214385 / 1000000000000) (-42933214384 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1832569457571853 / 4000000000000) 1 (IntervalRat.scale (847 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (9401564887 / 1000000000000) (9401564888 / 1000000000000), orderedInterval (36061596529 / 1000000000000) (36061596530 / 1000000000000)))) (orderedInterval (-2321901659 / 1000000000000) (-2321901605 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (774881520539511 / 4000000000000) 1 (IntervalRat.scale (847 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-15490078668 / 1000000000000) (-15490078479 / 1000000000000), orderedInterval (55233717827 / 1000000000000) (55233718016 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3149850360857431 / 4000000000000) 1 (IntervalRat.scale (847 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (8182995603 / 1000000000000) (8182995606 / 1000000000000), orderedInterval (-27235384631 / 1000000000000) (-27235384628 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2103954064187129 / 4000000000000) 1 (IntervalRat.scale (847 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-29532884261 / 1000000000000) (-29532802374 / 1000000000000), orderedInterval (18416643327 / 1000000000000) (18416725214 / 1000000000000)))) (orderedInterval (-17052333 / 1000000000000) (-17033085 / 1000000000000))) = true
  rfl'

theorem compactCertificate552_chunkChecks1 :
    compactCertificate552.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate552.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate552_chunkChecks1_0
    compactCertificate552_chunkChecks1_1 compactCertificate552_chunkChecks1_2

theorem compactCertificate552_chunkChecks2_0 :
    compactCertificate552.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (847 / 2) 2 (IntervalRat.scale (847 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-6563083894 / 1000000000000) (-6563083893 / 1000000000000), orderedInterval (-38204308737 / 1000000000000) (-38204308736 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1247792732872147 / 4000000000000) 2 (IntervalRat.scale (847 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-44702850381 / 1000000000000) (-44702849416 / 1000000000000), orderedInterval (6586220086 / 1000000000000) (6586221051 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (403510532291251 / 800000000000) 2 (IntervalRat.scale (847 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (20731966279 / 1000000000000) (20731968298 / 1000000000000), orderedInterval (-28870996572 / 1000000000000) (-28870994554 / 1000000000000)))) (orderedInterval (1142109288 / 1000000000000) (1142109500 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (364102807412729 / 4000000000000) 2 (IntervalRat.scale (847 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-54101100130 / 1000000000000) (-54101100129 / 1000000000000), orderedInterval (-63475355662 / 1000000000000) (-63475355661 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (978031356007013 / 4000000000000) 2 (IntervalRat.scale (847 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (12549857964 / 1000000000000) (12549857965 / 1000000000000), orderedInterval (49433251093 / 1000000000000) (49433251094 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2655545385752721 / 4000000000000) 2 (IntervalRat.scale (847 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30188041082 / 1000000000000) (-30188025742 / 1000000000000), orderedInterval (6922817463 / 1000000000000) (6922832802 / 1000000000000)))) (orderedInterval (-5454622359 / 1000000000000) (-5454619595 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1956062712014873 / 4000000000000) 2 (IntervalRat.scale (847 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-10235589717 / 1000000000000) (-10235589690 / 1000000000000), orderedInterval (34609200436 / 1000000000000) (34609200463 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3351746797058429 / 4000000000000) 2 (IntervalRat.scale (847 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (2293117787 / 1000000000000) (2293117788 / 1000000000000), orderedInterval (-27469324182 / 1000000000000) (-27469324181 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2468881520539511 / 4000000000000) 2 (IntervalRat.scale (847 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (24919443818 / 1000000000000) (24919461244 / 1000000000000), orderedInterval (-20279787131 / 1000000000000) (-20279769705 / 1000000000000)))) (orderedInterval (-1004622752 / 1000000000000) (-1004621782 / 1000000000000))) = true
  rfl'

theorem compactCertificate552_chunkChecks2_1 :
    compactCertificate552.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3787899153884153 / 4000000000000) 2 (IntervalRat.scale (847 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-21830728825 / 1000000000000) (-21830718577 / 1000000000000), orderedInterval (14000314168 / 1000000000000) (14000324416 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2186944596157937 / 4000000000000) 2 (IntervalRat.scale (847 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (26391171870 / 1000000000000) (26391171871 / 1000000000000), orderedInterval (21607007146 / 1000000000000) (21607007147 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3880771563093733 / 4000000000000) 2 (IntervalRat.scale (847 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-5740808092 / 1000000000000) (-5740808091 / 1000000000000), orderedInterval (-24961451260 / 1000000000000) (-24961451259 / 1000000000000)))) (orderedInterval (-18343791365 / 1000000000000) (-18343781504 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3625920194689177 / 4000000000000) 2 (IntervalRat.scale (847 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (16142604845 / 1000000000000) (16142605093 / 1000000000000), orderedInterval (-21025922138 / 1000000000000) (-21025921891 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2587627742417641 / 4000000000000) 2 (IntervalRat.scale (847 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (15697528211 / 1000000000000) (15697528212 / 1000000000000), orderedInterval (27148236888 / 1000000000000) (27148236889 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2934094068021039 / 4000000000000) 2 (IntervalRat.scale (847 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-21618514174 / 1000000000000) (-21618509101 / 1000000000000), orderedInterval (20028047247 / 1000000000000) (20028052320 / 1000000000000)))) (orderedInterval (-2467413360 / 1000000000000) (-2467413126 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2446141739232191 / 4000000000000) 2 (IntervalRat.scale (847 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (9224305913 / 1000000000000) (9224305923 / 1000000000000), orderedInterval (-30925677184 / 1000000000000) (-30925677174 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2161240410648011 / 4000000000000) 2 (IntervalRat.scale (847 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (23179122792 / 1000000000000) (23179122793 / 1000000000000), orderedInterval (25296077497 / 1000000000000) (25296077498 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (626411709397089 / 800000000000) 2 (IntervalRat.scale (847 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-28503024897 / 1000000000000) (-28503022814 / 1000000000000), orderedInterval (-765597309 / 1000000000000) (-765595226 / 1000000000000)))) (orderedInterval (4437438360 / 1000000000000) (4437438631 / 1000000000000))) = true
  rfl'

theorem compactCertificate552_chunkChecks2_2 :
    compactCertificate552.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1732687754434483 / 4000000000000) 2 (IntervalRat.scale (847 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (15536111109 / 1000000000000) (15536111110 / 1000000000000), orderedInterval (35029175906 / 1000000000000) (35029175907 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1468818598425563 / 4000000000000) 2 (IntervalRat.scale (847 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-17106078820 / 1000000000000) (-17106078819 / 1000000000000), orderedInterval (-37938203457 / 1000000000000) (-37938203456 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (919118479460489 / 4000000000000) 2 (IntervalRat.scale (847 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-49577380011 / 1000000000000) (-49577380010 / 1000000000000), orderedInterval (-17573891995 / 1000000000000) (-17573891994 / 1000000000000)))) (orderedInterval (2355962997 / 1000000000000) (2355963091 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (494304975103863 / 4000000000000) 2 (IntervalRat.scale (847 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-69217730183 / 1000000000000) (-69217728840 / 1000000000000), orderedInterval (19267030515 / 1000000000000) (19267031858 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1342134163420589 / 4000000000000) 2 (IntervalRat.scale (847 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-7289986605 / 1000000000000) (-7289986604 / 1000000000000), orderedInterval (-42933214385 / 1000000000000) (-42933214384 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1832569457571853 / 4000000000000) 2 (IntervalRat.scale (847 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (9401564887 / 1000000000000) (9401564888 / 1000000000000), orderedInterval (36061596529 / 1000000000000) (36061596530 / 1000000000000)))) (orderedInterval (636064886 / 1000000000000) (636064934 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (774881520539511 / 4000000000000) 2 (IntervalRat.scale (847 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-15490078668 / 1000000000000) (-15490078479 / 1000000000000), orderedInterval (55233717827 / 1000000000000) (55233718016 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3149850360857431 / 4000000000000) 2 (IntervalRat.scale (847 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (8182995603 / 1000000000000) (8182995606 / 1000000000000), orderedInterval (-27235384631 / 1000000000000) (-27235384628 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2103954064187129 / 4000000000000) 2 (IntervalRat.scale (847 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-29532884261 / 1000000000000) (-29532802374 / 1000000000000), orderedInterval (18416643327 / 1000000000000) (18416725214 / 1000000000000)))) (orderedInterval (-6225024816 / 1000000000000) (-6225000826 / 1000000000000))) = true
  rfl'

theorem compactCertificate552_chunkChecks2 :
    compactCertificate552.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate552.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate552_chunkChecks2_0
    compactCertificate552_chunkChecks2_1 compactCertificate552_chunkChecks2_2

theorem compactCertificate552_chunkChecks3_0 :
    compactCertificate552.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (847 / 2) 3 (IntervalRat.scale (847 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-6563083894 / 1000000000000) (-6563083893 / 1000000000000), orderedInterval (-38204308737 / 1000000000000) (-38204308736 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1247792732872147 / 4000000000000) 3 (IntervalRat.scale (847 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-44702850381 / 1000000000000) (-44702849416 / 1000000000000), orderedInterval (6586220086 / 1000000000000) (6586221051 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (403510532291251 / 800000000000) 3 (IntervalRat.scale (847 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (20731966279 / 1000000000000) (20731968298 / 1000000000000), orderedInterval (-28870996572 / 1000000000000) (-28870994554 / 1000000000000)))) (orderedInterval (17977696291 / 1000000000000) (17977696540 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (364102807412729 / 4000000000000) 3 (IntervalRat.scale (847 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-54101100130 / 1000000000000) (-54101100129 / 1000000000000), orderedInterval (-63475355662 / 1000000000000) (-63475355661 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (978031356007013 / 4000000000000) 3 (IntervalRat.scale (847 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (12549857964 / 1000000000000) (12549857965 / 1000000000000), orderedInterval (49433251093 / 1000000000000) (49433251094 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2655545385752721 / 4000000000000) 3 (IntervalRat.scale (847 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30188041082 / 1000000000000) (-30188025742 / 1000000000000), orderedInterval (6922817463 / 1000000000000) (6922832802 / 1000000000000)))) (orderedInterval (1554568960 / 1000000000000) (1554573287 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1956062712014873 / 4000000000000) 3 (IntervalRat.scale (847 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-10235589717 / 1000000000000) (-10235589690 / 1000000000000), orderedInterval (34609200436 / 1000000000000) (34609200463 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3351746797058429 / 4000000000000) 3 (IntervalRat.scale (847 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (2293117787 / 1000000000000) (2293117788 / 1000000000000), orderedInterval (-27469324182 / 1000000000000) (-27469324181 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2468881520539511 / 4000000000000) 3 (IntervalRat.scale (847 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (24919443818 / 1000000000000) (24919461244 / 1000000000000), orderedInterval (-20279787131 / 1000000000000) (-20279769705 / 1000000000000)))) (orderedInterval (-5043189864 / 1000000000000) (-5043188424 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate552_chunkChecks3_1 :
    compactCertificate552.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3787899153884153 / 4000000000000) 3 (IntervalRat.scale (847 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-21830728825 / 1000000000000) (-21830718577 / 1000000000000), orderedInterval (14000314168 / 1000000000000) (14000324416 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2186944596157937 / 4000000000000) 3 (IntervalRat.scale (847 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (26391171870 / 1000000000000) (26391171871 / 1000000000000), orderedInterval (21607007146 / 1000000000000) (21607007147 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3880771563093733 / 4000000000000) 3 (IntervalRat.scale (847 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-5740808092 / 1000000000000) (-5740808091 / 1000000000000), orderedInterval (-24961451260 / 1000000000000) (-24961451259 / 1000000000000)))) (orderedInterval (67074578716 / 1000000000000) (67074600732 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3625920194689177 / 4000000000000) 3 (IntervalRat.scale (847 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (16142604845 / 1000000000000) (16142605093 / 1000000000000), orderedInterval (-21025922138 / 1000000000000) (-21025921891 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2587627742417641 / 4000000000000) 3 (IntervalRat.scale (847 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (15697528211 / 1000000000000) (15697528212 / 1000000000000), orderedInterval (27148236888 / 1000000000000) (27148236889 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2934094068021039 / 4000000000000) 3 (IntervalRat.scale (847 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-21618514174 / 1000000000000) (-21618509101 / 1000000000000), orderedInterval (20028047247 / 1000000000000) (20028052320 / 1000000000000)))) (orderedInterval (-12340016628 / 1000000000000) (-12340016221 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2446141739232191 / 4000000000000) 3 (IntervalRat.scale (847 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (9224305913 / 1000000000000) (9224305923 / 1000000000000), orderedInterval (-30925677184 / 1000000000000) (-30925677174 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2161240410648011 / 4000000000000) 3 (IntervalRat.scale (847 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (23179122792 / 1000000000000) (23179122793 / 1000000000000), orderedInterval (25296077497 / 1000000000000) (25296077498 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (626411709397089 / 800000000000) 3 (IntervalRat.scale (847 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-28503024897 / 1000000000000) (-28503022814 / 1000000000000), orderedInterval (-765597309 / 1000000000000) (-765595226 / 1000000000000)))) (orderedInterval (4194895571 / 1000000000000) (4194896044 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate552_chunkChecks3_2 :
    compactCertificate552.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1732687754434483 / 4000000000000) 3 (IntervalRat.scale (847 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (15536111109 / 1000000000000) (15536111110 / 1000000000000), orderedInterval (35029175906 / 1000000000000) (35029175907 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1468818598425563 / 4000000000000) 3 (IntervalRat.scale (847 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-17106078820 / 1000000000000) (-17106078819 / 1000000000000), orderedInterval (-37938203457 / 1000000000000) (-37938203456 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (919118479460489 / 4000000000000) 3 (IntervalRat.scale (847 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-49577380011 / 1000000000000) (-49577380010 / 1000000000000), orderedInterval (-17573891995 / 1000000000000) (-17573891994 / 1000000000000)))) (orderedInterval (4679497799 / 1000000000000) (4679497890 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (494304975103863 / 4000000000000) 3 (IntervalRat.scale (847 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-69217730183 / 1000000000000) (-69217728840 / 1000000000000), orderedInterval (19267030515 / 1000000000000) (19267031858 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1342134163420589 / 4000000000000) 3 (IntervalRat.scale (847 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-7289986605 / 1000000000000) (-7289986604 / 1000000000000), orderedInterval (-42933214385 / 1000000000000) (-42933214384 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1832569457571853 / 4000000000000) 3 (IntervalRat.scale (847 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (9401564887 / 1000000000000) (9401564888 / 1000000000000), orderedInterval (36061596529 / 1000000000000) (36061596530 / 1000000000000)))) (orderedInterval (3021840921 / 1000000000000) (3021840968 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (774881520539511 / 4000000000000) 3 (IntervalRat.scale (847 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-15490078668 / 1000000000000) (-15490078479 / 1000000000000), orderedInterval (55233717827 / 1000000000000) (55233718016 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3149850360857431 / 4000000000000) 3 (IntervalRat.scale (847 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (8182995603 / 1000000000000) (8182995606 / 1000000000000), orderedInterval (-27235384631 / 1000000000000) (-27235384628 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2103954064187129 / 4000000000000) 3 (IntervalRat.scale (847 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-29532884261 / 1000000000000) (-29532802374 / 1000000000000), orderedInterval (18416643327 / 1000000000000) (18416725214 / 1000000000000)))) (orderedInterval (-7649631014 / 1000000000000) (-7649601146 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate552_chunkChecks3 :
    compactCertificate552.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate552.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate552_chunkChecks3_0
    compactCertificate552_chunkChecks3_1 compactCertificate552_chunkChecks3_2

theorem compactCertificate552_chunkChecks4_0 :
    compactCertificate552.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (847 / 2) 4 (IntervalRat.scale (847 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-6563083894 / 1000000000000) (-6563083893 / 1000000000000), orderedInterval (-38204308737 / 1000000000000) (-38204308736 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1247792732872147 / 4000000000000) 4 (IntervalRat.scale (847 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-44702850381 / 1000000000000) (-44702849416 / 1000000000000), orderedInterval (6586220086 / 1000000000000) (6586221051 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (403510532291251 / 800000000000) 4 (IntervalRat.scale (847 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (20731966279 / 1000000000000) (20731968298 / 1000000000000), orderedInterval (-28870996572 / 1000000000000) (-28870994554 / 1000000000000)))) (orderedInterval (-361044389 / 1000000000000) (-361044094 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (364102807412729 / 4000000000000) 4 (IntervalRat.scale (847 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-54101100130 / 1000000000000) (-54101100129 / 1000000000000), orderedInterval (-63475355662 / 1000000000000) (-63475355661 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (978031356007013 / 4000000000000) 4 (IntervalRat.scale (847 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (12549857964 / 1000000000000) (12549857965 / 1000000000000), orderedInterval (49433251093 / 1000000000000) (49433251094 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2655545385752721 / 4000000000000) 4 (IntervalRat.scale (847 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-30188041082 / 1000000000000) (-30188025742 / 1000000000000), orderedInterval (6922817463 / 1000000000000) (6922832802 / 1000000000000)))) (orderedInterval (13004713712 / 1000000000000) (13004720502 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1956062712014873 / 4000000000000) 4 (IntervalRat.scale (847 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-10235589717 / 1000000000000) (-10235589690 / 1000000000000), orderedInterval (34609200436 / 1000000000000) (34609200463 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3351746797058429 / 4000000000000) 4 (IntervalRat.scale (847 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (2293117787 / 1000000000000) (2293117788 / 1000000000000), orderedInterval (-27469324182 / 1000000000000) (-27469324181 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2468881520539511 / 4000000000000) 4 (IntervalRat.scale (847 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (24919443818 / 1000000000000) (24919461244 / 1000000000000), orderedInterval (-20279787131 / 1000000000000) (-20279769705 / 1000000000000)))) (orderedInterval (1657046739 / 1000000000000) (1657048893 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate552_chunkChecks4_1 :
    compactCertificate552.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3787899153884153 / 4000000000000) 4 (IntervalRat.scale (847 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-21830728825 / 1000000000000) (-21830718577 / 1000000000000), orderedInterval (14000314168 / 1000000000000) (14000324416 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2186944596157937 / 4000000000000) 4 (IntervalRat.scale (847 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (26391171870 / 1000000000000) (26391171871 / 1000000000000), orderedInterval (21607007146 / 1000000000000) (21607007147 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3880771563093733 / 4000000000000) 4 (IntervalRat.scale (847 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-5740808092 / 1000000000000) (-5740808091 / 1000000000000), orderedInterval (-24961451260 / 1000000000000) (-24961451259 / 1000000000000)))) (orderedInterval (79613146078 / 1000000000000) (79613195329 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3625920194689177 / 4000000000000) 4 (IntervalRat.scale (847 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (16142604845 / 1000000000000) (16142605093 / 1000000000000), orderedInterval (-21025922138 / 1000000000000) (-21025921891 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2587627742417641 / 4000000000000) 4 (IntervalRat.scale (847 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (15697528211 / 1000000000000) (15697528212 / 1000000000000), orderedInterval (27148236888 / 1000000000000) (27148236889 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2934094068021039 / 4000000000000) 4 (IntervalRat.scale (847 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-21618514174 / 1000000000000) (-21618509101 / 1000000000000), orderedInterval (20028047247 / 1000000000000) (20028052320 / 1000000000000)))) (orderedInterval (3007548792 / 1000000000000) (3007549517 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2446141739232191 / 4000000000000) 4 (IntervalRat.scale (847 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (9224305913 / 1000000000000) (9224305923 / 1000000000000), orderedInterval (-30925677184 / 1000000000000) (-30925677174 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2161240410648011 / 4000000000000) 4 (IntervalRat.scale (847 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (23179122792 / 1000000000000) (23179122793 / 1000000000000), orderedInterval (25296077497 / 1000000000000) (25296077498 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (626411709397089 / 800000000000) 4 (IntervalRat.scale (847 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-28503024897 / 1000000000000) (-28503022814 / 1000000000000), orderedInterval (-765597309 / 1000000000000) (-765595226 / 1000000000000)))) (orderedInterval (-11599408421 / 1000000000000) (-11599407582 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate552_chunkChecks4_2 :
    compactCertificate552.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1732687754434483 / 4000000000000) 4 (IntervalRat.scale (847 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (15536111109 / 1000000000000) (15536111110 / 1000000000000), orderedInterval (35029175906 / 1000000000000) (35029175907 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1468818598425563 / 4000000000000) 4 (IntervalRat.scale (847 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-17106078820 / 1000000000000) (-17106078819 / 1000000000000), orderedInterval (-37938203457 / 1000000000000) (-37938203456 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (919118479460489 / 4000000000000) 4 (IntervalRat.scale (847 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-49577380011 / 1000000000000) (-49577380010 / 1000000000000), orderedInterval (-17573891995 / 1000000000000) (-17573891994 / 1000000000000)))) (orderedInterval (-2333639249 / 1000000000000) (-2333639159 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (494304975103863 / 4000000000000) 4 (IntervalRat.scale (847 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-69217730183 / 1000000000000) (-69217728840 / 1000000000000), orderedInterval (19267030515 / 1000000000000) (19267031858 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1342134163420589 / 4000000000000) 4 (IntervalRat.scale (847 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-7289986605 / 1000000000000) (-7289986604 / 1000000000000), orderedInterval (-42933214385 / 1000000000000) (-42933214384 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1832569457571853 / 4000000000000) 4 (IntervalRat.scale (847 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (9401564887 / 1000000000000) (9401564888 / 1000000000000), orderedInterval (36061596529 / 1000000000000) (36061596530 / 1000000000000)))) (orderedInterval (-926652391 / 1000000000000) (-926652342 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (774881520539511 / 4000000000000) 4 (IntervalRat.scale (847 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-15490078668 / 1000000000000) (-15490078479 / 1000000000000), orderedInterval (55233717827 / 1000000000000) (55233718016 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3149850360857431 / 4000000000000) 4 (IntervalRat.scale (847 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (8182995603 / 1000000000000) (8182995606 / 1000000000000), orderedInterval (-27235384631 / 1000000000000) (-27235384628 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2103954064187129 / 4000000000000) 4 (IntervalRat.scale (847 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-29532884261 / 1000000000000) (-29532802374 / 1000000000000), orderedInterval (18416643327 / 1000000000000) (18416725214 / 1000000000000)))) (orderedInterval (5254758903 / 1000000000000) (5254796206 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate552_chunkChecks4 :
    compactCertificate552.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate552.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate552_chunkChecks4_0
    compactCertificate552_chunkChecks4_1 compactCertificate552_chunkChecks4_2

theorem compactCertificate552_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate552.chunkCheck r b = true :=
  compactCertificate552.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate552_chunkChecks0
    · exact compactCertificate552_chunkChecks1
    · exact compactCertificate552_chunkChecks2
    · exact compactCertificate552_chunkChecks3
    · exact compactCertificate552_chunkChecks4)

theorem compactCertificate552_coefficient0 :
    compactCertificate552.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate552_coefficient1 :
    compactCertificate552.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate552_coefficient2 :
    compactCertificate552.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate552_coefficient3 :
    compactCertificate552.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate552_coefficient4 :
    compactCertificate552.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate552_coefficients : ∀ r : Fin 5,
    compactCertificate552.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate552_coefficient0
  · exact compactCertificate552_coefficient1
  · exact compactCertificate552_coefficient2
  · exact compactCertificate552_coefficient3
  · exact compactCertificate552_coefficient4

theorem compactCertificate552_lower : (1 : ℚ) ≤ compactCertificate552.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate552, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate552_proves {t : ℝ} (ht : t ∈ compactCertificate552.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate552.proves compactCertificate552_states compactCertificate552_chunks
    compactCertificate552_coefficients compactCertificate552_lower ht

end Erdos232
