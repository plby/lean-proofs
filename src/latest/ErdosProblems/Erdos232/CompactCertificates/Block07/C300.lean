/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate300 : CompactCertificate where
  left := 173
  right := 174
  center := 347 / 2
  grid := fun i =>
    match i.val with
    | 0 => 55
    | 1 => 41
    | 2 => 66
    | 3 => 12
    | 4 => 32
    | 5 => 87
    | 6 => 64
    | 7 => 109
    | 8 => 81
    | 9 => 124
    | 10 => 71
    | 11 => 127
    | 12 => 118
    | 13 => 84
    | 14 => 96
    | 15 => 80
    | 16 => 70
    | 17 => 102
    | 18 => 57
    | 19 => 48
    | 20 => 30
    | 21 => 16
    | 22 => 44
    | 23 => 60
    | 24 => 25
    | 25 => 103
    | _ => 69
  point := fun i =>
    match i.val with
    | 0 => 347 / 2
    | 1 => 511197258921647 / 4000000000000
    | 2 => 165310690324751 / 800000000000
    | 3 => 149166085209229 / 4000000000000
    | 4 => 400681086817513 / 4000000000000
    | 5 => 1087927094281221 / 4000000000000
    | 6 => 801362173635373 / 4000000000000
    | 7 => 1373147743304929 / 4000000000000
    | 8 => 1011454412783011 / 4000000000000
    | 9 => 1551831176384653 / 4000000000000
    | 10 => 895950147422437 / 4000000000000
    | 11 => 1589879259024233 / 4000000000000
    | 12 => 1485471437493677 / 4000000000000
    | 13 => 1060102510766141 / 4000000000000
    | 14 => 1202043260452539 / 4000000000000
    | 15 => 1002138351255691 / 4000000000000
    | 16 => 885419625141511 / 4000000000000
    | 17 => 256629118253589 / 800000000000
    | 18 => 709849646739983 / 4000000000000
    | 19 => 601747406911063 / 4000000000000
    | 20 => 376545587216989 / 4000000000000
    | 21 => 202507469139363 / 4000000000000
    | 22 => 549847172027089 / 4000000000000
    | 23 => 750769305522353 / 4000000000000
    | 24 => 317454412783011 / 4000000000000
    | 25 => 1290434563420931 / 4000000000000
    | _ => 861950484383629 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-60409940450 / 1000000000000) (-60409940432 / 1000000000000), orderedInterval (-4287103440 / 1000000000000) (-4287103422 / 1000000000000))
    | 1 => (orderedInterval (15510083704 / 1000000000000) (15510083850 / 1000000000000), orderedInterval (-68914684214 / 1000000000000) (-68914684068 / 1000000000000))
    | 2 => (orderedInterval (4327289484 / 1000000000000) (4327289485 / 1000000000000), orderedInterval (55325988069 / 1000000000000) (55325988071 / 1000000000000))
    | 3 => (orderedInterval (47788145949 / 1000000000000) (47788145950 / 1000000000000), orderedInterval (120968795327 / 1000000000000) (120968795328 / 1000000000000))
    | 4 => (orderedInterval (32758167312 / 1000000000000) (32758167313 / 1000000000000), orderedInterval (72516139546 / 1000000000000) (72516139547 / 1000000000000))
    | 5 => (orderedInterval (25364043139 / 1000000000000) (25364046511 / 1000000000000), orderedInterval (-41245388441 / 1000000000000) (-41245385069 / 1000000000000))
    | 6 => (orderedInterval (3570835607 / 1000000000000) (3570835609 / 1000000000000), orderedInterval (56248950772 / 1000000000000) (56248950773 / 1000000000000))
    | 7 => (orderedInterval (-42965402385 / 1000000000000) (-42965401930 / 1000000000000), orderedInterval (2970366236 / 1000000000000) (2970366691 / 1000000000000))
    | 8 => (orderedInterval (36703023434 / 1000000000000) (36703074297 / 1000000000000), orderedInterval (-34285561288 / 1000000000000) (-34285510426 / 1000000000000))
    | 9 => (orderedInterval (-29468597208 / 1000000000000) (-29468571187 / 1000000000000), orderedInterval (27832813284 / 1000000000000) (27832839304 / 1000000000000))
    | 10 => (orderedInterval (-52725555242 / 1000000000000) (-52725554654 / 1000000000000), orderedInterval (8005647957 / 1000000000000) (8005648546 / 1000000000000))
    | 11 => (orderedInterval (26610208257 / 1000000000000) (26610219024 / 1000000000000), orderedInterval (-29926245927 / 1000000000000) (-29926235159 / 1000000000000))
    | 12 => (orderedInterval (41076330875 / 1000000000000) (41076330913 / 1000000000000), orderedInterval (5139890911 / 1000000000000) (5139890950 / 1000000000000))
    | 13 => (orderedInterval (46107093883 / 1000000000000) (46107100750 / 1000000000000), orderedInterval (-16707420351 / 1000000000000) (-16707413484 / 1000000000000))
    | 14 => (orderedInterval (-13474129665 / 1000000000000) (-13474129540 / 1000000000000), orderedInterval (44032747293 / 1000000000000) (44032747418 / 1000000000000))
    | 15 => (orderedInterval (-399497069 / 1000000000000) (-399497066 / 1000000000000), orderedInterval (50408047790 / 1000000000000) (50408047793 / 1000000000000))
    | 16 => (orderedInterval (42449432531 / 1000000000000) (42449532280 / 1000000000000), orderedInterval (-32868684863 / 1000000000000) (-32868585113 / 1000000000000))
    | 17 => (orderedInterval (40270217567 / 1000000000000) (40270217568 / 1000000000000), orderedInterval (18986321264 / 1000000000000) (18986321265 / 1000000000000))
    | 18 => (orderedInterval (43941381821 / 1000000000000) (43941454559 / 1000000000000), orderedInterval (-40823967579 / 1000000000000) (-40823894841 / 1000000000000))
    | 19 => (orderedInterval (26820677179 / 1000000000000) (26820677180 / 1000000000000), orderedInterval (59176987245 / 1000000000000) (59176987246 / 1000000000000))
    | 20 => (orderedInterval (51240011683 / 1000000000000) (51240011684 / 1000000000000), orderedInterval (64049077219 / 1000000000000) (64049077220 / 1000000000000))
    | 21 => (orderedInterval (102090174805 / 1000000000000) (102090174806 / 1000000000000), orderedInterval (45380787228 / 1000000000000) (45380787229 / 1000000000000))
    | 22 => (orderedInterval (1102757856 / 1000000000000) (1102757860 / 1000000000000), orderedInterval (68040558161 / 1000000000000) (68040558165 / 1000000000000))
    | 23 => (orderedInterval (-1077402876 / 1000000000000) (-1077402871 / 1000000000000), orderedInterval (58232394816 / 1000000000000) (58232394820 / 1000000000000))
    | 24 => (orderedInterval (-89501581267 / 1000000000000) (-89501581218 / 1000000000000), orderedInterval (3860295467 / 1000000000000) (3860295516 / 1000000000000))
    | 25 => (orderedInterval (8406650533 / 1000000000000) (8406650555 / 1000000000000), orderedInterval (-43632754750 / 1000000000000) (-43632754728 / 1000000000000))
    | _ => (orderedInterval (25936970440 / 1000000000000) (25936972980 / 1000000000000), orderedInterval (-47826275598 / 1000000000000) (-47826273058 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-23545931459 / 1000000000000) (-23545931438 / 1000000000000)
      | 1 => orderedInterval (-1125530589 / 1000000000000) (-1125530328 / 1000000000000)
      | 2 => orderedInterval (2212264556 / 1000000000000) (2212265810 / 1000000000000)
      | 3 => orderedInterval (5112477388 / 1000000000000) (5112483655 / 1000000000000)
      | 4 => orderedInterval (3686651252 / 1000000000000) (3686651924 / 1000000000000)
      | 5 => orderedInterval (-1402782305 / 1000000000000) (-1402776579 / 1000000000000)
      | 6 => orderedInterval (-6875823178 / 1000000000000) (-6875811504 / 1000000000000)
      | 7 => orderedInterval (-1827554210 / 1000000000000) (-1827554188 / 1000000000000)
      | _ => orderedInterval (-6090325368 / 1000000000000) (-6090324840 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (1694425196 / 1000000000000) (1694425219 / 1000000000000)
      | 1 => orderedInterval (5843000898 / 1000000000000) (5843001298 / 1000000000000)
      | 2 => orderedInterval (-1388920330 / 1000000000000) (-1388918493 / 1000000000000)
      | 3 => orderedInterval (-20038746654 / 1000000000000) (-20038732610 / 1000000000000)
      | 4 => orderedInterval (-2997908379 / 1000000000000) (-2997907350 / 1000000000000)
      | 5 => orderedInterval (4139118084 / 1000000000000) (4139125391 / 1000000000000)
      | 6 => orderedInterval (4903663036 / 1000000000000) (4903674973 / 1000000000000)
      | 7 => orderedInterval (-6295438462 / 1000000000000) (-6295438442 / 1000000000000)
      | _ => orderedInterval (17759978857 / 1000000000000) (17759979520 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (23496009923 / 1000000000000) (23496009947 / 1000000000000)
      | 1 => orderedInterval (4022626575 / 1000000000000) (4022627199 / 1000000000000)
      | 2 => orderedInterval (-7064215096 / 1000000000000) (-7064212389 / 1000000000000)
      | 3 => orderedInterval (-39407530691 / 1000000000000) (-39407499081 / 1000000000000)
      | 4 => orderedInterval (-6963213056 / 1000000000000) (-6963211473 / 1000000000000)
      | 5 => orderedInterval (415167979 / 1000000000000) (415177349 / 1000000000000)
      | 6 => orderedInterval (7972426917 / 1000000000000) (7972439192 / 1000000000000)
      | 7 => orderedInterval (115866119 / 1000000000000) (115866139 / 1000000000000)
      | _ => orderedInterval (9883379749 / 1000000000000) (9883380594 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-3664286643 / 1000000000000) (-3664286616 / 1000000000000)
      | 1 => orderedInterval (-11814935427 / 1000000000000) (-11814934451 / 1000000000000)
      | 2 => orderedInterval (3315483437 / 1000000000000) (3315487422 / 1000000000000)
      | 3 => orderedInterval (105391461865 / 1000000000000) (105391532904 / 1000000000000)
      | 4 => orderedInterval (7738976347 / 1000000000000) (7738978776 / 1000000000000)
      | 5 => orderedInterval (-8733616470 / 1000000000000) (-8733604506 / 1000000000000)
      | 6 => orderedInterval (-5180396243 / 1000000000000) (-5180383690 / 1000000000000)
      | 7 => orderedInterval (6437722914 / 1000000000000) (6437722935 / 1000000000000)
      | _ => orderedInterval (-40084406885 / 1000000000000) (-40084405802 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-23347891287 / 1000000000000) (-23347891257 / 1000000000000)
      | 1 => orderedInterval (-10620837228 / 1000000000000) (-10620835694 / 1000000000000)
      | 2 => orderedInterval (24274176982 / 1000000000000) (24274182890 / 1000000000000)
      | 3 => orderedInterval (223028956698 / 1000000000000) (223029116861 / 1000000000000)
      | 4 => orderedInterval (8696644593 / 1000000000000) (8696648340 / 1000000000000)
      | 5 => orderedInterval (5693582978 / 1000000000000) (5693598326 / 1000000000000)
      | 6 => orderedInterval (-8343553862 / 1000000000000) (-8343540953 / 1000000000000)
      | 7 => orderedInterval (15358118 / 1000000000000) (15358139 / 1000000000000)
      | _ => orderedInterval (-19321313613 / 1000000000000) (-19321312200 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-29856553913 / 1000000000000) (-29856527488 / 1000000000000)
    | 1 => orderedInterval (3619172246 / 1000000000000) (3619209506 / 1000000000000)
    | 2 => orderedInterval (-7529481581 / 1000000000000) (-7529422523 / 1000000000000)
    | 3 => orderedInterval (53406002895 / 1000000000000) (53406106972 / 1000000000000)
    | _ => orderedInterval (200075123379 / 1000000000000) (200075324452 / 1000000000000)

theorem compactCertificate300_stateChecks0 :
    compactCertificate300.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (347 / 2)) (orderedInterval (-60409940450 / 1000000000000) (-60409940432 / 1000000000000), orderedInterval (-4287103440 / 1000000000000) (-4287103422 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 41 12 (511197258921647 / 4000000000000)) (orderedInterval (15510083704 / 1000000000000) (15510083850 / 1000000000000), orderedInterval (-68914684214 / 1000000000000) (-68914684068 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (165310690324751 / 800000000000)) (orderedInterval (4327289484 / 1000000000000) (4327289485 / 1000000000000), orderedInterval (55325988069 / 1000000000000) (55325988071 / 1000000000000))) = true
  rfl'

theorem compactCertificate300_stateChecks1 :
    compactCertificate300.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 12 12 (149166085209229 / 4000000000000)) (orderedInterval (47788145949 / 1000000000000) (47788145950 / 1000000000000), orderedInterval (120968795327 / 1000000000000) (120968795328 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (400681086817513 / 4000000000000)) (orderedInterval (32758167312 / 1000000000000) (32758167313 / 1000000000000), orderedInterval (72516139546 / 1000000000000) (72516139547 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 87 12 (1087927094281221 / 4000000000000)) (orderedInterval (25364043139 / 1000000000000) (25364046511 / 1000000000000), orderedInterval (-41245388441 / 1000000000000) (-41245385069 / 1000000000000))) = true
  rfl'

theorem compactCertificate300_stateChecks2 :
    compactCertificate300.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (801362173635373 / 4000000000000)) (orderedInterval (3570835607 / 1000000000000) (3570835609 / 1000000000000), orderedInterval (56248950772 / 1000000000000) (56248950773 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 109 12 (1373147743304929 / 4000000000000)) (orderedInterval (-42965402385 / 1000000000000) (-42965401930 / 1000000000000), orderedInterval (2970366236 / 1000000000000) (2970366691 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 81 12 (1011454412783011 / 4000000000000)) (orderedInterval (36703023434 / 1000000000000) (36703074297 / 1000000000000), orderedInterval (-34285561288 / 1000000000000) (-34285510426 / 1000000000000))) = true
  rfl'

theorem compactCertificate300_stateChecks3 :
    compactCertificate300.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 124 12 (1551831176384653 / 4000000000000)) (orderedInterval (-29468597208 / 1000000000000) (-29468571187 / 1000000000000), orderedInterval (27832813284 / 1000000000000) (27832839304 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (895950147422437 / 4000000000000)) (orderedInterval (-52725555242 / 1000000000000) (-52725554654 / 1000000000000), orderedInterval (8005647957 / 1000000000000) (8005648546 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 127 12 (1589879259024233 / 4000000000000)) (orderedInterval (26610208257 / 1000000000000) (26610219024 / 1000000000000), orderedInterval (-29926245927 / 1000000000000) (-29926235159 / 1000000000000))) = true
  rfl'

theorem compactCertificate300_stateChecks4 :
    compactCertificate300.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 118 12 (1485471437493677 / 4000000000000)) (orderedInterval (41076330875 / 1000000000000) (41076330913 / 1000000000000), orderedInterval (5139890911 / 1000000000000) (5139890950 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 84 12 (1060102510766141 / 4000000000000)) (orderedInterval (46107093883 / 1000000000000) (46107100750 / 1000000000000), orderedInterval (-16707420351 / 1000000000000) (-16707413484 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 96 12 (1202043260452539 / 4000000000000)) (orderedInterval (-13474129665 / 1000000000000) (-13474129540 / 1000000000000), orderedInterval (44032747293 / 1000000000000) (44032747418 / 1000000000000))) = true
  rfl'

theorem compactCertificate300_stateChecks5 :
    compactCertificate300.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 80 12 (1002138351255691 / 4000000000000)) (orderedInterval (-399497069 / 1000000000000) (-399497066 / 1000000000000), orderedInterval (50408047790 / 1000000000000) (50408047793 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (885419625141511 / 4000000000000)) (orderedInterval (42449432531 / 1000000000000) (42449532280 / 1000000000000), orderedInterval (-32868684863 / 1000000000000) (-32868585113 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 102 12 (256629118253589 / 800000000000)) (orderedInterval (40270217567 / 1000000000000) (40270217568 / 1000000000000), orderedInterval (18986321264 / 1000000000000) (18986321265 / 1000000000000))) = true
  rfl'

theorem compactCertificate300_stateChecks6 :
    compactCertificate300.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 57 12 (709849646739983 / 4000000000000)) (orderedInterval (43941381821 / 1000000000000) (43941454559 / 1000000000000), orderedInterval (-40823967579 / 1000000000000) (-40823894841 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 48 12 (601747406911063 / 4000000000000)) (orderedInterval (26820677179 / 1000000000000) (26820677180 / 1000000000000), orderedInterval (59176987245 / 1000000000000) (59176987246 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (376545587216989 / 4000000000000)) (orderedInterval (51240011683 / 1000000000000) (51240011684 / 1000000000000), orderedInterval (64049077219 / 1000000000000) (64049077220 / 1000000000000))) = true
  rfl'

theorem compactCertificate300_stateChecks7 :
    compactCertificate300.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 16 12 (202507469139363 / 4000000000000)) (orderedInterval (102090174805 / 1000000000000) (102090174806 / 1000000000000), orderedInterval (45380787228 / 1000000000000) (45380787229 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 44 12 (549847172027089 / 4000000000000)) (orderedInterval (1102757856 / 1000000000000) (1102757860 / 1000000000000), orderedInterval (68040558161 / 1000000000000) (68040558165 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 60 12 (750769305522353 / 4000000000000)) (orderedInterval (-1077402876 / 1000000000000) (-1077402871 / 1000000000000), orderedInterval (58232394816 / 1000000000000) (58232394820 / 1000000000000))) = true
  rfl'

theorem compactCertificate300_stateChecks8 :
    compactCertificate300.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 25 12 (317454412783011 / 4000000000000)) (orderedInterval (-89501581267 / 1000000000000) (-89501581218 / 1000000000000), orderedInterval (3860295467 / 1000000000000) (3860295516 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 103 12 (1290434563420931 / 4000000000000)) (orderedInterval (8406650533 / 1000000000000) (8406650555 / 1000000000000), orderedInterval (-43632754750 / 1000000000000) (-43632754728 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (861950484383629 / 4000000000000)) (orderedInterval (25936970440 / 1000000000000) (25936972980 / 1000000000000), orderedInterval (-47826275598 / 1000000000000) (-47826273058 / 1000000000000))) = true
  rfl'

theorem compactCertificate300_states : ∀ j,
    BesselStateValid (compactCertificate300.point j) (compactCertificate300.state j) :=
  compactCertificate300.statesValid_of_checks3 compactCertificate300_stateChecks0
    compactCertificate300_stateChecks1 compactCertificate300_stateChecks2
    compactCertificate300_stateChecks3 compactCertificate300_stateChecks4
    compactCertificate300_stateChecks5 compactCertificate300_stateChecks6
    compactCertificate300_stateChecks7 compactCertificate300_stateChecks8

theorem compactCertificate300_chunkChecks0_0 :
    compactCertificate300.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (347 / 2) 0 (IntervalRat.scale (347 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-60409940450 / 1000000000000) (-60409940432 / 1000000000000), orderedInterval (-4287103440 / 1000000000000) (-4287103422 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (511197258921647 / 4000000000000) 0 (IntervalRat.scale (347 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (15510083704 / 1000000000000) (15510083850 / 1000000000000), orderedInterval (-68914684214 / 1000000000000) (-68914684068 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (165310690324751 / 800000000000) 0 (IntervalRat.scale (347 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (4327289484 / 1000000000000) (4327289485 / 1000000000000), orderedInterval (55325988069 / 1000000000000) (55325988071 / 1000000000000)))) (orderedInterval (-23545931459 / 1000000000000) (-23545931438 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (149166085209229 / 4000000000000) 0 (IntervalRat.scale (347 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (47788145949 / 1000000000000) (47788145950 / 1000000000000), orderedInterval (120968795327 / 1000000000000) (120968795328 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (400681086817513 / 4000000000000) 0 (IntervalRat.scale (347 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (32758167312 / 1000000000000) (32758167313 / 1000000000000), orderedInterval (72516139546 / 1000000000000) (72516139547 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1087927094281221 / 4000000000000) 0 (IntervalRat.scale (347 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (25364043139 / 1000000000000) (25364046511 / 1000000000000), orderedInterval (-41245388441 / 1000000000000) (-41245385069 / 1000000000000)))) (orderedInterval (-1125530589 / 1000000000000) (-1125530328 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (801362173635373 / 4000000000000) 0 (IntervalRat.scale (347 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (3570835607 / 1000000000000) (3570835609 / 1000000000000), orderedInterval (56248950772 / 1000000000000) (56248950773 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1373147743304929 / 4000000000000) 0 (IntervalRat.scale (347 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-42965402385 / 1000000000000) (-42965401930 / 1000000000000), orderedInterval (2970366236 / 1000000000000) (2970366691 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1011454412783011 / 4000000000000) 0 (IntervalRat.scale (347 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (36703023434 / 1000000000000) (36703074297 / 1000000000000), orderedInterval (-34285561288 / 1000000000000) (-34285510426 / 1000000000000)))) (orderedInterval (2212264556 / 1000000000000) (2212265810 / 1000000000000))) = true
  rfl'

theorem compactCertificate300_chunkChecks0_1 :
    compactCertificate300.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1551831176384653 / 4000000000000) 0 (IntervalRat.scale (347 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-29468597208 / 1000000000000) (-29468571187 / 1000000000000), orderedInterval (27832813284 / 1000000000000) (27832839304 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (895950147422437 / 4000000000000) 0 (IntervalRat.scale (347 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-52725555242 / 1000000000000) (-52725554654 / 1000000000000), orderedInterval (8005647957 / 1000000000000) (8005648546 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1589879259024233 / 4000000000000) 0 (IntervalRat.scale (347 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (26610208257 / 1000000000000) (26610219024 / 1000000000000), orderedInterval (-29926245927 / 1000000000000) (-29926235159 / 1000000000000)))) (orderedInterval (5112477388 / 1000000000000) (5112483655 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1485471437493677 / 4000000000000) 0 (IntervalRat.scale (347 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (41076330875 / 1000000000000) (41076330913 / 1000000000000), orderedInterval (5139890911 / 1000000000000) (5139890950 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1060102510766141 / 4000000000000) 0 (IntervalRat.scale (347 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (46107093883 / 1000000000000) (46107100750 / 1000000000000), orderedInterval (-16707420351 / 1000000000000) (-16707413484 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1202043260452539 / 4000000000000) 0 (IntervalRat.scale (347 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-13474129665 / 1000000000000) (-13474129540 / 1000000000000), orderedInterval (44032747293 / 1000000000000) (44032747418 / 1000000000000)))) (orderedInterval (3686651252 / 1000000000000) (3686651924 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1002138351255691 / 4000000000000) 0 (IntervalRat.scale (347 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-399497069 / 1000000000000) (-399497066 / 1000000000000), orderedInterval (50408047790 / 1000000000000) (50408047793 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (885419625141511 / 4000000000000) 0 (IntervalRat.scale (347 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (42449432531 / 1000000000000) (42449532280 / 1000000000000), orderedInterval (-32868684863 / 1000000000000) (-32868585113 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (256629118253589 / 800000000000) 0 (IntervalRat.scale (347 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (40270217567 / 1000000000000) (40270217568 / 1000000000000), orderedInterval (18986321264 / 1000000000000) (18986321265 / 1000000000000)))) (orderedInterval (-1402782305 / 1000000000000) (-1402776579 / 1000000000000))) = true
  rfl'

theorem compactCertificate300_chunkChecks0_2 :
    compactCertificate300.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (709849646739983 / 4000000000000) 0 (IntervalRat.scale (347 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (43941381821 / 1000000000000) (43941454559 / 1000000000000), orderedInterval (-40823967579 / 1000000000000) (-40823894841 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (601747406911063 / 4000000000000) 0 (IntervalRat.scale (347 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (26820677179 / 1000000000000) (26820677180 / 1000000000000), orderedInterval (59176987245 / 1000000000000) (59176987246 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (376545587216989 / 4000000000000) 0 (IntervalRat.scale (347 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (51240011683 / 1000000000000) (51240011684 / 1000000000000), orderedInterval (64049077219 / 1000000000000) (64049077220 / 1000000000000)))) (orderedInterval (-6875823178 / 1000000000000) (-6875811504 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (202507469139363 / 4000000000000) 0 (IntervalRat.scale (347 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (102090174805 / 1000000000000) (102090174806 / 1000000000000), orderedInterval (45380787228 / 1000000000000) (45380787229 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (549847172027089 / 4000000000000) 0 (IntervalRat.scale (347 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (1102757856 / 1000000000000) (1102757860 / 1000000000000), orderedInterval (68040558161 / 1000000000000) (68040558165 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (750769305522353 / 4000000000000) 0 (IntervalRat.scale (347 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-1077402876 / 1000000000000) (-1077402871 / 1000000000000), orderedInterval (58232394816 / 1000000000000) (58232394820 / 1000000000000)))) (orderedInterval (-1827554210 / 1000000000000) (-1827554188 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (317454412783011 / 4000000000000) 0 (IntervalRat.scale (347 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-89501581267 / 1000000000000) (-89501581218 / 1000000000000), orderedInterval (3860295467 / 1000000000000) (3860295516 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1290434563420931 / 4000000000000) 0 (IntervalRat.scale (347 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (8406650533 / 1000000000000) (8406650555 / 1000000000000), orderedInterval (-43632754750 / 1000000000000) (-43632754728 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (861950484383629 / 4000000000000) 0 (IntervalRat.scale (347 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (25936970440 / 1000000000000) (25936972980 / 1000000000000), orderedInterval (-47826275598 / 1000000000000) (-47826273058 / 1000000000000)))) (orderedInterval (-6090325368 / 1000000000000) (-6090324840 / 1000000000000))) = true
  rfl'

theorem compactCertificate300_chunkChecks0 :
    compactCertificate300.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate300.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate300_chunkChecks0_0
    compactCertificate300_chunkChecks0_1 compactCertificate300_chunkChecks0_2

theorem compactCertificate300_chunkChecks1_0 :
    compactCertificate300.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (347 / 2) 1 (IntervalRat.scale (347 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-60409940450 / 1000000000000) (-60409940432 / 1000000000000), orderedInterval (-4287103440 / 1000000000000) (-4287103422 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (511197258921647 / 4000000000000) 1 (IntervalRat.scale (347 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (15510083704 / 1000000000000) (15510083850 / 1000000000000), orderedInterval (-68914684214 / 1000000000000) (-68914684068 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (165310690324751 / 800000000000) 1 (IntervalRat.scale (347 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (4327289484 / 1000000000000) (4327289485 / 1000000000000), orderedInterval (55325988069 / 1000000000000) (55325988071 / 1000000000000)))) (orderedInterval (1694425196 / 1000000000000) (1694425219 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (149166085209229 / 4000000000000) 1 (IntervalRat.scale (347 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (47788145949 / 1000000000000) (47788145950 / 1000000000000), orderedInterval (120968795327 / 1000000000000) (120968795328 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (400681086817513 / 4000000000000) 1 (IntervalRat.scale (347 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (32758167312 / 1000000000000) (32758167313 / 1000000000000), orderedInterval (72516139546 / 1000000000000) (72516139547 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1087927094281221 / 4000000000000) 1 (IntervalRat.scale (347 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (25364043139 / 1000000000000) (25364046511 / 1000000000000), orderedInterval (-41245388441 / 1000000000000) (-41245385069 / 1000000000000)))) (orderedInterval (5843000898 / 1000000000000) (5843001298 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (801362173635373 / 4000000000000) 1 (IntervalRat.scale (347 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (3570835607 / 1000000000000) (3570835609 / 1000000000000), orderedInterval (56248950772 / 1000000000000) (56248950773 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1373147743304929 / 4000000000000) 1 (IntervalRat.scale (347 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-42965402385 / 1000000000000) (-42965401930 / 1000000000000), orderedInterval (2970366236 / 1000000000000) (2970366691 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1011454412783011 / 4000000000000) 1 (IntervalRat.scale (347 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (36703023434 / 1000000000000) (36703074297 / 1000000000000), orderedInterval (-34285561288 / 1000000000000) (-34285510426 / 1000000000000)))) (orderedInterval (-1388920330 / 1000000000000) (-1388918493 / 1000000000000))) = true
  rfl'

theorem compactCertificate300_chunkChecks1_1 :
    compactCertificate300.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1551831176384653 / 4000000000000) 1 (IntervalRat.scale (347 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-29468597208 / 1000000000000) (-29468571187 / 1000000000000), orderedInterval (27832813284 / 1000000000000) (27832839304 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (895950147422437 / 4000000000000) 1 (IntervalRat.scale (347 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-52725555242 / 1000000000000) (-52725554654 / 1000000000000), orderedInterval (8005647957 / 1000000000000) (8005648546 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1589879259024233 / 4000000000000) 1 (IntervalRat.scale (347 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (26610208257 / 1000000000000) (26610219024 / 1000000000000), orderedInterval (-29926245927 / 1000000000000) (-29926235159 / 1000000000000)))) (orderedInterval (-20038746654 / 1000000000000) (-20038732610 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1485471437493677 / 4000000000000) 1 (IntervalRat.scale (347 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (41076330875 / 1000000000000) (41076330913 / 1000000000000), orderedInterval (5139890911 / 1000000000000) (5139890950 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1060102510766141 / 4000000000000) 1 (IntervalRat.scale (347 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (46107093883 / 1000000000000) (46107100750 / 1000000000000), orderedInterval (-16707420351 / 1000000000000) (-16707413484 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1202043260452539 / 4000000000000) 1 (IntervalRat.scale (347 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-13474129665 / 1000000000000) (-13474129540 / 1000000000000), orderedInterval (44032747293 / 1000000000000) (44032747418 / 1000000000000)))) (orderedInterval (-2997908379 / 1000000000000) (-2997907350 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1002138351255691 / 4000000000000) 1 (IntervalRat.scale (347 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-399497069 / 1000000000000) (-399497066 / 1000000000000), orderedInterval (50408047790 / 1000000000000) (50408047793 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (885419625141511 / 4000000000000) 1 (IntervalRat.scale (347 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (42449432531 / 1000000000000) (42449532280 / 1000000000000), orderedInterval (-32868684863 / 1000000000000) (-32868585113 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (256629118253589 / 800000000000) 1 (IntervalRat.scale (347 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (40270217567 / 1000000000000) (40270217568 / 1000000000000), orderedInterval (18986321264 / 1000000000000) (18986321265 / 1000000000000)))) (orderedInterval (4139118084 / 1000000000000) (4139125391 / 1000000000000))) = true
  rfl'

theorem compactCertificate300_chunkChecks1_2 :
    compactCertificate300.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (709849646739983 / 4000000000000) 1 (IntervalRat.scale (347 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (43941381821 / 1000000000000) (43941454559 / 1000000000000), orderedInterval (-40823967579 / 1000000000000) (-40823894841 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (601747406911063 / 4000000000000) 1 (IntervalRat.scale (347 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (26820677179 / 1000000000000) (26820677180 / 1000000000000), orderedInterval (59176987245 / 1000000000000) (59176987246 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (376545587216989 / 4000000000000) 1 (IntervalRat.scale (347 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (51240011683 / 1000000000000) (51240011684 / 1000000000000), orderedInterval (64049077219 / 1000000000000) (64049077220 / 1000000000000)))) (orderedInterval (4903663036 / 1000000000000) (4903674973 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (202507469139363 / 4000000000000) 1 (IntervalRat.scale (347 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (102090174805 / 1000000000000) (102090174806 / 1000000000000), orderedInterval (45380787228 / 1000000000000) (45380787229 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (549847172027089 / 4000000000000) 1 (IntervalRat.scale (347 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (1102757856 / 1000000000000) (1102757860 / 1000000000000), orderedInterval (68040558161 / 1000000000000) (68040558165 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (750769305522353 / 4000000000000) 1 (IntervalRat.scale (347 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-1077402876 / 1000000000000) (-1077402871 / 1000000000000), orderedInterval (58232394816 / 1000000000000) (58232394820 / 1000000000000)))) (orderedInterval (-6295438462 / 1000000000000) (-6295438442 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (317454412783011 / 4000000000000) 1 (IntervalRat.scale (347 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-89501581267 / 1000000000000) (-89501581218 / 1000000000000), orderedInterval (3860295467 / 1000000000000) (3860295516 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1290434563420931 / 4000000000000) 1 (IntervalRat.scale (347 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (8406650533 / 1000000000000) (8406650555 / 1000000000000), orderedInterval (-43632754750 / 1000000000000) (-43632754728 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (861950484383629 / 4000000000000) 1 (IntervalRat.scale (347 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (25936970440 / 1000000000000) (25936972980 / 1000000000000), orderedInterval (-47826275598 / 1000000000000) (-47826273058 / 1000000000000)))) (orderedInterval (17759978857 / 1000000000000) (17759979520 / 1000000000000))) = true
  rfl'

theorem compactCertificate300_chunkChecks1 :
    compactCertificate300.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate300.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate300_chunkChecks1_0
    compactCertificate300_chunkChecks1_1 compactCertificate300_chunkChecks1_2

theorem compactCertificate300_chunkChecks2_0 :
    compactCertificate300.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (347 / 2) 2 (IntervalRat.scale (347 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-60409940450 / 1000000000000) (-60409940432 / 1000000000000), orderedInterval (-4287103440 / 1000000000000) (-4287103422 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (511197258921647 / 4000000000000) 2 (IntervalRat.scale (347 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (15510083704 / 1000000000000) (15510083850 / 1000000000000), orderedInterval (-68914684214 / 1000000000000) (-68914684068 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (165310690324751 / 800000000000) 2 (IntervalRat.scale (347 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (4327289484 / 1000000000000) (4327289485 / 1000000000000), orderedInterval (55325988069 / 1000000000000) (55325988071 / 1000000000000)))) (orderedInterval (23496009923 / 1000000000000) (23496009947 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (149166085209229 / 4000000000000) 2 (IntervalRat.scale (347 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (47788145949 / 1000000000000) (47788145950 / 1000000000000), orderedInterval (120968795327 / 1000000000000) (120968795328 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (400681086817513 / 4000000000000) 2 (IntervalRat.scale (347 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (32758167312 / 1000000000000) (32758167313 / 1000000000000), orderedInterval (72516139546 / 1000000000000) (72516139547 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1087927094281221 / 4000000000000) 2 (IntervalRat.scale (347 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (25364043139 / 1000000000000) (25364046511 / 1000000000000), orderedInterval (-41245388441 / 1000000000000) (-41245385069 / 1000000000000)))) (orderedInterval (4022626575 / 1000000000000) (4022627199 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (801362173635373 / 4000000000000) 2 (IntervalRat.scale (347 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (3570835607 / 1000000000000) (3570835609 / 1000000000000), orderedInterval (56248950772 / 1000000000000) (56248950773 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1373147743304929 / 4000000000000) 2 (IntervalRat.scale (347 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-42965402385 / 1000000000000) (-42965401930 / 1000000000000), orderedInterval (2970366236 / 1000000000000) (2970366691 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1011454412783011 / 4000000000000) 2 (IntervalRat.scale (347 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (36703023434 / 1000000000000) (36703074297 / 1000000000000), orderedInterval (-34285561288 / 1000000000000) (-34285510426 / 1000000000000)))) (orderedInterval (-7064215096 / 1000000000000) (-7064212389 / 1000000000000))) = true
  rfl'

theorem compactCertificate300_chunkChecks2_1 :
    compactCertificate300.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1551831176384653 / 4000000000000) 2 (IntervalRat.scale (347 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-29468597208 / 1000000000000) (-29468571187 / 1000000000000), orderedInterval (27832813284 / 1000000000000) (27832839304 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (895950147422437 / 4000000000000) 2 (IntervalRat.scale (347 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-52725555242 / 1000000000000) (-52725554654 / 1000000000000), orderedInterval (8005647957 / 1000000000000) (8005648546 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1589879259024233 / 4000000000000) 2 (IntervalRat.scale (347 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (26610208257 / 1000000000000) (26610219024 / 1000000000000), orderedInterval (-29926245927 / 1000000000000) (-29926235159 / 1000000000000)))) (orderedInterval (-39407530691 / 1000000000000) (-39407499081 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1485471437493677 / 4000000000000) 2 (IntervalRat.scale (347 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (41076330875 / 1000000000000) (41076330913 / 1000000000000), orderedInterval (5139890911 / 1000000000000) (5139890950 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1060102510766141 / 4000000000000) 2 (IntervalRat.scale (347 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (46107093883 / 1000000000000) (46107100750 / 1000000000000), orderedInterval (-16707420351 / 1000000000000) (-16707413484 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1202043260452539 / 4000000000000) 2 (IntervalRat.scale (347 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-13474129665 / 1000000000000) (-13474129540 / 1000000000000), orderedInterval (44032747293 / 1000000000000) (44032747418 / 1000000000000)))) (orderedInterval (-6963213056 / 1000000000000) (-6963211473 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1002138351255691 / 4000000000000) 2 (IntervalRat.scale (347 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-399497069 / 1000000000000) (-399497066 / 1000000000000), orderedInterval (50408047790 / 1000000000000) (50408047793 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (885419625141511 / 4000000000000) 2 (IntervalRat.scale (347 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (42449432531 / 1000000000000) (42449532280 / 1000000000000), orderedInterval (-32868684863 / 1000000000000) (-32868585113 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (256629118253589 / 800000000000) 2 (IntervalRat.scale (347 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (40270217567 / 1000000000000) (40270217568 / 1000000000000), orderedInterval (18986321264 / 1000000000000) (18986321265 / 1000000000000)))) (orderedInterval (415167979 / 1000000000000) (415177349 / 1000000000000))) = true
  rfl'

theorem compactCertificate300_chunkChecks2_2 :
    compactCertificate300.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (709849646739983 / 4000000000000) 2 (IntervalRat.scale (347 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (43941381821 / 1000000000000) (43941454559 / 1000000000000), orderedInterval (-40823967579 / 1000000000000) (-40823894841 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (601747406911063 / 4000000000000) 2 (IntervalRat.scale (347 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (26820677179 / 1000000000000) (26820677180 / 1000000000000), orderedInterval (59176987245 / 1000000000000) (59176987246 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (376545587216989 / 4000000000000) 2 (IntervalRat.scale (347 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (51240011683 / 1000000000000) (51240011684 / 1000000000000), orderedInterval (64049077219 / 1000000000000) (64049077220 / 1000000000000)))) (orderedInterval (7972426917 / 1000000000000) (7972439192 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (202507469139363 / 4000000000000) 2 (IntervalRat.scale (347 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (102090174805 / 1000000000000) (102090174806 / 1000000000000), orderedInterval (45380787228 / 1000000000000) (45380787229 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (549847172027089 / 4000000000000) 2 (IntervalRat.scale (347 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (1102757856 / 1000000000000) (1102757860 / 1000000000000), orderedInterval (68040558161 / 1000000000000) (68040558165 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (750769305522353 / 4000000000000) 2 (IntervalRat.scale (347 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-1077402876 / 1000000000000) (-1077402871 / 1000000000000), orderedInterval (58232394816 / 1000000000000) (58232394820 / 1000000000000)))) (orderedInterval (115866119 / 1000000000000) (115866139 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (317454412783011 / 4000000000000) 2 (IntervalRat.scale (347 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-89501581267 / 1000000000000) (-89501581218 / 1000000000000), orderedInterval (3860295467 / 1000000000000) (3860295516 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1290434563420931 / 4000000000000) 2 (IntervalRat.scale (347 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (8406650533 / 1000000000000) (8406650555 / 1000000000000), orderedInterval (-43632754750 / 1000000000000) (-43632754728 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (861950484383629 / 4000000000000) 2 (IntervalRat.scale (347 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (25936970440 / 1000000000000) (25936972980 / 1000000000000), orderedInterval (-47826275598 / 1000000000000) (-47826273058 / 1000000000000)))) (orderedInterval (9883379749 / 1000000000000) (9883380594 / 1000000000000))) = true
  rfl'

theorem compactCertificate300_chunkChecks2 :
    compactCertificate300.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate300.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate300_chunkChecks2_0
    compactCertificate300_chunkChecks2_1 compactCertificate300_chunkChecks2_2

theorem compactCertificate300_chunkChecks3_0 :
    compactCertificate300.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (347 / 2) 3 (IntervalRat.scale (347 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-60409940450 / 1000000000000) (-60409940432 / 1000000000000), orderedInterval (-4287103440 / 1000000000000) (-4287103422 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (511197258921647 / 4000000000000) 3 (IntervalRat.scale (347 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (15510083704 / 1000000000000) (15510083850 / 1000000000000), orderedInterval (-68914684214 / 1000000000000) (-68914684068 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (165310690324751 / 800000000000) 3 (IntervalRat.scale (347 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (4327289484 / 1000000000000) (4327289485 / 1000000000000), orderedInterval (55325988069 / 1000000000000) (55325988071 / 1000000000000)))) (orderedInterval (-3664286643 / 1000000000000) (-3664286616 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (149166085209229 / 4000000000000) 3 (IntervalRat.scale (347 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (47788145949 / 1000000000000) (47788145950 / 1000000000000), orderedInterval (120968795327 / 1000000000000) (120968795328 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (400681086817513 / 4000000000000) 3 (IntervalRat.scale (347 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (32758167312 / 1000000000000) (32758167313 / 1000000000000), orderedInterval (72516139546 / 1000000000000) (72516139547 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1087927094281221 / 4000000000000) 3 (IntervalRat.scale (347 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (25364043139 / 1000000000000) (25364046511 / 1000000000000), orderedInterval (-41245388441 / 1000000000000) (-41245385069 / 1000000000000)))) (orderedInterval (-11814935427 / 1000000000000) (-11814934451 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (801362173635373 / 4000000000000) 3 (IntervalRat.scale (347 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (3570835607 / 1000000000000) (3570835609 / 1000000000000), orderedInterval (56248950772 / 1000000000000) (56248950773 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1373147743304929 / 4000000000000) 3 (IntervalRat.scale (347 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-42965402385 / 1000000000000) (-42965401930 / 1000000000000), orderedInterval (2970366236 / 1000000000000) (2970366691 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1011454412783011 / 4000000000000) 3 (IntervalRat.scale (347 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (36703023434 / 1000000000000) (36703074297 / 1000000000000), orderedInterval (-34285561288 / 1000000000000) (-34285510426 / 1000000000000)))) (orderedInterval (3315483437 / 1000000000000) (3315487422 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate300_chunkChecks3_1 :
    compactCertificate300.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1551831176384653 / 4000000000000) 3 (IntervalRat.scale (347 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-29468597208 / 1000000000000) (-29468571187 / 1000000000000), orderedInterval (27832813284 / 1000000000000) (27832839304 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (895950147422437 / 4000000000000) 3 (IntervalRat.scale (347 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-52725555242 / 1000000000000) (-52725554654 / 1000000000000), orderedInterval (8005647957 / 1000000000000) (8005648546 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1589879259024233 / 4000000000000) 3 (IntervalRat.scale (347 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (26610208257 / 1000000000000) (26610219024 / 1000000000000), orderedInterval (-29926245927 / 1000000000000) (-29926235159 / 1000000000000)))) (orderedInterval (105391461865 / 1000000000000) (105391532904 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1485471437493677 / 4000000000000) 3 (IntervalRat.scale (347 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (41076330875 / 1000000000000) (41076330913 / 1000000000000), orderedInterval (5139890911 / 1000000000000) (5139890950 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1060102510766141 / 4000000000000) 3 (IntervalRat.scale (347 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (46107093883 / 1000000000000) (46107100750 / 1000000000000), orderedInterval (-16707420351 / 1000000000000) (-16707413484 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1202043260452539 / 4000000000000) 3 (IntervalRat.scale (347 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-13474129665 / 1000000000000) (-13474129540 / 1000000000000), orderedInterval (44032747293 / 1000000000000) (44032747418 / 1000000000000)))) (orderedInterval (7738976347 / 1000000000000) (7738978776 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1002138351255691 / 4000000000000) 3 (IntervalRat.scale (347 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-399497069 / 1000000000000) (-399497066 / 1000000000000), orderedInterval (50408047790 / 1000000000000) (50408047793 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (885419625141511 / 4000000000000) 3 (IntervalRat.scale (347 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (42449432531 / 1000000000000) (42449532280 / 1000000000000), orderedInterval (-32868684863 / 1000000000000) (-32868585113 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (256629118253589 / 800000000000) 3 (IntervalRat.scale (347 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (40270217567 / 1000000000000) (40270217568 / 1000000000000), orderedInterval (18986321264 / 1000000000000) (18986321265 / 1000000000000)))) (orderedInterval (-8733616470 / 1000000000000) (-8733604506 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate300_chunkChecks3_2 :
    compactCertificate300.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (709849646739983 / 4000000000000) 3 (IntervalRat.scale (347 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (43941381821 / 1000000000000) (43941454559 / 1000000000000), orderedInterval (-40823967579 / 1000000000000) (-40823894841 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (601747406911063 / 4000000000000) 3 (IntervalRat.scale (347 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (26820677179 / 1000000000000) (26820677180 / 1000000000000), orderedInterval (59176987245 / 1000000000000) (59176987246 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (376545587216989 / 4000000000000) 3 (IntervalRat.scale (347 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (51240011683 / 1000000000000) (51240011684 / 1000000000000), orderedInterval (64049077219 / 1000000000000) (64049077220 / 1000000000000)))) (orderedInterval (-5180396243 / 1000000000000) (-5180383690 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (202507469139363 / 4000000000000) 3 (IntervalRat.scale (347 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (102090174805 / 1000000000000) (102090174806 / 1000000000000), orderedInterval (45380787228 / 1000000000000) (45380787229 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (549847172027089 / 4000000000000) 3 (IntervalRat.scale (347 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (1102757856 / 1000000000000) (1102757860 / 1000000000000), orderedInterval (68040558161 / 1000000000000) (68040558165 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (750769305522353 / 4000000000000) 3 (IntervalRat.scale (347 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-1077402876 / 1000000000000) (-1077402871 / 1000000000000), orderedInterval (58232394816 / 1000000000000) (58232394820 / 1000000000000)))) (orderedInterval (6437722914 / 1000000000000) (6437722935 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (317454412783011 / 4000000000000) 3 (IntervalRat.scale (347 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-89501581267 / 1000000000000) (-89501581218 / 1000000000000), orderedInterval (3860295467 / 1000000000000) (3860295516 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1290434563420931 / 4000000000000) 3 (IntervalRat.scale (347 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (8406650533 / 1000000000000) (8406650555 / 1000000000000), orderedInterval (-43632754750 / 1000000000000) (-43632754728 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (861950484383629 / 4000000000000) 3 (IntervalRat.scale (347 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (25936970440 / 1000000000000) (25936972980 / 1000000000000), orderedInterval (-47826275598 / 1000000000000) (-47826273058 / 1000000000000)))) (orderedInterval (-40084406885 / 1000000000000) (-40084405802 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate300_chunkChecks3 :
    compactCertificate300.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate300.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate300_chunkChecks3_0
    compactCertificate300_chunkChecks3_1 compactCertificate300_chunkChecks3_2

theorem compactCertificate300_chunkChecks4_0 :
    compactCertificate300.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (347 / 2) 4 (IntervalRat.scale (347 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-60409940450 / 1000000000000) (-60409940432 / 1000000000000), orderedInterval (-4287103440 / 1000000000000) (-4287103422 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (511197258921647 / 4000000000000) 4 (IntervalRat.scale (347 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (15510083704 / 1000000000000) (15510083850 / 1000000000000), orderedInterval (-68914684214 / 1000000000000) (-68914684068 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (165310690324751 / 800000000000) 4 (IntervalRat.scale (347 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (4327289484 / 1000000000000) (4327289485 / 1000000000000), orderedInterval (55325988069 / 1000000000000) (55325988071 / 1000000000000)))) (orderedInterval (-23347891287 / 1000000000000) (-23347891257 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (149166085209229 / 4000000000000) 4 (IntervalRat.scale (347 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (47788145949 / 1000000000000) (47788145950 / 1000000000000), orderedInterval (120968795327 / 1000000000000) (120968795328 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (400681086817513 / 4000000000000) 4 (IntervalRat.scale (347 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (32758167312 / 1000000000000) (32758167313 / 1000000000000), orderedInterval (72516139546 / 1000000000000) (72516139547 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1087927094281221 / 4000000000000) 4 (IntervalRat.scale (347 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (25364043139 / 1000000000000) (25364046511 / 1000000000000), orderedInterval (-41245388441 / 1000000000000) (-41245385069 / 1000000000000)))) (orderedInterval (-10620837228 / 1000000000000) (-10620835694 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (801362173635373 / 4000000000000) 4 (IntervalRat.scale (347 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (3570835607 / 1000000000000) (3570835609 / 1000000000000), orderedInterval (56248950772 / 1000000000000) (56248950773 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1373147743304929 / 4000000000000) 4 (IntervalRat.scale (347 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-42965402385 / 1000000000000) (-42965401930 / 1000000000000), orderedInterval (2970366236 / 1000000000000) (2970366691 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1011454412783011 / 4000000000000) 4 (IntervalRat.scale (347 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (36703023434 / 1000000000000) (36703074297 / 1000000000000), orderedInterval (-34285561288 / 1000000000000) (-34285510426 / 1000000000000)))) (orderedInterval (24274176982 / 1000000000000) (24274182890 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate300_chunkChecks4_1 :
    compactCertificate300.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1551831176384653 / 4000000000000) 4 (IntervalRat.scale (347 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-29468597208 / 1000000000000) (-29468571187 / 1000000000000), orderedInterval (27832813284 / 1000000000000) (27832839304 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (895950147422437 / 4000000000000) 4 (IntervalRat.scale (347 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-52725555242 / 1000000000000) (-52725554654 / 1000000000000), orderedInterval (8005647957 / 1000000000000) (8005648546 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1589879259024233 / 4000000000000) 4 (IntervalRat.scale (347 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (26610208257 / 1000000000000) (26610219024 / 1000000000000), orderedInterval (-29926245927 / 1000000000000) (-29926235159 / 1000000000000)))) (orderedInterval (223028956698 / 1000000000000) (223029116861 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1485471437493677 / 4000000000000) 4 (IntervalRat.scale (347 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (41076330875 / 1000000000000) (41076330913 / 1000000000000), orderedInterval (5139890911 / 1000000000000) (5139890950 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1060102510766141 / 4000000000000) 4 (IntervalRat.scale (347 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (46107093883 / 1000000000000) (46107100750 / 1000000000000), orderedInterval (-16707420351 / 1000000000000) (-16707413484 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1202043260452539 / 4000000000000) 4 (IntervalRat.scale (347 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-13474129665 / 1000000000000) (-13474129540 / 1000000000000), orderedInterval (44032747293 / 1000000000000) (44032747418 / 1000000000000)))) (orderedInterval (8696644593 / 1000000000000) (8696648340 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1002138351255691 / 4000000000000) 4 (IntervalRat.scale (347 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-399497069 / 1000000000000) (-399497066 / 1000000000000), orderedInterval (50408047790 / 1000000000000) (50408047793 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (885419625141511 / 4000000000000) 4 (IntervalRat.scale (347 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (42449432531 / 1000000000000) (42449532280 / 1000000000000), orderedInterval (-32868684863 / 1000000000000) (-32868585113 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (256629118253589 / 800000000000) 4 (IntervalRat.scale (347 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (40270217567 / 1000000000000) (40270217568 / 1000000000000), orderedInterval (18986321264 / 1000000000000) (18986321265 / 1000000000000)))) (orderedInterval (5693582978 / 1000000000000) (5693598326 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate300_chunkChecks4_2 :
    compactCertificate300.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (709849646739983 / 4000000000000) 4 (IntervalRat.scale (347 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (43941381821 / 1000000000000) (43941454559 / 1000000000000), orderedInterval (-40823967579 / 1000000000000) (-40823894841 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (601747406911063 / 4000000000000) 4 (IntervalRat.scale (347 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (26820677179 / 1000000000000) (26820677180 / 1000000000000), orderedInterval (59176987245 / 1000000000000) (59176987246 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (376545587216989 / 4000000000000) 4 (IntervalRat.scale (347 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (51240011683 / 1000000000000) (51240011684 / 1000000000000), orderedInterval (64049077219 / 1000000000000) (64049077220 / 1000000000000)))) (orderedInterval (-8343553862 / 1000000000000) (-8343540953 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (202507469139363 / 4000000000000) 4 (IntervalRat.scale (347 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (102090174805 / 1000000000000) (102090174806 / 1000000000000), orderedInterval (45380787228 / 1000000000000) (45380787229 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (549847172027089 / 4000000000000) 4 (IntervalRat.scale (347 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (1102757856 / 1000000000000) (1102757860 / 1000000000000), orderedInterval (68040558161 / 1000000000000) (68040558165 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (750769305522353 / 4000000000000) 4 (IntervalRat.scale (347 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-1077402876 / 1000000000000) (-1077402871 / 1000000000000), orderedInterval (58232394816 / 1000000000000) (58232394820 / 1000000000000)))) (orderedInterval (15358118 / 1000000000000) (15358139 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (317454412783011 / 4000000000000) 4 (IntervalRat.scale (347 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-89501581267 / 1000000000000) (-89501581218 / 1000000000000), orderedInterval (3860295467 / 1000000000000) (3860295516 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1290434563420931 / 4000000000000) 4 (IntervalRat.scale (347 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (8406650533 / 1000000000000) (8406650555 / 1000000000000), orderedInterval (-43632754750 / 1000000000000) (-43632754728 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (861950484383629 / 4000000000000) 4 (IntervalRat.scale (347 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (25936970440 / 1000000000000) (25936972980 / 1000000000000), orderedInterval (-47826275598 / 1000000000000) (-47826273058 / 1000000000000)))) (orderedInterval (-19321313613 / 1000000000000) (-19321312200 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate300_chunkChecks4 :
    compactCertificate300.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate300.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate300_chunkChecks4_0
    compactCertificate300_chunkChecks4_1 compactCertificate300_chunkChecks4_2

theorem compactCertificate300_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate300.chunkCheck r b = true :=
  compactCertificate300.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate300_chunkChecks0
    · exact compactCertificate300_chunkChecks1
    · exact compactCertificate300_chunkChecks2
    · exact compactCertificate300_chunkChecks3
    · exact compactCertificate300_chunkChecks4)

theorem compactCertificate300_coefficient0 :
    compactCertificate300.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate300_coefficient1 :
    compactCertificate300.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate300_coefficient2 :
    compactCertificate300.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate300_coefficient3 :
    compactCertificate300.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate300_coefficient4 :
    compactCertificate300.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate300_coefficients : ∀ r : Fin 5,
    compactCertificate300.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate300_coefficient0
  · exact compactCertificate300_coefficient1
  · exact compactCertificate300_coefficient2
  · exact compactCertificate300_coefficient3
  · exact compactCertificate300_coefficient4

theorem compactCertificate300_lower : (1 : ℚ) ≤ compactCertificate300.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate300, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate300_proves {t : ℝ} (ht : t ∈ compactCertificate300.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate300.proves compactCertificate300_states compactCertificate300_chunks
    compactCertificate300_coefficients compactCertificate300_lower ht

end Erdos232
