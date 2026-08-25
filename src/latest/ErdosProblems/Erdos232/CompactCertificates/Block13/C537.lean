/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate537 : CompactCertificate where
  left := 408
  right := 409
  center := 817 / 2
  grid := fun i =>
    match i.val with
    | 0 => 130
    | 1 => 96
    | 2 => 155
    | 3 => 28
    | 4 => 75
    | 5 => 204
    | 6 => 150
    | 7 => 257
    | 8 => 190
    | 9 => 291
    | 10 => 168
    | 11 => 298
    | 12 => 278
    | 13 => 199
    | 14 => 225
    | 15 => 188
    | 16 => 166
    | 17 => 241
    | 18 => 133
    | 19 => 113
    | 20 => 71
    | 21 => 38
    | 22 => 103
    | 23 => 141
    | 24 => 60
    | 25 => 242
    | _ => 162
  point := fun i =>
    match i.val with
    | 0 => 817 / 2
    | 1 => 1203597004435117 / 4000000000000
    | 2 => 389218541773261 / 800000000000
    | 3 => 351206604080519 / 4000000000000
    | 4 => 943390339855643 / 4000000000000
    | 5 => 2561488288264431 / 4000000000000
    | 6 => 1886780679712103 / 4000000000000
    | 7 => 3233030853833219 / 4000000000000
    | 8 => 2381435894074121 / 4000000000000
    | 9 => 3653735075234183 / 4000000000000
    | 10 => 2109484929233807 / 4000000000000
    | 11 => 3743318024849563 / 4000000000000
    | 12 => 3497493269257447 / 4000000000000
    | 13 => 2495976228518551 / 4000000000000
    | 14 => 2830171019566929 / 4000000000000
    | 15 => 2359501535953601 / 4000000000000
    | 16 => 2084691163517621 / 4000000000000
    | 17 => 604224753928479 / 800000000000
    | 18 => 1671317467972813 / 4000000000000
    | 19 => 1416794326934693 / 4000000000000
    | 20 => 886564105925879 / 4000000000000
    | 21 => 476797124745993 / 4000000000000
    | 22 => 1294596943936979 / 4000000000000
    | 23 => 1767661448448883 / 4000000000000
    | 24 => 747435894074121 / 4000000000000
    | 25 => 3038285413011241 / 4000000000000
    | _ => 2029433849398919 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (30377263210 / 1000000000000) (30377263211 / 1000000000000), orderedInterval (25175006112 / 1000000000000) (25175006113 / 1000000000000))
    | 1 => (orderedInterval (4195482697 / 1000000000000) (4195482698 / 1000000000000), orderedInterval (45798320875 / 1000000000000) (45798320876 / 1000000000000))
    | 2 => (orderedInterval (-12792240455 / 1000000000000) (-12792240454 / 1000000000000), orderedInterval (-33822747454 / 1000000000000) (-33822747453 / 1000000000000))
    | 3 => (orderedInterval (49546652072 / 1000000000000) (49546652073 / 1000000000000), orderedInterval (68969757349 / 1000000000000) (68969757350 / 1000000000000))
    | 4 => (orderedInterval (-44079607399 / 1000000000000) (-44079607398 / 1000000000000), orderedInterval (-27406918749 / 1000000000000) (-27406918748 / 1000000000000))
    | 5 => (orderedInterval (8482146402 / 1000000000000) (8482146403 / 1000000000000), orderedInterval (30361022621 / 1000000000000) (30361022622 / 1000000000000))
    | 6 => (orderedInterval (34762440790 / 1000000000000) (34762440794 / 1000000000000), orderedInterval (11846520229 / 1000000000000) (11846520233 / 1000000000000))
    | 7 => (orderedInterval (-27968744026 / 1000000000000) (-27968736256 / 1000000000000), orderedInterval (2339787482 / 1000000000000) (2339795253 / 1000000000000))
    | 8 => (orderedInterval (-22490933415 / 1000000000000) (-22490928094 / 1000000000000), orderedInterval (23756242865 / 1000000000000) (23756248186 / 1000000000000))
    | 9 => (orderedInterval (-410974482 / 1000000000000) (-410974481 / 1000000000000), orderedInterval (-26396432237 / 1000000000000) (-26396432236 / 1000000000000))
    | 10 => (orderedInterval (12526037744 / 1000000000000) (12526037745 / 1000000000000), orderedInterval (32395771118 / 1000000000000) (32395771119 / 1000000000000))
    | 11 => (orderedInterval (10639038190 / 1000000000000) (10639038191 / 1000000000000), orderedInterval (23807844928 / 1000000000000) (23807844929 / 1000000000000))
    | 12 => (orderedInterval (26302818266 / 1000000000000) (26302859709 / 1000000000000), orderedInterval (-6035646465 / 1000000000000) (-6035605022 / 1000000000000))
    | 13 => (orderedInterval (12370251219 / 1000000000000) (12370251270 / 1000000000000), orderedInterval (-29458355666 / 1000000000000) (-29458355615 / 1000000000000))
    | 14 => (orderedInterval (-29842652063 / 1000000000000) (-29842651509 / 1000000000000), orderedInterval (-3008345808 / 1000000000000) (-3008345254 / 1000000000000))
    | 15 => (orderedInterval (1351517093 / 1000000000000) (1351517094 / 1000000000000), orderedInterval (32822905075 / 1000000000000) (32822905076 / 1000000000000))
    | 16 => (orderedInterval (15314325219 / 1000000000000) (15314325220 / 1000000000000), orderedInterval (31401635125 / 1000000000000) (31401635126 / 1000000000000))
    | 17 => (orderedInterval (25293354212 / 1000000000000) (25293397834 / 1000000000000), orderedInterval (-14269357035 / 1000000000000) (-14269313413 / 1000000000000))
    | 18 => (orderedInterval (-27524890568 / 1000000000000) (-27524890567 / 1000000000000), orderedInterval (-27644059446 / 1000000000000) (-27644059445 / 1000000000000))
    | 19 => (orderedInterval (692827848 / 1000000000000) (692827850 / 1000000000000), orderedInterval (-42390534113 / 1000000000000) (-42390534111 / 1000000000000))
    | 20 => (orderedInterval (31453883673 / 1000000000000) (31453893302 / 1000000000000), orderedInterval (-43464005469 / 1000000000000) (-43463995839 / 1000000000000))
    | 21 => (orderedInterval (41451713353 / 1000000000000) (41451713354 / 1000000000000), orderedInterval (60013952724 / 1000000000000) (60013952725 / 1000000000000))
    | 22 => (orderedInterval (-33325956035 / 1000000000000) (-33325956034 / 1000000000000), orderedInterval (-29212583536 / 1000000000000) (-29212583535 / 1000000000000))
    | 23 => (orderedInterval (9907340721 / 1000000000000) (9907340748 / 1000000000000), orderedInterval (-36650498290 / 1000000000000) (-36650498263 / 1000000000000))
    | 24 => (orderedInterval (-43922974142 / 1000000000000) (-43922885368 / 1000000000000), orderedInterval (38558705744 / 1000000000000) (38558794518 / 1000000000000))
    | 25 => (orderedInterval (2635606719 / 1000000000000) (2635606720 / 1000000000000), orderedInterval (28828528058 / 1000000000000) (28828528059 / 1000000000000))
    | _ => (orderedInterval (-25272037250 / 1000000000000) (-25272025205 / 1000000000000), orderedInterval (24846211975 / 1000000000000) (24846224020 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (11328914212 / 1000000000000) (11328914241 / 1000000000000)
      | 1 => orderedInterval (-2749962243 / 1000000000000) (-2749962193 / 1000000000000)
      | 2 => orderedInterval (319106231 / 1000000000000) (319106623 / 1000000000000)
      | 3 => orderedInterval (2513503406 / 1000000000000) (2513503569 / 1000000000000)
      | 4 => orderedInterval (845939602 / 1000000000000) (845940406 / 1000000000000)
      | 5 => orderedInterval (-213171313 / 1000000000000) (-213170156 / 1000000000000)
      | 6 => orderedInterval (5385797598 / 1000000000000) (5385798015 / 1000000000000)
      | 7 => orderedInterval (-768636796 / 1000000000000) (-768636744 / 1000000000000)
      | _ => orderedInterval (4262377097 / 1000000000000) (4262380006 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (7928989860 / 1000000000000) (7928989893 / 1000000000000)
      | 1 => orderedInterval (-4122046555 / 1000000000000) (-4122046499 / 1000000000000)
      | 2 => orderedInterval (693976576 / 1000000000000) (693977278 / 1000000000000)
      | 3 => orderedInterval (21339967090 / 1000000000000) (21339967426 / 1000000000000)
      | 4 => orderedInterval (-3995581222 / 1000000000000) (-3995579529 / 1000000000000)
      | 5 => orderedInterval (-2420850351 / 1000000000000) (-2420848229 / 1000000000000)
      | 6 => orderedInterval (5833657125 / 1000000000000) (5833657391 / 1000000000000)
      | 7 => orderedInterval (3240339397 / 1000000000000) (3240339444 / 1000000000000)
      | _ => orderedInterval (-10047138060 / 1000000000000) (-10047134849 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-11016304816 / 1000000000000) (-11016304778 / 1000000000000)
      | 1 => orderedInterval (2053209280 / 1000000000000) (2053209358 / 1000000000000)
      | 2 => orderedInterval (-2224342917 / 1000000000000) (-2224341633 / 1000000000000)
      | 3 => orderedInterval (-9901529222 / 1000000000000) (-9901528501 / 1000000000000)
      | 4 => orderedInterval (-997215325 / 1000000000000) (-997211743 / 1000000000000)
      | 5 => orderedInterval (-813947753 / 1000000000000) (-813943845 / 1000000000000)
      | 6 => orderedInterval (-4890586263 / 1000000000000) (-4890586079 / 1000000000000)
      | 7 => orderedInterval (471232988 / 1000000000000) (471233035 / 1000000000000)
      | _ => orderedInterval (-6492660071 / 1000000000000) (-6492656230 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-6768966024 / 1000000000000) (-6768965981 / 1000000000000)
      | 1 => orderedInterval (8509603430 / 1000000000000) (8509603546 / 1000000000000)
      | 2 => orderedInterval (-1212916656 / 1000000000000) (-1212914269 / 1000000000000)
      | 3 => orderedInterval (-98270681730 / 1000000000000) (-98270680150 / 1000000000000)
      | 4 => orderedInterval (8783517425 / 1000000000000) (8783525024 / 1000000000000)
      | 5 => orderedInterval (4901741766 / 1000000000000) (4901748965 / 1000000000000)
      | 6 => orderedInterval (-6055912924 / 1000000000000) (-6055912785 / 1000000000000)
      | 7 => orderedInterval (-3859273355 / 1000000000000) (-3859273307 / 1000000000000)
      | _ => orderedInterval (24011466167 / 1000000000000) (24011470919 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (10574670008 / 1000000000000) (10574670059 / 1000000000000)
      | 1 => orderedInterval (-3863064297 / 1000000000000) (-3863064119 / 1000000000000)
      | 2 => orderedInterval (10774815818 / 1000000000000) (10774820321 / 1000000000000)
      | 3 => orderedInterval (46541489838 / 1000000000000) (46541493346 / 1000000000000)
      | 4 => orderedInterval (-2282306110 / 1000000000000) (-2282289934 / 1000000000000)
      | 5 => orderedInterval (5289857985 / 1000000000000) (5289871277 / 1000000000000)
      | 6 => orderedInterval (4913246997 / 1000000000000) (4913247112 / 1000000000000)
      | 7 => orderedInterval (-728646683 / 1000000000000) (-728646633 / 1000000000000)
      | _ => orderedInterval (8589232092 / 1000000000000) (8589238096 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (20923867794 / 1000000000000) (20923873767 / 1000000000000)
    | 1 => orderedInterval (18451313860 / 1000000000000) (18451322326 / 1000000000000)
    | 2 => orderedInterval (-33812144099 / 1000000000000) (-33812130416 / 1000000000000)
    | 3 => orderedInterval (-69961421901 / 1000000000000) (-69961398038 / 1000000000000)
    | _ => orderedInterval (79809295648 / 1000000000000) (79809339525 / 1000000000000)

theorem compactCertificate537_stateChecks0 :
    compactCertificate537.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 130 12 (817 / 2)) (orderedInterval (30377263210 / 1000000000000) (30377263211 / 1000000000000), orderedInterval (25175006112 / 1000000000000) (25175006113 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 96 12 (1203597004435117 / 4000000000000)) (orderedInterval (4195482697 / 1000000000000) (4195482698 / 1000000000000), orderedInterval (45798320875 / 1000000000000) (45798320876 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 155 12 (389218541773261 / 800000000000)) (orderedInterval (-12792240455 / 1000000000000) (-12792240454 / 1000000000000), orderedInterval (-33822747454 / 1000000000000) (-33822747453 / 1000000000000))) = true
  rfl'

theorem compactCertificate537_stateChecks1 :
    compactCertificate537.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 28 12 (351206604080519 / 4000000000000)) (orderedInterval (49546652072 / 1000000000000) (49546652073 / 1000000000000), orderedInterval (68969757349 / 1000000000000) (68969757350 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 75 12 (943390339855643 / 4000000000000)) (orderedInterval (-44079607399 / 1000000000000) (-44079607398 / 1000000000000), orderedInterval (-27406918749 / 1000000000000) (-27406918748 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 204 12 (2561488288264431 / 4000000000000)) (orderedInterval (8482146402 / 1000000000000) (8482146403 / 1000000000000), orderedInterval (30361022621 / 1000000000000) (30361022622 / 1000000000000))) = true
  rfl'

theorem compactCertificate537_stateChecks2 :
    compactCertificate537.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 150 12 (1886780679712103 / 4000000000000)) (orderedInterval (34762440790 / 1000000000000) (34762440794 / 1000000000000), orderedInterval (11846520229 / 1000000000000) (11846520233 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 257 12 (3233030853833219 / 4000000000000)) (orderedInterval (-27968744026 / 1000000000000) (-27968736256 / 1000000000000), orderedInterval (2339787482 / 1000000000000) (2339795253 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 190 12 (2381435894074121 / 4000000000000)) (orderedInterval (-22490933415 / 1000000000000) (-22490928094 / 1000000000000), orderedInterval (23756242865 / 1000000000000) (23756248186 / 1000000000000))) = true
  rfl'

theorem compactCertificate537_stateChecks3 :
    compactCertificate537.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 291 12 (3653735075234183 / 4000000000000)) (orderedInterval (-410974482 / 1000000000000) (-410974481 / 1000000000000), orderedInterval (-26396432237 / 1000000000000) (-26396432236 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 168 12 (2109484929233807 / 4000000000000)) (orderedInterval (12526037744 / 1000000000000) (12526037745 / 1000000000000), orderedInterval (32395771118 / 1000000000000) (32395771119 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 298 12 (3743318024849563 / 4000000000000)) (orderedInterval (10639038190 / 1000000000000) (10639038191 / 1000000000000), orderedInterval (23807844928 / 1000000000000) (23807844929 / 1000000000000))) = true
  rfl'

theorem compactCertificate537_stateChecks4 :
    compactCertificate537.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 278 12 (3497493269257447 / 4000000000000)) (orderedInterval (26302818266 / 1000000000000) (26302859709 / 1000000000000), orderedInterval (-6035646465 / 1000000000000) (-6035605022 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 199 12 (2495976228518551 / 4000000000000)) (orderedInterval (12370251219 / 1000000000000) (12370251270 / 1000000000000), orderedInterval (-29458355666 / 1000000000000) (-29458355615 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 225 12 (2830171019566929 / 4000000000000)) (orderedInterval (-29842652063 / 1000000000000) (-29842651509 / 1000000000000), orderedInterval (-3008345808 / 1000000000000) (-3008345254 / 1000000000000))) = true
  rfl'

theorem compactCertificate537_stateChecks5 :
    compactCertificate537.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 188 12 (2359501535953601 / 4000000000000)) (orderedInterval (1351517093 / 1000000000000) (1351517094 / 1000000000000), orderedInterval (32822905075 / 1000000000000) (32822905076 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 166 12 (2084691163517621 / 4000000000000)) (orderedInterval (15314325219 / 1000000000000) (15314325220 / 1000000000000), orderedInterval (31401635125 / 1000000000000) (31401635126 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 241 12 (604224753928479 / 800000000000)) (orderedInterval (25293354212 / 1000000000000) (25293397834 / 1000000000000), orderedInterval (-14269357035 / 1000000000000) (-14269313413 / 1000000000000))) = true
  rfl'

theorem compactCertificate537_stateChecks6 :
    compactCertificate537.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 133 12 (1671317467972813 / 4000000000000)) (orderedInterval (-27524890568 / 1000000000000) (-27524890567 / 1000000000000), orderedInterval (-27644059446 / 1000000000000) (-27644059445 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 113 12 (1416794326934693 / 4000000000000)) (orderedInterval (692827848 / 1000000000000) (692827850 / 1000000000000), orderedInterval (-42390534113 / 1000000000000) (-42390534111 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (886564105925879 / 4000000000000)) (orderedInterval (31453883673 / 1000000000000) (31453893302 / 1000000000000), orderedInterval (-43464005469 / 1000000000000) (-43463995839 / 1000000000000))) = true
  rfl'

theorem compactCertificate537_stateChecks7 :
    compactCertificate537.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (476797124745993 / 4000000000000)) (orderedInterval (41451713353 / 1000000000000) (41451713354 / 1000000000000), orderedInterval (60013952724 / 1000000000000) (60013952725 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 103 12 (1294596943936979 / 4000000000000)) (orderedInterval (-33325956035 / 1000000000000) (-33325956034 / 1000000000000), orderedInterval (-29212583536 / 1000000000000) (-29212583535 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 141 12 (1767661448448883 / 4000000000000)) (orderedInterval (9907340721 / 1000000000000) (9907340748 / 1000000000000), orderedInterval (-36650498290 / 1000000000000) (-36650498263 / 1000000000000))) = true
  rfl'

theorem compactCertificate537_stateChecks8 :
    compactCertificate537.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 60 12 (747435894074121 / 4000000000000)) (orderedInterval (-43922974142 / 1000000000000) (-43922885368 / 1000000000000), orderedInterval (38558705744 / 1000000000000) (38558794518 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 242 12 (3038285413011241 / 4000000000000)) (orderedInterval (2635606719 / 1000000000000) (2635606720 / 1000000000000), orderedInterval (28828528058 / 1000000000000) (28828528059 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 162 12 (2029433849398919 / 4000000000000)) (orderedInterval (-25272037250 / 1000000000000) (-25272025205 / 1000000000000), orderedInterval (24846211975 / 1000000000000) (24846224020 / 1000000000000))) = true
  rfl'

theorem compactCertificate537_states : ∀ j,
    BesselStateValid (compactCertificate537.point j) (compactCertificate537.state j) :=
  compactCertificate537.statesValid_of_checks3 compactCertificate537_stateChecks0
    compactCertificate537_stateChecks1 compactCertificate537_stateChecks2
    compactCertificate537_stateChecks3 compactCertificate537_stateChecks4
    compactCertificate537_stateChecks5 compactCertificate537_stateChecks6
    compactCertificate537_stateChecks7 compactCertificate537_stateChecks8

theorem compactCertificate537_chunkChecks0_0 :
    compactCertificate537.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (817 / 2) 0 (IntervalRat.scale (817 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (30377263210 / 1000000000000) (30377263211 / 1000000000000), orderedInterval (25175006112 / 1000000000000) (25175006113 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1203597004435117 / 4000000000000) 0 (IntervalRat.scale (817 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (4195482697 / 1000000000000) (4195482698 / 1000000000000), orderedInterval (45798320875 / 1000000000000) (45798320876 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (389218541773261 / 800000000000) 0 (IntervalRat.scale (817 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-12792240455 / 1000000000000) (-12792240454 / 1000000000000), orderedInterval (-33822747454 / 1000000000000) (-33822747453 / 1000000000000)))) (orderedInterval (11328914212 / 1000000000000) (11328914241 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (351206604080519 / 4000000000000) 0 (IntervalRat.scale (817 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (49546652072 / 1000000000000) (49546652073 / 1000000000000), orderedInterval (68969757349 / 1000000000000) (68969757350 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (943390339855643 / 4000000000000) 0 (IntervalRat.scale (817 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-44079607399 / 1000000000000) (-44079607398 / 1000000000000), orderedInterval (-27406918749 / 1000000000000) (-27406918748 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2561488288264431 / 4000000000000) 0 (IntervalRat.scale (817 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (8482146402 / 1000000000000) (8482146403 / 1000000000000), orderedInterval (30361022621 / 1000000000000) (30361022622 / 1000000000000)))) (orderedInterval (-2749962243 / 1000000000000) (-2749962193 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1886780679712103 / 4000000000000) 0 (IntervalRat.scale (817 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (34762440790 / 1000000000000) (34762440794 / 1000000000000), orderedInterval (11846520229 / 1000000000000) (11846520233 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3233030853833219 / 4000000000000) 0 (IntervalRat.scale (817 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-27968744026 / 1000000000000) (-27968736256 / 1000000000000), orderedInterval (2339787482 / 1000000000000) (2339795253 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2381435894074121 / 4000000000000) 0 (IntervalRat.scale (817 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-22490933415 / 1000000000000) (-22490928094 / 1000000000000), orderedInterval (23756242865 / 1000000000000) (23756248186 / 1000000000000)))) (orderedInterval (319106231 / 1000000000000) (319106623 / 1000000000000))) = true
  rfl'

theorem compactCertificate537_chunkChecks0_1 :
    compactCertificate537.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3653735075234183 / 4000000000000) 0 (IntervalRat.scale (817 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-410974482 / 1000000000000) (-410974481 / 1000000000000), orderedInterval (-26396432237 / 1000000000000) (-26396432236 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2109484929233807 / 4000000000000) 0 (IntervalRat.scale (817 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (12526037744 / 1000000000000) (12526037745 / 1000000000000), orderedInterval (32395771118 / 1000000000000) (32395771119 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3743318024849563 / 4000000000000) 0 (IntervalRat.scale (817 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (10639038190 / 1000000000000) (10639038191 / 1000000000000), orderedInterval (23807844928 / 1000000000000) (23807844929 / 1000000000000)))) (orderedInterval (2513503406 / 1000000000000) (2513503569 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3497493269257447 / 4000000000000) 0 (IntervalRat.scale (817 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (26302818266 / 1000000000000) (26302859709 / 1000000000000), orderedInterval (-6035646465 / 1000000000000) (-6035605022 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2495976228518551 / 4000000000000) 0 (IntervalRat.scale (817 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (12370251219 / 1000000000000) (12370251270 / 1000000000000), orderedInterval (-29458355666 / 1000000000000) (-29458355615 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2830171019566929 / 4000000000000) 0 (IntervalRat.scale (817 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-29842652063 / 1000000000000) (-29842651509 / 1000000000000), orderedInterval (-3008345808 / 1000000000000) (-3008345254 / 1000000000000)))) (orderedInterval (845939602 / 1000000000000) (845940406 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2359501535953601 / 4000000000000) 0 (IntervalRat.scale (817 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (1351517093 / 1000000000000) (1351517094 / 1000000000000), orderedInterval (32822905075 / 1000000000000) (32822905076 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2084691163517621 / 4000000000000) 0 (IntervalRat.scale (817 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (15314325219 / 1000000000000) (15314325220 / 1000000000000), orderedInterval (31401635125 / 1000000000000) (31401635126 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (604224753928479 / 800000000000) 0 (IntervalRat.scale (817 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (25293354212 / 1000000000000) (25293397834 / 1000000000000), orderedInterval (-14269357035 / 1000000000000) (-14269313413 / 1000000000000)))) (orderedInterval (-213171313 / 1000000000000) (-213170156 / 1000000000000))) = true
  rfl'

theorem compactCertificate537_chunkChecks0_2 :
    compactCertificate537.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1671317467972813 / 4000000000000) 0 (IntervalRat.scale (817 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-27524890568 / 1000000000000) (-27524890567 / 1000000000000), orderedInterval (-27644059446 / 1000000000000) (-27644059445 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1416794326934693 / 4000000000000) 0 (IntervalRat.scale (817 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (692827848 / 1000000000000) (692827850 / 1000000000000), orderedInterval (-42390534113 / 1000000000000) (-42390534111 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (886564105925879 / 4000000000000) 0 (IntervalRat.scale (817 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (31453883673 / 1000000000000) (31453893302 / 1000000000000), orderedInterval (-43464005469 / 1000000000000) (-43463995839 / 1000000000000)))) (orderedInterval (5385797598 / 1000000000000) (5385798015 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (476797124745993 / 4000000000000) 0 (IntervalRat.scale (817 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (41451713353 / 1000000000000) (41451713354 / 1000000000000), orderedInterval (60013952724 / 1000000000000) (60013952725 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1294596943936979 / 4000000000000) 0 (IntervalRat.scale (817 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-33325956035 / 1000000000000) (-33325956034 / 1000000000000), orderedInterval (-29212583536 / 1000000000000) (-29212583535 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1767661448448883 / 4000000000000) 0 (IntervalRat.scale (817 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (9907340721 / 1000000000000) (9907340748 / 1000000000000), orderedInterval (-36650498290 / 1000000000000) (-36650498263 / 1000000000000)))) (orderedInterval (-768636796 / 1000000000000) (-768636744 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (747435894074121 / 4000000000000) 0 (IntervalRat.scale (817 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-43922974142 / 1000000000000) (-43922885368 / 1000000000000), orderedInterval (38558705744 / 1000000000000) (38558794518 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3038285413011241 / 4000000000000) 0 (IntervalRat.scale (817 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (2635606719 / 1000000000000) (2635606720 / 1000000000000), orderedInterval (28828528058 / 1000000000000) (28828528059 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2029433849398919 / 4000000000000) 0 (IntervalRat.scale (817 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-25272037250 / 1000000000000) (-25272025205 / 1000000000000), orderedInterval (24846211975 / 1000000000000) (24846224020 / 1000000000000)))) (orderedInterval (4262377097 / 1000000000000) (4262380006 / 1000000000000))) = true
  rfl'

theorem compactCertificate537_chunkChecks0 :
    compactCertificate537.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate537.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate537_chunkChecks0_0
    compactCertificate537_chunkChecks0_1 compactCertificate537_chunkChecks0_2

theorem compactCertificate537_chunkChecks1_0 :
    compactCertificate537.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (817 / 2) 1 (IntervalRat.scale (817 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (30377263210 / 1000000000000) (30377263211 / 1000000000000), orderedInterval (25175006112 / 1000000000000) (25175006113 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1203597004435117 / 4000000000000) 1 (IntervalRat.scale (817 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (4195482697 / 1000000000000) (4195482698 / 1000000000000), orderedInterval (45798320875 / 1000000000000) (45798320876 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (389218541773261 / 800000000000) 1 (IntervalRat.scale (817 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-12792240455 / 1000000000000) (-12792240454 / 1000000000000), orderedInterval (-33822747454 / 1000000000000) (-33822747453 / 1000000000000)))) (orderedInterval (7928989860 / 1000000000000) (7928989893 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (351206604080519 / 4000000000000) 1 (IntervalRat.scale (817 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (49546652072 / 1000000000000) (49546652073 / 1000000000000), orderedInterval (68969757349 / 1000000000000) (68969757350 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (943390339855643 / 4000000000000) 1 (IntervalRat.scale (817 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-44079607399 / 1000000000000) (-44079607398 / 1000000000000), orderedInterval (-27406918749 / 1000000000000) (-27406918748 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2561488288264431 / 4000000000000) 1 (IntervalRat.scale (817 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (8482146402 / 1000000000000) (8482146403 / 1000000000000), orderedInterval (30361022621 / 1000000000000) (30361022622 / 1000000000000)))) (orderedInterval (-4122046555 / 1000000000000) (-4122046499 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1886780679712103 / 4000000000000) 1 (IntervalRat.scale (817 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (34762440790 / 1000000000000) (34762440794 / 1000000000000), orderedInterval (11846520229 / 1000000000000) (11846520233 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3233030853833219 / 4000000000000) 1 (IntervalRat.scale (817 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-27968744026 / 1000000000000) (-27968736256 / 1000000000000), orderedInterval (2339787482 / 1000000000000) (2339795253 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2381435894074121 / 4000000000000) 1 (IntervalRat.scale (817 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-22490933415 / 1000000000000) (-22490928094 / 1000000000000), orderedInterval (23756242865 / 1000000000000) (23756248186 / 1000000000000)))) (orderedInterval (693976576 / 1000000000000) (693977278 / 1000000000000))) = true
  rfl'

theorem compactCertificate537_chunkChecks1_1 :
    compactCertificate537.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3653735075234183 / 4000000000000) 1 (IntervalRat.scale (817 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-410974482 / 1000000000000) (-410974481 / 1000000000000), orderedInterval (-26396432237 / 1000000000000) (-26396432236 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2109484929233807 / 4000000000000) 1 (IntervalRat.scale (817 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (12526037744 / 1000000000000) (12526037745 / 1000000000000), orderedInterval (32395771118 / 1000000000000) (32395771119 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3743318024849563 / 4000000000000) 1 (IntervalRat.scale (817 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (10639038190 / 1000000000000) (10639038191 / 1000000000000), orderedInterval (23807844928 / 1000000000000) (23807844929 / 1000000000000)))) (orderedInterval (21339967090 / 1000000000000) (21339967426 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3497493269257447 / 4000000000000) 1 (IntervalRat.scale (817 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (26302818266 / 1000000000000) (26302859709 / 1000000000000), orderedInterval (-6035646465 / 1000000000000) (-6035605022 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2495976228518551 / 4000000000000) 1 (IntervalRat.scale (817 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (12370251219 / 1000000000000) (12370251270 / 1000000000000), orderedInterval (-29458355666 / 1000000000000) (-29458355615 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2830171019566929 / 4000000000000) 1 (IntervalRat.scale (817 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-29842652063 / 1000000000000) (-29842651509 / 1000000000000), orderedInterval (-3008345808 / 1000000000000) (-3008345254 / 1000000000000)))) (orderedInterval (-3995581222 / 1000000000000) (-3995579529 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2359501535953601 / 4000000000000) 1 (IntervalRat.scale (817 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (1351517093 / 1000000000000) (1351517094 / 1000000000000), orderedInterval (32822905075 / 1000000000000) (32822905076 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2084691163517621 / 4000000000000) 1 (IntervalRat.scale (817 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (15314325219 / 1000000000000) (15314325220 / 1000000000000), orderedInterval (31401635125 / 1000000000000) (31401635126 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (604224753928479 / 800000000000) 1 (IntervalRat.scale (817 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (25293354212 / 1000000000000) (25293397834 / 1000000000000), orderedInterval (-14269357035 / 1000000000000) (-14269313413 / 1000000000000)))) (orderedInterval (-2420850351 / 1000000000000) (-2420848229 / 1000000000000))) = true
  rfl'

theorem compactCertificate537_chunkChecks1_2 :
    compactCertificate537.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1671317467972813 / 4000000000000) 1 (IntervalRat.scale (817 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-27524890568 / 1000000000000) (-27524890567 / 1000000000000), orderedInterval (-27644059446 / 1000000000000) (-27644059445 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1416794326934693 / 4000000000000) 1 (IntervalRat.scale (817 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (692827848 / 1000000000000) (692827850 / 1000000000000), orderedInterval (-42390534113 / 1000000000000) (-42390534111 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (886564105925879 / 4000000000000) 1 (IntervalRat.scale (817 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (31453883673 / 1000000000000) (31453893302 / 1000000000000), orderedInterval (-43464005469 / 1000000000000) (-43463995839 / 1000000000000)))) (orderedInterval (5833657125 / 1000000000000) (5833657391 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (476797124745993 / 4000000000000) 1 (IntervalRat.scale (817 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (41451713353 / 1000000000000) (41451713354 / 1000000000000), orderedInterval (60013952724 / 1000000000000) (60013952725 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1294596943936979 / 4000000000000) 1 (IntervalRat.scale (817 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-33325956035 / 1000000000000) (-33325956034 / 1000000000000), orderedInterval (-29212583536 / 1000000000000) (-29212583535 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1767661448448883 / 4000000000000) 1 (IntervalRat.scale (817 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (9907340721 / 1000000000000) (9907340748 / 1000000000000), orderedInterval (-36650498290 / 1000000000000) (-36650498263 / 1000000000000)))) (orderedInterval (3240339397 / 1000000000000) (3240339444 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (747435894074121 / 4000000000000) 1 (IntervalRat.scale (817 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-43922974142 / 1000000000000) (-43922885368 / 1000000000000), orderedInterval (38558705744 / 1000000000000) (38558794518 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3038285413011241 / 4000000000000) 1 (IntervalRat.scale (817 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (2635606719 / 1000000000000) (2635606720 / 1000000000000), orderedInterval (28828528058 / 1000000000000) (28828528059 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2029433849398919 / 4000000000000) 1 (IntervalRat.scale (817 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-25272037250 / 1000000000000) (-25272025205 / 1000000000000), orderedInterval (24846211975 / 1000000000000) (24846224020 / 1000000000000)))) (orderedInterval (-10047138060 / 1000000000000) (-10047134849 / 1000000000000))) = true
  rfl'

theorem compactCertificate537_chunkChecks1 :
    compactCertificate537.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate537.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate537_chunkChecks1_0
    compactCertificate537_chunkChecks1_1 compactCertificate537_chunkChecks1_2

theorem compactCertificate537_chunkChecks2_0 :
    compactCertificate537.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (817 / 2) 2 (IntervalRat.scale (817 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (30377263210 / 1000000000000) (30377263211 / 1000000000000), orderedInterval (25175006112 / 1000000000000) (25175006113 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1203597004435117 / 4000000000000) 2 (IntervalRat.scale (817 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (4195482697 / 1000000000000) (4195482698 / 1000000000000), orderedInterval (45798320875 / 1000000000000) (45798320876 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (389218541773261 / 800000000000) 2 (IntervalRat.scale (817 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-12792240455 / 1000000000000) (-12792240454 / 1000000000000), orderedInterval (-33822747454 / 1000000000000) (-33822747453 / 1000000000000)))) (orderedInterval (-11016304816 / 1000000000000) (-11016304778 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (351206604080519 / 4000000000000) 2 (IntervalRat.scale (817 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (49546652072 / 1000000000000) (49546652073 / 1000000000000), orderedInterval (68969757349 / 1000000000000) (68969757350 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (943390339855643 / 4000000000000) 2 (IntervalRat.scale (817 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-44079607399 / 1000000000000) (-44079607398 / 1000000000000), orderedInterval (-27406918749 / 1000000000000) (-27406918748 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2561488288264431 / 4000000000000) 2 (IntervalRat.scale (817 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (8482146402 / 1000000000000) (8482146403 / 1000000000000), orderedInterval (30361022621 / 1000000000000) (30361022622 / 1000000000000)))) (orderedInterval (2053209280 / 1000000000000) (2053209358 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1886780679712103 / 4000000000000) 2 (IntervalRat.scale (817 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (34762440790 / 1000000000000) (34762440794 / 1000000000000), orderedInterval (11846520229 / 1000000000000) (11846520233 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3233030853833219 / 4000000000000) 2 (IntervalRat.scale (817 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-27968744026 / 1000000000000) (-27968736256 / 1000000000000), orderedInterval (2339787482 / 1000000000000) (2339795253 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2381435894074121 / 4000000000000) 2 (IntervalRat.scale (817 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-22490933415 / 1000000000000) (-22490928094 / 1000000000000), orderedInterval (23756242865 / 1000000000000) (23756248186 / 1000000000000)))) (orderedInterval (-2224342917 / 1000000000000) (-2224341633 / 1000000000000))) = true
  rfl'

theorem compactCertificate537_chunkChecks2_1 :
    compactCertificate537.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3653735075234183 / 4000000000000) 2 (IntervalRat.scale (817 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-410974482 / 1000000000000) (-410974481 / 1000000000000), orderedInterval (-26396432237 / 1000000000000) (-26396432236 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2109484929233807 / 4000000000000) 2 (IntervalRat.scale (817 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (12526037744 / 1000000000000) (12526037745 / 1000000000000), orderedInterval (32395771118 / 1000000000000) (32395771119 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3743318024849563 / 4000000000000) 2 (IntervalRat.scale (817 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (10639038190 / 1000000000000) (10639038191 / 1000000000000), orderedInterval (23807844928 / 1000000000000) (23807844929 / 1000000000000)))) (orderedInterval (-9901529222 / 1000000000000) (-9901528501 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3497493269257447 / 4000000000000) 2 (IntervalRat.scale (817 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (26302818266 / 1000000000000) (26302859709 / 1000000000000), orderedInterval (-6035646465 / 1000000000000) (-6035605022 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2495976228518551 / 4000000000000) 2 (IntervalRat.scale (817 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (12370251219 / 1000000000000) (12370251270 / 1000000000000), orderedInterval (-29458355666 / 1000000000000) (-29458355615 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2830171019566929 / 4000000000000) 2 (IntervalRat.scale (817 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-29842652063 / 1000000000000) (-29842651509 / 1000000000000), orderedInterval (-3008345808 / 1000000000000) (-3008345254 / 1000000000000)))) (orderedInterval (-997215325 / 1000000000000) (-997211743 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2359501535953601 / 4000000000000) 2 (IntervalRat.scale (817 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (1351517093 / 1000000000000) (1351517094 / 1000000000000), orderedInterval (32822905075 / 1000000000000) (32822905076 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2084691163517621 / 4000000000000) 2 (IntervalRat.scale (817 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (15314325219 / 1000000000000) (15314325220 / 1000000000000), orderedInterval (31401635125 / 1000000000000) (31401635126 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (604224753928479 / 800000000000) 2 (IntervalRat.scale (817 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (25293354212 / 1000000000000) (25293397834 / 1000000000000), orderedInterval (-14269357035 / 1000000000000) (-14269313413 / 1000000000000)))) (orderedInterval (-813947753 / 1000000000000) (-813943845 / 1000000000000))) = true
  rfl'

theorem compactCertificate537_chunkChecks2_2 :
    compactCertificate537.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1671317467972813 / 4000000000000) 2 (IntervalRat.scale (817 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-27524890568 / 1000000000000) (-27524890567 / 1000000000000), orderedInterval (-27644059446 / 1000000000000) (-27644059445 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1416794326934693 / 4000000000000) 2 (IntervalRat.scale (817 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (692827848 / 1000000000000) (692827850 / 1000000000000), orderedInterval (-42390534113 / 1000000000000) (-42390534111 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (886564105925879 / 4000000000000) 2 (IntervalRat.scale (817 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (31453883673 / 1000000000000) (31453893302 / 1000000000000), orderedInterval (-43464005469 / 1000000000000) (-43463995839 / 1000000000000)))) (orderedInterval (-4890586263 / 1000000000000) (-4890586079 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (476797124745993 / 4000000000000) 2 (IntervalRat.scale (817 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (41451713353 / 1000000000000) (41451713354 / 1000000000000), orderedInterval (60013952724 / 1000000000000) (60013952725 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1294596943936979 / 4000000000000) 2 (IntervalRat.scale (817 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-33325956035 / 1000000000000) (-33325956034 / 1000000000000), orderedInterval (-29212583536 / 1000000000000) (-29212583535 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1767661448448883 / 4000000000000) 2 (IntervalRat.scale (817 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (9907340721 / 1000000000000) (9907340748 / 1000000000000), orderedInterval (-36650498290 / 1000000000000) (-36650498263 / 1000000000000)))) (orderedInterval (471232988 / 1000000000000) (471233035 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (747435894074121 / 4000000000000) 2 (IntervalRat.scale (817 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-43922974142 / 1000000000000) (-43922885368 / 1000000000000), orderedInterval (38558705744 / 1000000000000) (38558794518 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3038285413011241 / 4000000000000) 2 (IntervalRat.scale (817 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (2635606719 / 1000000000000) (2635606720 / 1000000000000), orderedInterval (28828528058 / 1000000000000) (28828528059 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2029433849398919 / 4000000000000) 2 (IntervalRat.scale (817 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-25272037250 / 1000000000000) (-25272025205 / 1000000000000), orderedInterval (24846211975 / 1000000000000) (24846224020 / 1000000000000)))) (orderedInterval (-6492660071 / 1000000000000) (-6492656230 / 1000000000000))) = true
  rfl'

theorem compactCertificate537_chunkChecks2 :
    compactCertificate537.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate537.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate537_chunkChecks2_0
    compactCertificate537_chunkChecks2_1 compactCertificate537_chunkChecks2_2

theorem compactCertificate537_chunkChecks3_0 :
    compactCertificate537.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (817 / 2) 3 (IntervalRat.scale (817 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (30377263210 / 1000000000000) (30377263211 / 1000000000000), orderedInterval (25175006112 / 1000000000000) (25175006113 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1203597004435117 / 4000000000000) 3 (IntervalRat.scale (817 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (4195482697 / 1000000000000) (4195482698 / 1000000000000), orderedInterval (45798320875 / 1000000000000) (45798320876 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (389218541773261 / 800000000000) 3 (IntervalRat.scale (817 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-12792240455 / 1000000000000) (-12792240454 / 1000000000000), orderedInterval (-33822747454 / 1000000000000) (-33822747453 / 1000000000000)))) (orderedInterval (-6768966024 / 1000000000000) (-6768965981 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (351206604080519 / 4000000000000) 3 (IntervalRat.scale (817 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (49546652072 / 1000000000000) (49546652073 / 1000000000000), orderedInterval (68969757349 / 1000000000000) (68969757350 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (943390339855643 / 4000000000000) 3 (IntervalRat.scale (817 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-44079607399 / 1000000000000) (-44079607398 / 1000000000000), orderedInterval (-27406918749 / 1000000000000) (-27406918748 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2561488288264431 / 4000000000000) 3 (IntervalRat.scale (817 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (8482146402 / 1000000000000) (8482146403 / 1000000000000), orderedInterval (30361022621 / 1000000000000) (30361022622 / 1000000000000)))) (orderedInterval (8509603430 / 1000000000000) (8509603546 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1886780679712103 / 4000000000000) 3 (IntervalRat.scale (817 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (34762440790 / 1000000000000) (34762440794 / 1000000000000), orderedInterval (11846520229 / 1000000000000) (11846520233 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3233030853833219 / 4000000000000) 3 (IntervalRat.scale (817 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-27968744026 / 1000000000000) (-27968736256 / 1000000000000), orderedInterval (2339787482 / 1000000000000) (2339795253 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2381435894074121 / 4000000000000) 3 (IntervalRat.scale (817 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-22490933415 / 1000000000000) (-22490928094 / 1000000000000), orderedInterval (23756242865 / 1000000000000) (23756248186 / 1000000000000)))) (orderedInterval (-1212916656 / 1000000000000) (-1212914269 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate537_chunkChecks3_1 :
    compactCertificate537.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3653735075234183 / 4000000000000) 3 (IntervalRat.scale (817 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-410974482 / 1000000000000) (-410974481 / 1000000000000), orderedInterval (-26396432237 / 1000000000000) (-26396432236 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2109484929233807 / 4000000000000) 3 (IntervalRat.scale (817 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (12526037744 / 1000000000000) (12526037745 / 1000000000000), orderedInterval (32395771118 / 1000000000000) (32395771119 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3743318024849563 / 4000000000000) 3 (IntervalRat.scale (817 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (10639038190 / 1000000000000) (10639038191 / 1000000000000), orderedInterval (23807844928 / 1000000000000) (23807844929 / 1000000000000)))) (orderedInterval (-98270681730 / 1000000000000) (-98270680150 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3497493269257447 / 4000000000000) 3 (IntervalRat.scale (817 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (26302818266 / 1000000000000) (26302859709 / 1000000000000), orderedInterval (-6035646465 / 1000000000000) (-6035605022 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2495976228518551 / 4000000000000) 3 (IntervalRat.scale (817 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (12370251219 / 1000000000000) (12370251270 / 1000000000000), orderedInterval (-29458355666 / 1000000000000) (-29458355615 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2830171019566929 / 4000000000000) 3 (IntervalRat.scale (817 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-29842652063 / 1000000000000) (-29842651509 / 1000000000000), orderedInterval (-3008345808 / 1000000000000) (-3008345254 / 1000000000000)))) (orderedInterval (8783517425 / 1000000000000) (8783525024 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2359501535953601 / 4000000000000) 3 (IntervalRat.scale (817 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (1351517093 / 1000000000000) (1351517094 / 1000000000000), orderedInterval (32822905075 / 1000000000000) (32822905076 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2084691163517621 / 4000000000000) 3 (IntervalRat.scale (817 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (15314325219 / 1000000000000) (15314325220 / 1000000000000), orderedInterval (31401635125 / 1000000000000) (31401635126 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (604224753928479 / 800000000000) 3 (IntervalRat.scale (817 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (25293354212 / 1000000000000) (25293397834 / 1000000000000), orderedInterval (-14269357035 / 1000000000000) (-14269313413 / 1000000000000)))) (orderedInterval (4901741766 / 1000000000000) (4901748965 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate537_chunkChecks3_2 :
    compactCertificate537.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1671317467972813 / 4000000000000) 3 (IntervalRat.scale (817 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-27524890568 / 1000000000000) (-27524890567 / 1000000000000), orderedInterval (-27644059446 / 1000000000000) (-27644059445 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1416794326934693 / 4000000000000) 3 (IntervalRat.scale (817 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (692827848 / 1000000000000) (692827850 / 1000000000000), orderedInterval (-42390534113 / 1000000000000) (-42390534111 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (886564105925879 / 4000000000000) 3 (IntervalRat.scale (817 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (31453883673 / 1000000000000) (31453893302 / 1000000000000), orderedInterval (-43464005469 / 1000000000000) (-43463995839 / 1000000000000)))) (orderedInterval (-6055912924 / 1000000000000) (-6055912785 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (476797124745993 / 4000000000000) 3 (IntervalRat.scale (817 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (41451713353 / 1000000000000) (41451713354 / 1000000000000), orderedInterval (60013952724 / 1000000000000) (60013952725 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1294596943936979 / 4000000000000) 3 (IntervalRat.scale (817 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-33325956035 / 1000000000000) (-33325956034 / 1000000000000), orderedInterval (-29212583536 / 1000000000000) (-29212583535 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1767661448448883 / 4000000000000) 3 (IntervalRat.scale (817 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (9907340721 / 1000000000000) (9907340748 / 1000000000000), orderedInterval (-36650498290 / 1000000000000) (-36650498263 / 1000000000000)))) (orderedInterval (-3859273355 / 1000000000000) (-3859273307 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (747435894074121 / 4000000000000) 3 (IntervalRat.scale (817 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-43922974142 / 1000000000000) (-43922885368 / 1000000000000), orderedInterval (38558705744 / 1000000000000) (38558794518 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3038285413011241 / 4000000000000) 3 (IntervalRat.scale (817 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (2635606719 / 1000000000000) (2635606720 / 1000000000000), orderedInterval (28828528058 / 1000000000000) (28828528059 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2029433849398919 / 4000000000000) 3 (IntervalRat.scale (817 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-25272037250 / 1000000000000) (-25272025205 / 1000000000000), orderedInterval (24846211975 / 1000000000000) (24846224020 / 1000000000000)))) (orderedInterval (24011466167 / 1000000000000) (24011470919 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate537_chunkChecks3 :
    compactCertificate537.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate537.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate537_chunkChecks3_0
    compactCertificate537_chunkChecks3_1 compactCertificate537_chunkChecks3_2

theorem compactCertificate537_chunkChecks4_0 :
    compactCertificate537.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (817 / 2) 4 (IntervalRat.scale (817 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (30377263210 / 1000000000000) (30377263211 / 1000000000000), orderedInterval (25175006112 / 1000000000000) (25175006113 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1203597004435117 / 4000000000000) 4 (IntervalRat.scale (817 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (4195482697 / 1000000000000) (4195482698 / 1000000000000), orderedInterval (45798320875 / 1000000000000) (45798320876 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (389218541773261 / 800000000000) 4 (IntervalRat.scale (817 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-12792240455 / 1000000000000) (-12792240454 / 1000000000000), orderedInterval (-33822747454 / 1000000000000) (-33822747453 / 1000000000000)))) (orderedInterval (10574670008 / 1000000000000) (10574670059 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (351206604080519 / 4000000000000) 4 (IntervalRat.scale (817 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (49546652072 / 1000000000000) (49546652073 / 1000000000000), orderedInterval (68969757349 / 1000000000000) (68969757350 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (943390339855643 / 4000000000000) 4 (IntervalRat.scale (817 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-44079607399 / 1000000000000) (-44079607398 / 1000000000000), orderedInterval (-27406918749 / 1000000000000) (-27406918748 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2561488288264431 / 4000000000000) 4 (IntervalRat.scale (817 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (8482146402 / 1000000000000) (8482146403 / 1000000000000), orderedInterval (30361022621 / 1000000000000) (30361022622 / 1000000000000)))) (orderedInterval (-3863064297 / 1000000000000) (-3863064119 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1886780679712103 / 4000000000000) 4 (IntervalRat.scale (817 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (34762440790 / 1000000000000) (34762440794 / 1000000000000), orderedInterval (11846520229 / 1000000000000) (11846520233 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3233030853833219 / 4000000000000) 4 (IntervalRat.scale (817 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-27968744026 / 1000000000000) (-27968736256 / 1000000000000), orderedInterval (2339787482 / 1000000000000) (2339795253 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2381435894074121 / 4000000000000) 4 (IntervalRat.scale (817 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-22490933415 / 1000000000000) (-22490928094 / 1000000000000), orderedInterval (23756242865 / 1000000000000) (23756248186 / 1000000000000)))) (orderedInterval (10774815818 / 1000000000000) (10774820321 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate537_chunkChecks4_1 :
    compactCertificate537.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3653735075234183 / 4000000000000) 4 (IntervalRat.scale (817 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-410974482 / 1000000000000) (-410974481 / 1000000000000), orderedInterval (-26396432237 / 1000000000000) (-26396432236 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2109484929233807 / 4000000000000) 4 (IntervalRat.scale (817 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (12526037744 / 1000000000000) (12526037745 / 1000000000000), orderedInterval (32395771118 / 1000000000000) (32395771119 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3743318024849563 / 4000000000000) 4 (IntervalRat.scale (817 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (10639038190 / 1000000000000) (10639038191 / 1000000000000), orderedInterval (23807844928 / 1000000000000) (23807844929 / 1000000000000)))) (orderedInterval (46541489838 / 1000000000000) (46541493346 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3497493269257447 / 4000000000000) 4 (IntervalRat.scale (817 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (26302818266 / 1000000000000) (26302859709 / 1000000000000), orderedInterval (-6035646465 / 1000000000000) (-6035605022 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2495976228518551 / 4000000000000) 4 (IntervalRat.scale (817 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (12370251219 / 1000000000000) (12370251270 / 1000000000000), orderedInterval (-29458355666 / 1000000000000) (-29458355615 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2830171019566929 / 4000000000000) 4 (IntervalRat.scale (817 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-29842652063 / 1000000000000) (-29842651509 / 1000000000000), orderedInterval (-3008345808 / 1000000000000) (-3008345254 / 1000000000000)))) (orderedInterval (-2282306110 / 1000000000000) (-2282289934 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2359501535953601 / 4000000000000) 4 (IntervalRat.scale (817 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (1351517093 / 1000000000000) (1351517094 / 1000000000000), orderedInterval (32822905075 / 1000000000000) (32822905076 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2084691163517621 / 4000000000000) 4 (IntervalRat.scale (817 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (15314325219 / 1000000000000) (15314325220 / 1000000000000), orderedInterval (31401635125 / 1000000000000) (31401635126 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (604224753928479 / 800000000000) 4 (IntervalRat.scale (817 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (25293354212 / 1000000000000) (25293397834 / 1000000000000), orderedInterval (-14269357035 / 1000000000000) (-14269313413 / 1000000000000)))) (orderedInterval (5289857985 / 1000000000000) (5289871277 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate537_chunkChecks4_2 :
    compactCertificate537.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1671317467972813 / 4000000000000) 4 (IntervalRat.scale (817 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-27524890568 / 1000000000000) (-27524890567 / 1000000000000), orderedInterval (-27644059446 / 1000000000000) (-27644059445 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1416794326934693 / 4000000000000) 4 (IntervalRat.scale (817 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (692827848 / 1000000000000) (692827850 / 1000000000000), orderedInterval (-42390534113 / 1000000000000) (-42390534111 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (886564105925879 / 4000000000000) 4 (IntervalRat.scale (817 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (31453883673 / 1000000000000) (31453893302 / 1000000000000), orderedInterval (-43464005469 / 1000000000000) (-43463995839 / 1000000000000)))) (orderedInterval (4913246997 / 1000000000000) (4913247112 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (476797124745993 / 4000000000000) 4 (IntervalRat.scale (817 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (41451713353 / 1000000000000) (41451713354 / 1000000000000), orderedInterval (60013952724 / 1000000000000) (60013952725 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1294596943936979 / 4000000000000) 4 (IntervalRat.scale (817 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-33325956035 / 1000000000000) (-33325956034 / 1000000000000), orderedInterval (-29212583536 / 1000000000000) (-29212583535 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1767661448448883 / 4000000000000) 4 (IntervalRat.scale (817 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (9907340721 / 1000000000000) (9907340748 / 1000000000000), orderedInterval (-36650498290 / 1000000000000) (-36650498263 / 1000000000000)))) (orderedInterval (-728646683 / 1000000000000) (-728646633 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (747435894074121 / 4000000000000) 4 (IntervalRat.scale (817 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-43922974142 / 1000000000000) (-43922885368 / 1000000000000), orderedInterval (38558705744 / 1000000000000) (38558794518 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3038285413011241 / 4000000000000) 4 (IntervalRat.scale (817 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (2635606719 / 1000000000000) (2635606720 / 1000000000000), orderedInterval (28828528058 / 1000000000000) (28828528059 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2029433849398919 / 4000000000000) 4 (IntervalRat.scale (817 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-25272037250 / 1000000000000) (-25272025205 / 1000000000000), orderedInterval (24846211975 / 1000000000000) (24846224020 / 1000000000000)))) (orderedInterval (8589232092 / 1000000000000) (8589238096 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate537_chunkChecks4 :
    compactCertificate537.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate537.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate537_chunkChecks4_0
    compactCertificate537_chunkChecks4_1 compactCertificate537_chunkChecks4_2

theorem compactCertificate537_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate537.chunkCheck r b = true :=
  compactCertificate537.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate537_chunkChecks0
    · exact compactCertificate537_chunkChecks1
    · exact compactCertificate537_chunkChecks2
    · exact compactCertificate537_chunkChecks3
    · exact compactCertificate537_chunkChecks4)

theorem compactCertificate537_coefficient0 :
    compactCertificate537.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate537_coefficient1 :
    compactCertificate537.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate537_coefficient2 :
    compactCertificate537.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate537_coefficient3 :
    compactCertificate537.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate537_coefficient4 :
    compactCertificate537.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate537_coefficients : ∀ r : Fin 5,
    compactCertificate537.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate537_coefficient0
  · exact compactCertificate537_coefficient1
  · exact compactCertificate537_coefficient2
  · exact compactCertificate537_coefficient3
  · exact compactCertificate537_coefficient4

theorem compactCertificate537_lower : (1 : ℚ) ≤ compactCertificate537.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate537, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate537_proves {t : ℝ} (ht : t ∈ compactCertificate537.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate537.proves compactCertificate537_states compactCertificate537_chunks
    compactCertificate537_coefficients compactCertificate537_lower ht

end Erdos232
