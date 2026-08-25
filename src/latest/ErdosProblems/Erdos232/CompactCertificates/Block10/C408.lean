/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate408 : CompactCertificate where
  left := 279
  right := 280
  center := 559 / 2
  grid := fun i =>
    match i.val with
    | 0 => 89
    | 1 => 66
    | 2 => 106
    | 3 => 19
    | 4 => 51
    | 5 => 140
    | 6 => 103
    | 7 => 176
    | 8 => 130
    | 9 => 199
    | 10 => 115
    | 11 => 204
    | 12 => 191
    | 13 => 136
    | 14 => 154
    | 15 => 129
    | 16 => 114
    | 17 => 165
    | 18 => 91
    | 19 => 77
    | 20 => 48
    | 21 => 26
    | 22 => 71
    | 23 => 96
    | 24 => 41
    | 25 => 166
    | _ => 111
  point := fun i =>
    match i.val with
    | 0 => 559 / 2
    | 1 => 823513739876659 / 4000000000000
    | 2 => 266307423318547 / 800000000000
    | 3 => 240299255423513 / 4000000000000
    | 4 => 645477600953861 / 4000000000000
    | 5 => 1752597249865137 / 4000000000000
    | 6 => 1290955201908281 / 4000000000000
    | 7 => 2212073742096413 / 4000000000000
    | 8 => 1629403506471767 / 4000000000000
    | 9 => 2499923998844441 / 4000000000000
    | 10 => 1443331793686289 / 4000000000000
    | 11 => 2561217595949701 / 4000000000000
    | 12 => 2393021710544569 / 4000000000000
    | 13 => 1707773208986377 / 4000000000000
    | 14 => 1936432802861583 / 4000000000000
    | 15 => 1614395787757727 / 4000000000000
    | 16 => 1426367638196267 / 4000000000000
    | 17 => 413416936898433 / 800000000000
    | 18 => 1143533004402451 / 4000000000000
    | 19 => 969385592113211 / 4000000000000
    | 20 => 606596493528233 / 4000000000000
    | 21 => 326229611668311 / 4000000000000
    | 22 => 885776856377933 / 4000000000000
    | 23 => 1209452569991341 / 4000000000000
    | 24 => 511403506471767 / 4000000000000
    | 25 => 2078826861534007 / 4000000000000
    | _ => 1388560002220313 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-30128119829 / 1000000000000) (-30128119828 / 1000000000000), orderedInterval (-36959702807 / 1000000000000) (-36959702806 / 1000000000000))
    | 1 => (orderedInterval (-35047289049 / 1000000000000) (-35047271296 / 1000000000000), orderedInterval (43258038396 / 1000000000000) (43258056149 / 1000000000000))
    | 2 => (orderedInterval (26829043396 / 1000000000000) (26829043397 / 1000000000000), orderedInterval (34494302896 / 1000000000000) (34494302897 / 1000000000000))
    | 3 => (orderedInterval (-94696824615 / 1000000000000) (-94696824614 / 1000000000000), orderedInterval (-39577394432 / 1000000000000) (-39577394431 / 1000000000000))
    | 4 => (orderedInterval (-58739214391 / 1000000000000) (-58739209683 / 1000000000000), orderedInterval (22426079267 / 1000000000000) (22426083976 / 1000000000000))
    | 5 => (orderedInterval (-29585443434 / 1000000000000) (-29585402956 / 1000000000000), orderedInterval (24068653006 / 1000000000000) (24068693484 / 1000000000000))
    | 6 => (orderedInterval (2673491309 / 1000000000000) (2673491312 / 1000000000000), orderedInterval (-44337075249 / 1000000000000) (-44337075246 / 1000000000000))
    | 7 => (orderedInterval (26221555575 / 1000000000000) (26221555576 / 1000000000000), orderedInterval (21507727888 / 1000000000000) (21507727889 / 1000000000000))
    | 8 => (orderedInterval (-10585621589 / 1000000000000) (-10585621549 / 1000000000000), orderedInterval (38102028993 / 1000000000000) (38102029033 / 1000000000000))
    | 9 => (orderedInterval (-17737106893 / 1000000000000) (-17737106892 / 1000000000000), orderedInterval (-26519143006 / 1000000000000) (-26519143005 / 1000000000000))
    | 10 => (orderedInterval (-13803347814 / 1000000000000) (-13803347813 / 1000000000000), orderedInterval (-39651706320 / 1000000000000) (-39651706319 / 1000000000000))
    | 11 => (orderedInterval (6409566038 / 1000000000000) (6409566039 / 1000000000000), orderedInterval (30868336957 / 1000000000000) (30868336958 / 1000000000000))
    | 12 => (orderedInterval (27512480089 / 1000000000000) (27512534738 / 1000000000000), orderedInterval (-17549822262 / 1000000000000) (-17549767614 / 1000000000000))
    | 13 => (orderedInterval (17550328074 / 1000000000000) (17550328075 / 1000000000000), orderedInterval (34375629382 / 1000000000000) (34375629383 / 1000000000000))
    | 14 => (orderedInterval (32119727187 / 1000000000000) (32119727188 / 1000000000000), orderedInterval (16800092125 / 1000000000000) (16800092126 / 1000000000000))
    | 15 => (orderedInterval (30646423255 / 1000000000000) (30646467659 / 1000000000000), orderedInterval (-25299668056 / 1000000000000) (-25299623653 / 1000000000000))
    | 16 => (orderedInterval (-29249511063 / 1000000000000) (-29249492171 / 1000000000000), orderedInterval (30532905922 / 1000000000000) (30532924814 / 1000000000000))
    | 17 => (orderedInterval (25335701169 / 1000000000000) (25335714108 / 1000000000000), orderedInterval (-24314847300 / 1000000000000) (-24314834362 / 1000000000000))
    | 18 => (orderedInterval (-33297279893 / 1000000000000) (-33297279892 / 1000000000000), orderedInterval (-33380416506 / 1000000000000) (-33380416505 / 1000000000000))
    | 19 => (orderedInterval (-48282365681 / 1000000000000) (-48282365680 / 1000000000000), orderedInterval (-17096574945 / 1000000000000) (-17096574944 / 1000000000000))
    | 20 => (orderedInterval (64648623532 / 1000000000000) (64648623656 / 1000000000000), orderedInterval (-4515641702 / 1000000000000) (-4515641577 / 1000000000000))
    | 21 => (orderedInterval (54158787532 / 1000000000000) (54158787533 / 1000000000000), orderedInterval (69472352377 / 1000000000000) (69472352378 / 1000000000000))
    | 22 => (orderedInterval (39349367722 / 1000000000000) (39349427986 / 1000000000000), orderedInterval (-36509723901 / 1000000000000) (-36509663637 / 1000000000000))
    | 23 => (orderedInterval (45879928944 / 1000000000000) (45879929058 / 1000000000000), orderedInterval (638256737 / 1000000000000) (638256852 / 1000000000000))
    | 24 => (orderedInterval (11938392733 / 1000000000000) (11938392804 / 1000000000000), orderedInterval (-69594540431 / 1000000000000) (-69594540360 / 1000000000000))
    | 25 => (orderedInterval (-29685243038 / 1000000000000) (-29685159890 / 1000000000000), orderedInterval (18568964195 / 1000000000000) (18569047343 / 1000000000000))
    | _ => (orderedInterval (30472752704 / 1000000000000) (30472778197 / 1000000000000), orderedInterval (-30132268783 / 1000000000000) (-30132243290 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-10693945906 / 1000000000000) (-10693945720 / 1000000000000)
      | 1 => orderedInterval (985937789 / 1000000000000) (985940872 / 1000000000000)
      | 2 => orderedInterval (-1064611283 / 1000000000000) (-1064611266 / 1000000000000)
      | 3 => orderedInterval (3040112774 / 1000000000000) (3040112885 / 1000000000000)
      | 4 => orderedInterval (1000378829 / 1000000000000) (1000379849 / 1000000000000)
      | 5 => orderedInterval (2676440036 / 1000000000000) (2676441988 / 1000000000000)
      | 6 => orderedInterval (10161416591 / 1000000000000) (10161416665 / 1000000000000)
      | 7 => orderedInterval (-5408949327 / 1000000000000) (-5408947917 / 1000000000000)
      | _ => orderedInterval (-3229108267 / 1000000000000) (-3229096637 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-11941845781 / 1000000000000) (-11941845636 / 1000000000000)
      | 1 => orderedInterval (-2117215234 / 1000000000000) (-2117210585 / 1000000000000)
      | 2 => orderedInterval (29501292 / 1000000000000) (29501321 / 1000000000000)
      | 3 => orderedInterval (16796579806 / 1000000000000) (16796580036 / 1000000000000)
      | 4 => orderedInterval (5496359349 / 1000000000000) (5496361515 / 1000000000000)
      | 5 => orderedInterval (-3802159800 / 1000000000000) (-3802157028 / 1000000000000)
      | 6 => orderedInterval (6218441828 / 1000000000000) (6218441896 / 1000000000000)
      | 7 => orderedInterval (229004327 / 1000000000000) (229005450 / 1000000000000)
      | _ => orderedInterval (4019286771 / 1000000000000) (4019305406 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (9928452009 / 1000000000000) (9928452125 / 1000000000000)
      | 1 => orderedInterval (-4493504260 / 1000000000000) (-4493497061 / 1000000000000)
      | 2 => orderedInterval (3709555690 / 1000000000000) (3709555742 / 1000000000000)
      | 3 => orderedInterval (-18895845741 / 1000000000000) (-18895845247 / 1000000000000)
      | 4 => orderedInterval (-1128880339 / 1000000000000) (-1128875721 / 1000000000000)
      | 5 => orderedInterval (-5666428689 / 1000000000000) (-5666424659 / 1000000000000)
      | 6 => orderedInterval (-8266305159 / 1000000000000) (-8266305095 / 1000000000000)
      | 7 => orderedInterval (4759666319 / 1000000000000) (4759667221 / 1000000000000)
      | _ => orderedInterval (435580532 / 1000000000000) (435611539 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (11033123593 / 1000000000000) (11033123690 / 1000000000000)
      | 1 => orderedInterval (6445626361 / 1000000000000) (6445637584 / 1000000000000)
      | 2 => orderedInterval (2274566166 / 1000000000000) (2274566258 / 1000000000000)
      | 3 => orderedInterval (-99052593140 / 1000000000000) (-99052592058 / 1000000000000)
      | 4 => orderedInterval (-14247183553 / 1000000000000) (-14247173709 / 1000000000000)
      | 5 => orderedInterval (8463298115 / 1000000000000) (8463304101 / 1000000000000)
      | 6 => orderedInterval (-6289032174 / 1000000000000) (-6289032113 / 1000000000000)
      | 7 => orderedInterval (-335163313 / 1000000000000) (-335162588 / 1000000000000)
      | _ => orderedInterval (-1075579187 / 1000000000000) (-1075526153 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-8948950926 / 1000000000000) (-8948950841 / 1000000000000)
      | 1 => orderedInterval (12418925850 / 1000000000000) (12418943448 / 1000000000000)
      | 2 => orderedInterval (-13565886367 / 1000000000000) (-13565886198 / 1000000000000)
      | 3 => orderedInterval (101755853930 / 1000000000000) (101755856333 / 1000000000000)
      | 4 => orderedInterval (-2750923489 / 1000000000000) (-2750902448 / 1000000000000)
      | 5 => orderedInterval (13493496147 / 1000000000000) (13493505296 / 1000000000000)
      | 6 => orderedInterval (7599176663 / 1000000000000) (7599176723 / 1000000000000)
      | 7 => orderedInterval (-5172254316 / 1000000000000) (-5172253727 / 1000000000000)
      | _ => orderedInterval (15291342937 / 1000000000000) (15291436001 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-2532328764 / 1000000000000) (-2532309281 / 1000000000000)
    | 1 => orderedInterval (14927952558 / 1000000000000) (14927982375 / 1000000000000)
    | 2 => orderedInterval (-19617709638 / 1000000000000) (-19617661156 / 1000000000000)
    | 3 => orderedInterval (-92782937132 / 1000000000000) (-92782854988 / 1000000000000)
    | _ => orderedInterval (120120780429 / 1000000000000) (120120924587 / 1000000000000)

theorem compactCertificate408_stateChecks0 :
    compactCertificate408.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 89 12 (559 / 2)) (orderedInterval (-30128119829 / 1000000000000) (-30128119828 / 1000000000000), orderedInterval (-36959702807 / 1000000000000) (-36959702806 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (823513739876659 / 4000000000000)) (orderedInterval (-35047289049 / 1000000000000) (-35047271296 / 1000000000000), orderedInterval (43258038396 / 1000000000000) (43258056149 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 106 12 (266307423318547 / 800000000000)) (orderedInterval (26829043396 / 1000000000000) (26829043397 / 1000000000000), orderedInterval (34494302896 / 1000000000000) (34494302897 / 1000000000000))) = true
  rfl'

theorem compactCertificate408_stateChecks1 :
    compactCertificate408.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 19 12 (240299255423513 / 4000000000000)) (orderedInterval (-94696824615 / 1000000000000) (-94696824614 / 1000000000000), orderedInterval (-39577394432 / 1000000000000) (-39577394431 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (645477600953861 / 4000000000000)) (orderedInterval (-58739214391 / 1000000000000) (-58739209683 / 1000000000000), orderedInterval (22426079267 / 1000000000000) (22426083976 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 140 12 (1752597249865137 / 4000000000000)) (orderedInterval (-29585443434 / 1000000000000) (-29585402956 / 1000000000000), orderedInterval (24068653006 / 1000000000000) (24068693484 / 1000000000000))) = true
  rfl'

theorem compactCertificate408_stateChecks2 :
    compactCertificate408.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 103 12 (1290955201908281 / 4000000000000)) (orderedInterval (2673491309 / 1000000000000) (2673491312 / 1000000000000), orderedInterval (-44337075249 / 1000000000000) (-44337075246 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 176 12 (2212073742096413 / 4000000000000)) (orderedInterval (26221555575 / 1000000000000) (26221555576 / 1000000000000), orderedInterval (21507727888 / 1000000000000) (21507727889 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 130 12 (1629403506471767 / 4000000000000)) (orderedInterval (-10585621589 / 1000000000000) (-10585621549 / 1000000000000), orderedInterval (38102028993 / 1000000000000) (38102029033 / 1000000000000))) = true
  rfl'

theorem compactCertificate408_stateChecks3 :
    compactCertificate408.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 199 12 (2499923998844441 / 4000000000000)) (orderedInterval (-17737106893 / 1000000000000) (-17737106892 / 1000000000000), orderedInterval (-26519143006 / 1000000000000) (-26519143005 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 115 12 (1443331793686289 / 4000000000000)) (orderedInterval (-13803347814 / 1000000000000) (-13803347813 / 1000000000000), orderedInterval (-39651706320 / 1000000000000) (-39651706319 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 204 12 (2561217595949701 / 4000000000000)) (orderedInterval (6409566038 / 1000000000000) (6409566039 / 1000000000000), orderedInterval (30868336957 / 1000000000000) (30868336958 / 1000000000000))) = true
  rfl'

theorem compactCertificate408_stateChecks4 :
    compactCertificate408.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 191 12 (2393021710544569 / 4000000000000)) (orderedInterval (27512480089 / 1000000000000) (27512534738 / 1000000000000), orderedInterval (-17549822262 / 1000000000000) (-17549767614 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 136 12 (1707773208986377 / 4000000000000)) (orderedInterval (17550328074 / 1000000000000) (17550328075 / 1000000000000), orderedInterval (34375629382 / 1000000000000) (34375629383 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 154 12 (1936432802861583 / 4000000000000)) (orderedInterval (32119727187 / 1000000000000) (32119727188 / 1000000000000), orderedInterval (16800092125 / 1000000000000) (16800092126 / 1000000000000))) = true
  rfl'

theorem compactCertificate408_stateChecks5 :
    compactCertificate408.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 129 12 (1614395787757727 / 4000000000000)) (orderedInterval (30646423255 / 1000000000000) (30646467659 / 1000000000000), orderedInterval (-25299668056 / 1000000000000) (-25299623653 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 114 12 (1426367638196267 / 4000000000000)) (orderedInterval (-29249511063 / 1000000000000) (-29249492171 / 1000000000000), orderedInterval (30532905922 / 1000000000000) (30532924814 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 165 12 (413416936898433 / 800000000000)) (orderedInterval (25335701169 / 1000000000000) (25335714108 / 1000000000000), orderedInterval (-24314847300 / 1000000000000) (-24314834362 / 1000000000000))) = true
  rfl'

theorem compactCertificate408_stateChecks6 :
    compactCertificate408.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 91 12 (1143533004402451 / 4000000000000)) (orderedInterval (-33297279893 / 1000000000000) (-33297279892 / 1000000000000), orderedInterval (-33380416506 / 1000000000000) (-33380416505 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 77 12 (969385592113211 / 4000000000000)) (orderedInterval (-48282365681 / 1000000000000) (-48282365680 / 1000000000000), orderedInterval (-17096574945 / 1000000000000) (-17096574944 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 48 12 (606596493528233 / 4000000000000)) (orderedInterval (64648623532 / 1000000000000) (64648623656 / 1000000000000), orderedInterval (-4515641702 / 1000000000000) (-4515641577 / 1000000000000))) = true
  rfl'

theorem compactCertificate408_stateChecks7 :
    compactCertificate408.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 26 12 (326229611668311 / 4000000000000)) (orderedInterval (54158787532 / 1000000000000) (54158787533 / 1000000000000), orderedInterval (69472352377 / 1000000000000) (69472352378 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (885776856377933 / 4000000000000)) (orderedInterval (39349367722 / 1000000000000) (39349427986 / 1000000000000), orderedInterval (-36509723901 / 1000000000000) (-36509663637 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 96 12 (1209452569991341 / 4000000000000)) (orderedInterval (45879928944 / 1000000000000) (45879929058 / 1000000000000), orderedInterval (638256737 / 1000000000000) (638256852 / 1000000000000))) = true
  rfl'

theorem compactCertificate408_stateChecks8 :
    compactCertificate408.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 41 12 (511403506471767 / 4000000000000)) (orderedInterval (11938392733 / 1000000000000) (11938392804 / 1000000000000), orderedInterval (-69594540431 / 1000000000000) (-69594540360 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 166 12 (2078826861534007 / 4000000000000)) (orderedInterval (-29685243038 / 1000000000000) (-29685159890 / 1000000000000), orderedInterval (18568964195 / 1000000000000) (18569047343 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 111 12 (1388560002220313 / 4000000000000)) (orderedInterval (30472752704 / 1000000000000) (30472778197 / 1000000000000), orderedInterval (-30132268783 / 1000000000000) (-30132243290 / 1000000000000))) = true
  rfl'

theorem compactCertificate408_states : ∀ j,
    BesselStateValid (compactCertificate408.point j) (compactCertificate408.state j) :=
  compactCertificate408.statesValid_of_checks3 compactCertificate408_stateChecks0
    compactCertificate408_stateChecks1 compactCertificate408_stateChecks2
    compactCertificate408_stateChecks3 compactCertificate408_stateChecks4
    compactCertificate408_stateChecks5 compactCertificate408_stateChecks6
    compactCertificate408_stateChecks7 compactCertificate408_stateChecks8

theorem compactCertificate408_chunkChecks0_0 :
    compactCertificate408.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (559 / 2) 0 (IntervalRat.scale (559 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-30128119829 / 1000000000000) (-30128119828 / 1000000000000), orderedInterval (-36959702807 / 1000000000000) (-36959702806 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (823513739876659 / 4000000000000) 0 (IntervalRat.scale (559 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-35047289049 / 1000000000000) (-35047271296 / 1000000000000), orderedInterval (43258038396 / 1000000000000) (43258056149 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (266307423318547 / 800000000000) 0 (IntervalRat.scale (559 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (26829043396 / 1000000000000) (26829043397 / 1000000000000), orderedInterval (34494302896 / 1000000000000) (34494302897 / 1000000000000)))) (orderedInterval (-10693945906 / 1000000000000) (-10693945720 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (240299255423513 / 4000000000000) 0 (IntervalRat.scale (559 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-94696824615 / 1000000000000) (-94696824614 / 1000000000000), orderedInterval (-39577394432 / 1000000000000) (-39577394431 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (645477600953861 / 4000000000000) 0 (IntervalRat.scale (559 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-58739214391 / 1000000000000) (-58739209683 / 1000000000000), orderedInterval (22426079267 / 1000000000000) (22426083976 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1752597249865137 / 4000000000000) 0 (IntervalRat.scale (559 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29585443434 / 1000000000000) (-29585402956 / 1000000000000), orderedInterval (24068653006 / 1000000000000) (24068693484 / 1000000000000)))) (orderedInterval (985937789 / 1000000000000) (985940872 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1290955201908281 / 4000000000000) 0 (IntervalRat.scale (559 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (2673491309 / 1000000000000) (2673491312 / 1000000000000), orderedInterval (-44337075249 / 1000000000000) (-44337075246 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2212073742096413 / 4000000000000) 0 (IntervalRat.scale (559 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (26221555575 / 1000000000000) (26221555576 / 1000000000000), orderedInterval (21507727888 / 1000000000000) (21507727889 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1629403506471767 / 4000000000000) 0 (IntervalRat.scale (559 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-10585621589 / 1000000000000) (-10585621549 / 1000000000000), orderedInterval (38102028993 / 1000000000000) (38102029033 / 1000000000000)))) (orderedInterval (-1064611283 / 1000000000000) (-1064611266 / 1000000000000))) = true
  rfl'

theorem compactCertificate408_chunkChecks0_1 :
    compactCertificate408.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2499923998844441 / 4000000000000) 0 (IntervalRat.scale (559 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-17737106893 / 1000000000000) (-17737106892 / 1000000000000), orderedInterval (-26519143006 / 1000000000000) (-26519143005 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1443331793686289 / 4000000000000) 0 (IntervalRat.scale (559 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-13803347814 / 1000000000000) (-13803347813 / 1000000000000), orderedInterval (-39651706320 / 1000000000000) (-39651706319 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2561217595949701 / 4000000000000) 0 (IntervalRat.scale (559 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (6409566038 / 1000000000000) (6409566039 / 1000000000000), orderedInterval (30868336957 / 1000000000000) (30868336958 / 1000000000000)))) (orderedInterval (3040112774 / 1000000000000) (3040112885 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2393021710544569 / 4000000000000) 0 (IntervalRat.scale (559 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (27512480089 / 1000000000000) (27512534738 / 1000000000000), orderedInterval (-17549822262 / 1000000000000) (-17549767614 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1707773208986377 / 4000000000000) 0 (IntervalRat.scale (559 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (17550328074 / 1000000000000) (17550328075 / 1000000000000), orderedInterval (34375629382 / 1000000000000) (34375629383 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1936432802861583 / 4000000000000) 0 (IntervalRat.scale (559 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (32119727187 / 1000000000000) (32119727188 / 1000000000000), orderedInterval (16800092125 / 1000000000000) (16800092126 / 1000000000000)))) (orderedInterval (1000378829 / 1000000000000) (1000379849 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1614395787757727 / 4000000000000) 0 (IntervalRat.scale (559 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (30646423255 / 1000000000000) (30646467659 / 1000000000000), orderedInterval (-25299668056 / 1000000000000) (-25299623653 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1426367638196267 / 4000000000000) 0 (IntervalRat.scale (559 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-29249511063 / 1000000000000) (-29249492171 / 1000000000000), orderedInterval (30532905922 / 1000000000000) (30532924814 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (413416936898433 / 800000000000) 0 (IntervalRat.scale (559 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (25335701169 / 1000000000000) (25335714108 / 1000000000000), orderedInterval (-24314847300 / 1000000000000) (-24314834362 / 1000000000000)))) (orderedInterval (2676440036 / 1000000000000) (2676441988 / 1000000000000))) = true
  rfl'

theorem compactCertificate408_chunkChecks0_2 :
    compactCertificate408.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1143533004402451 / 4000000000000) 0 (IntervalRat.scale (559 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-33297279893 / 1000000000000) (-33297279892 / 1000000000000), orderedInterval (-33380416506 / 1000000000000) (-33380416505 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (969385592113211 / 4000000000000) 0 (IntervalRat.scale (559 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-48282365681 / 1000000000000) (-48282365680 / 1000000000000), orderedInterval (-17096574945 / 1000000000000) (-17096574944 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (606596493528233 / 4000000000000) 0 (IntervalRat.scale (559 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (64648623532 / 1000000000000) (64648623656 / 1000000000000), orderedInterval (-4515641702 / 1000000000000) (-4515641577 / 1000000000000)))) (orderedInterval (10161416591 / 1000000000000) (10161416665 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (326229611668311 / 4000000000000) 0 (IntervalRat.scale (559 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (54158787532 / 1000000000000) (54158787533 / 1000000000000), orderedInterval (69472352377 / 1000000000000) (69472352378 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (885776856377933 / 4000000000000) 0 (IntervalRat.scale (559 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (39349367722 / 1000000000000) (39349427986 / 1000000000000), orderedInterval (-36509723901 / 1000000000000) (-36509663637 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1209452569991341 / 4000000000000) 0 (IntervalRat.scale (559 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (45879928944 / 1000000000000) (45879929058 / 1000000000000), orderedInterval (638256737 / 1000000000000) (638256852 / 1000000000000)))) (orderedInterval (-5408949327 / 1000000000000) (-5408947917 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (511403506471767 / 4000000000000) 0 (IntervalRat.scale (559 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (11938392733 / 1000000000000) (11938392804 / 1000000000000), orderedInterval (-69594540431 / 1000000000000) (-69594540360 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2078826861534007 / 4000000000000) 0 (IntervalRat.scale (559 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-29685243038 / 1000000000000) (-29685159890 / 1000000000000), orderedInterval (18568964195 / 1000000000000) (18569047343 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1388560002220313 / 4000000000000) 0 (IntervalRat.scale (559 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (30472752704 / 1000000000000) (30472778197 / 1000000000000), orderedInterval (-30132268783 / 1000000000000) (-30132243290 / 1000000000000)))) (orderedInterval (-3229108267 / 1000000000000) (-3229096637 / 1000000000000))) = true
  rfl'

theorem compactCertificate408_chunkChecks0 :
    compactCertificate408.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate408.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate408_chunkChecks0_0
    compactCertificate408_chunkChecks0_1 compactCertificate408_chunkChecks0_2

theorem compactCertificate408_chunkChecks1_0 :
    compactCertificate408.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (559 / 2) 1 (IntervalRat.scale (559 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-30128119829 / 1000000000000) (-30128119828 / 1000000000000), orderedInterval (-36959702807 / 1000000000000) (-36959702806 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (823513739876659 / 4000000000000) 1 (IntervalRat.scale (559 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-35047289049 / 1000000000000) (-35047271296 / 1000000000000), orderedInterval (43258038396 / 1000000000000) (43258056149 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (266307423318547 / 800000000000) 1 (IntervalRat.scale (559 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (26829043396 / 1000000000000) (26829043397 / 1000000000000), orderedInterval (34494302896 / 1000000000000) (34494302897 / 1000000000000)))) (orderedInterval (-11941845781 / 1000000000000) (-11941845636 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (240299255423513 / 4000000000000) 1 (IntervalRat.scale (559 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-94696824615 / 1000000000000) (-94696824614 / 1000000000000), orderedInterval (-39577394432 / 1000000000000) (-39577394431 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (645477600953861 / 4000000000000) 1 (IntervalRat.scale (559 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-58739214391 / 1000000000000) (-58739209683 / 1000000000000), orderedInterval (22426079267 / 1000000000000) (22426083976 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1752597249865137 / 4000000000000) 1 (IntervalRat.scale (559 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29585443434 / 1000000000000) (-29585402956 / 1000000000000), orderedInterval (24068653006 / 1000000000000) (24068693484 / 1000000000000)))) (orderedInterval (-2117215234 / 1000000000000) (-2117210585 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1290955201908281 / 4000000000000) 1 (IntervalRat.scale (559 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (2673491309 / 1000000000000) (2673491312 / 1000000000000), orderedInterval (-44337075249 / 1000000000000) (-44337075246 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2212073742096413 / 4000000000000) 1 (IntervalRat.scale (559 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (26221555575 / 1000000000000) (26221555576 / 1000000000000), orderedInterval (21507727888 / 1000000000000) (21507727889 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1629403506471767 / 4000000000000) 1 (IntervalRat.scale (559 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-10585621589 / 1000000000000) (-10585621549 / 1000000000000), orderedInterval (38102028993 / 1000000000000) (38102029033 / 1000000000000)))) (orderedInterval (29501292 / 1000000000000) (29501321 / 1000000000000))) = true
  rfl'

theorem compactCertificate408_chunkChecks1_1 :
    compactCertificate408.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2499923998844441 / 4000000000000) 1 (IntervalRat.scale (559 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-17737106893 / 1000000000000) (-17737106892 / 1000000000000), orderedInterval (-26519143006 / 1000000000000) (-26519143005 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1443331793686289 / 4000000000000) 1 (IntervalRat.scale (559 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-13803347814 / 1000000000000) (-13803347813 / 1000000000000), orderedInterval (-39651706320 / 1000000000000) (-39651706319 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2561217595949701 / 4000000000000) 1 (IntervalRat.scale (559 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (6409566038 / 1000000000000) (6409566039 / 1000000000000), orderedInterval (30868336957 / 1000000000000) (30868336958 / 1000000000000)))) (orderedInterval (16796579806 / 1000000000000) (16796580036 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2393021710544569 / 4000000000000) 1 (IntervalRat.scale (559 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (27512480089 / 1000000000000) (27512534738 / 1000000000000), orderedInterval (-17549822262 / 1000000000000) (-17549767614 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1707773208986377 / 4000000000000) 1 (IntervalRat.scale (559 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (17550328074 / 1000000000000) (17550328075 / 1000000000000), orderedInterval (34375629382 / 1000000000000) (34375629383 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1936432802861583 / 4000000000000) 1 (IntervalRat.scale (559 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (32119727187 / 1000000000000) (32119727188 / 1000000000000), orderedInterval (16800092125 / 1000000000000) (16800092126 / 1000000000000)))) (orderedInterval (5496359349 / 1000000000000) (5496361515 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1614395787757727 / 4000000000000) 1 (IntervalRat.scale (559 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (30646423255 / 1000000000000) (30646467659 / 1000000000000), orderedInterval (-25299668056 / 1000000000000) (-25299623653 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1426367638196267 / 4000000000000) 1 (IntervalRat.scale (559 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-29249511063 / 1000000000000) (-29249492171 / 1000000000000), orderedInterval (30532905922 / 1000000000000) (30532924814 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (413416936898433 / 800000000000) 1 (IntervalRat.scale (559 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (25335701169 / 1000000000000) (25335714108 / 1000000000000), orderedInterval (-24314847300 / 1000000000000) (-24314834362 / 1000000000000)))) (orderedInterval (-3802159800 / 1000000000000) (-3802157028 / 1000000000000))) = true
  rfl'

theorem compactCertificate408_chunkChecks1_2 :
    compactCertificate408.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1143533004402451 / 4000000000000) 1 (IntervalRat.scale (559 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-33297279893 / 1000000000000) (-33297279892 / 1000000000000), orderedInterval (-33380416506 / 1000000000000) (-33380416505 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (969385592113211 / 4000000000000) 1 (IntervalRat.scale (559 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-48282365681 / 1000000000000) (-48282365680 / 1000000000000), orderedInterval (-17096574945 / 1000000000000) (-17096574944 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (606596493528233 / 4000000000000) 1 (IntervalRat.scale (559 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (64648623532 / 1000000000000) (64648623656 / 1000000000000), orderedInterval (-4515641702 / 1000000000000) (-4515641577 / 1000000000000)))) (orderedInterval (6218441828 / 1000000000000) (6218441896 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (326229611668311 / 4000000000000) 1 (IntervalRat.scale (559 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (54158787532 / 1000000000000) (54158787533 / 1000000000000), orderedInterval (69472352377 / 1000000000000) (69472352378 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (885776856377933 / 4000000000000) 1 (IntervalRat.scale (559 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (39349367722 / 1000000000000) (39349427986 / 1000000000000), orderedInterval (-36509723901 / 1000000000000) (-36509663637 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1209452569991341 / 4000000000000) 1 (IntervalRat.scale (559 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (45879928944 / 1000000000000) (45879929058 / 1000000000000), orderedInterval (638256737 / 1000000000000) (638256852 / 1000000000000)))) (orderedInterval (229004327 / 1000000000000) (229005450 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (511403506471767 / 4000000000000) 1 (IntervalRat.scale (559 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (11938392733 / 1000000000000) (11938392804 / 1000000000000), orderedInterval (-69594540431 / 1000000000000) (-69594540360 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2078826861534007 / 4000000000000) 1 (IntervalRat.scale (559 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-29685243038 / 1000000000000) (-29685159890 / 1000000000000), orderedInterval (18568964195 / 1000000000000) (18569047343 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1388560002220313 / 4000000000000) 1 (IntervalRat.scale (559 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (30472752704 / 1000000000000) (30472778197 / 1000000000000), orderedInterval (-30132268783 / 1000000000000) (-30132243290 / 1000000000000)))) (orderedInterval (4019286771 / 1000000000000) (4019305406 / 1000000000000))) = true
  rfl'

theorem compactCertificate408_chunkChecks1 :
    compactCertificate408.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate408.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate408_chunkChecks1_0
    compactCertificate408_chunkChecks1_1 compactCertificate408_chunkChecks1_2

theorem compactCertificate408_chunkChecks2_0 :
    compactCertificate408.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (559 / 2) 2 (IntervalRat.scale (559 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-30128119829 / 1000000000000) (-30128119828 / 1000000000000), orderedInterval (-36959702807 / 1000000000000) (-36959702806 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (823513739876659 / 4000000000000) 2 (IntervalRat.scale (559 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-35047289049 / 1000000000000) (-35047271296 / 1000000000000), orderedInterval (43258038396 / 1000000000000) (43258056149 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (266307423318547 / 800000000000) 2 (IntervalRat.scale (559 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (26829043396 / 1000000000000) (26829043397 / 1000000000000), orderedInterval (34494302896 / 1000000000000) (34494302897 / 1000000000000)))) (orderedInterval (9928452009 / 1000000000000) (9928452125 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (240299255423513 / 4000000000000) 2 (IntervalRat.scale (559 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-94696824615 / 1000000000000) (-94696824614 / 1000000000000), orderedInterval (-39577394432 / 1000000000000) (-39577394431 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (645477600953861 / 4000000000000) 2 (IntervalRat.scale (559 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-58739214391 / 1000000000000) (-58739209683 / 1000000000000), orderedInterval (22426079267 / 1000000000000) (22426083976 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1752597249865137 / 4000000000000) 2 (IntervalRat.scale (559 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29585443434 / 1000000000000) (-29585402956 / 1000000000000), orderedInterval (24068653006 / 1000000000000) (24068693484 / 1000000000000)))) (orderedInterval (-4493504260 / 1000000000000) (-4493497061 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1290955201908281 / 4000000000000) 2 (IntervalRat.scale (559 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (2673491309 / 1000000000000) (2673491312 / 1000000000000), orderedInterval (-44337075249 / 1000000000000) (-44337075246 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2212073742096413 / 4000000000000) 2 (IntervalRat.scale (559 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (26221555575 / 1000000000000) (26221555576 / 1000000000000), orderedInterval (21507727888 / 1000000000000) (21507727889 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1629403506471767 / 4000000000000) 2 (IntervalRat.scale (559 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-10585621589 / 1000000000000) (-10585621549 / 1000000000000), orderedInterval (38102028993 / 1000000000000) (38102029033 / 1000000000000)))) (orderedInterval (3709555690 / 1000000000000) (3709555742 / 1000000000000))) = true
  rfl'

theorem compactCertificate408_chunkChecks2_1 :
    compactCertificate408.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2499923998844441 / 4000000000000) 2 (IntervalRat.scale (559 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-17737106893 / 1000000000000) (-17737106892 / 1000000000000), orderedInterval (-26519143006 / 1000000000000) (-26519143005 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1443331793686289 / 4000000000000) 2 (IntervalRat.scale (559 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-13803347814 / 1000000000000) (-13803347813 / 1000000000000), orderedInterval (-39651706320 / 1000000000000) (-39651706319 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2561217595949701 / 4000000000000) 2 (IntervalRat.scale (559 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (6409566038 / 1000000000000) (6409566039 / 1000000000000), orderedInterval (30868336957 / 1000000000000) (30868336958 / 1000000000000)))) (orderedInterval (-18895845741 / 1000000000000) (-18895845247 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2393021710544569 / 4000000000000) 2 (IntervalRat.scale (559 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (27512480089 / 1000000000000) (27512534738 / 1000000000000), orderedInterval (-17549822262 / 1000000000000) (-17549767614 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1707773208986377 / 4000000000000) 2 (IntervalRat.scale (559 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (17550328074 / 1000000000000) (17550328075 / 1000000000000), orderedInterval (34375629382 / 1000000000000) (34375629383 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1936432802861583 / 4000000000000) 2 (IntervalRat.scale (559 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (32119727187 / 1000000000000) (32119727188 / 1000000000000), orderedInterval (16800092125 / 1000000000000) (16800092126 / 1000000000000)))) (orderedInterval (-1128880339 / 1000000000000) (-1128875721 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1614395787757727 / 4000000000000) 2 (IntervalRat.scale (559 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (30646423255 / 1000000000000) (30646467659 / 1000000000000), orderedInterval (-25299668056 / 1000000000000) (-25299623653 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1426367638196267 / 4000000000000) 2 (IntervalRat.scale (559 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-29249511063 / 1000000000000) (-29249492171 / 1000000000000), orderedInterval (30532905922 / 1000000000000) (30532924814 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (413416936898433 / 800000000000) 2 (IntervalRat.scale (559 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (25335701169 / 1000000000000) (25335714108 / 1000000000000), orderedInterval (-24314847300 / 1000000000000) (-24314834362 / 1000000000000)))) (orderedInterval (-5666428689 / 1000000000000) (-5666424659 / 1000000000000))) = true
  rfl'

theorem compactCertificate408_chunkChecks2_2 :
    compactCertificate408.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1143533004402451 / 4000000000000) 2 (IntervalRat.scale (559 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-33297279893 / 1000000000000) (-33297279892 / 1000000000000), orderedInterval (-33380416506 / 1000000000000) (-33380416505 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (969385592113211 / 4000000000000) 2 (IntervalRat.scale (559 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-48282365681 / 1000000000000) (-48282365680 / 1000000000000), orderedInterval (-17096574945 / 1000000000000) (-17096574944 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (606596493528233 / 4000000000000) 2 (IntervalRat.scale (559 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (64648623532 / 1000000000000) (64648623656 / 1000000000000), orderedInterval (-4515641702 / 1000000000000) (-4515641577 / 1000000000000)))) (orderedInterval (-8266305159 / 1000000000000) (-8266305095 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (326229611668311 / 4000000000000) 2 (IntervalRat.scale (559 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (54158787532 / 1000000000000) (54158787533 / 1000000000000), orderedInterval (69472352377 / 1000000000000) (69472352378 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (885776856377933 / 4000000000000) 2 (IntervalRat.scale (559 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (39349367722 / 1000000000000) (39349427986 / 1000000000000), orderedInterval (-36509723901 / 1000000000000) (-36509663637 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1209452569991341 / 4000000000000) 2 (IntervalRat.scale (559 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (45879928944 / 1000000000000) (45879929058 / 1000000000000), orderedInterval (638256737 / 1000000000000) (638256852 / 1000000000000)))) (orderedInterval (4759666319 / 1000000000000) (4759667221 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (511403506471767 / 4000000000000) 2 (IntervalRat.scale (559 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (11938392733 / 1000000000000) (11938392804 / 1000000000000), orderedInterval (-69594540431 / 1000000000000) (-69594540360 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2078826861534007 / 4000000000000) 2 (IntervalRat.scale (559 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-29685243038 / 1000000000000) (-29685159890 / 1000000000000), orderedInterval (18568964195 / 1000000000000) (18569047343 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1388560002220313 / 4000000000000) 2 (IntervalRat.scale (559 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (30472752704 / 1000000000000) (30472778197 / 1000000000000), orderedInterval (-30132268783 / 1000000000000) (-30132243290 / 1000000000000)))) (orderedInterval (435580532 / 1000000000000) (435611539 / 1000000000000))) = true
  rfl'

theorem compactCertificate408_chunkChecks2 :
    compactCertificate408.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate408.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate408_chunkChecks2_0
    compactCertificate408_chunkChecks2_1 compactCertificate408_chunkChecks2_2

theorem compactCertificate408_chunkChecks3_0 :
    compactCertificate408.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (559 / 2) 3 (IntervalRat.scale (559 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-30128119829 / 1000000000000) (-30128119828 / 1000000000000), orderedInterval (-36959702807 / 1000000000000) (-36959702806 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (823513739876659 / 4000000000000) 3 (IntervalRat.scale (559 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-35047289049 / 1000000000000) (-35047271296 / 1000000000000), orderedInterval (43258038396 / 1000000000000) (43258056149 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (266307423318547 / 800000000000) 3 (IntervalRat.scale (559 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (26829043396 / 1000000000000) (26829043397 / 1000000000000), orderedInterval (34494302896 / 1000000000000) (34494302897 / 1000000000000)))) (orderedInterval (11033123593 / 1000000000000) (11033123690 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (240299255423513 / 4000000000000) 3 (IntervalRat.scale (559 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-94696824615 / 1000000000000) (-94696824614 / 1000000000000), orderedInterval (-39577394432 / 1000000000000) (-39577394431 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (645477600953861 / 4000000000000) 3 (IntervalRat.scale (559 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-58739214391 / 1000000000000) (-58739209683 / 1000000000000), orderedInterval (22426079267 / 1000000000000) (22426083976 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1752597249865137 / 4000000000000) 3 (IntervalRat.scale (559 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29585443434 / 1000000000000) (-29585402956 / 1000000000000), orderedInterval (24068653006 / 1000000000000) (24068693484 / 1000000000000)))) (orderedInterval (6445626361 / 1000000000000) (6445637584 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1290955201908281 / 4000000000000) 3 (IntervalRat.scale (559 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (2673491309 / 1000000000000) (2673491312 / 1000000000000), orderedInterval (-44337075249 / 1000000000000) (-44337075246 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2212073742096413 / 4000000000000) 3 (IntervalRat.scale (559 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (26221555575 / 1000000000000) (26221555576 / 1000000000000), orderedInterval (21507727888 / 1000000000000) (21507727889 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1629403506471767 / 4000000000000) 3 (IntervalRat.scale (559 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-10585621589 / 1000000000000) (-10585621549 / 1000000000000), orderedInterval (38102028993 / 1000000000000) (38102029033 / 1000000000000)))) (orderedInterval (2274566166 / 1000000000000) (2274566258 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate408_chunkChecks3_1 :
    compactCertificate408.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2499923998844441 / 4000000000000) 3 (IntervalRat.scale (559 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-17737106893 / 1000000000000) (-17737106892 / 1000000000000), orderedInterval (-26519143006 / 1000000000000) (-26519143005 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1443331793686289 / 4000000000000) 3 (IntervalRat.scale (559 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-13803347814 / 1000000000000) (-13803347813 / 1000000000000), orderedInterval (-39651706320 / 1000000000000) (-39651706319 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2561217595949701 / 4000000000000) 3 (IntervalRat.scale (559 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (6409566038 / 1000000000000) (6409566039 / 1000000000000), orderedInterval (30868336957 / 1000000000000) (30868336958 / 1000000000000)))) (orderedInterval (-99052593140 / 1000000000000) (-99052592058 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2393021710544569 / 4000000000000) 3 (IntervalRat.scale (559 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (27512480089 / 1000000000000) (27512534738 / 1000000000000), orderedInterval (-17549822262 / 1000000000000) (-17549767614 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1707773208986377 / 4000000000000) 3 (IntervalRat.scale (559 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (17550328074 / 1000000000000) (17550328075 / 1000000000000), orderedInterval (34375629382 / 1000000000000) (34375629383 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1936432802861583 / 4000000000000) 3 (IntervalRat.scale (559 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (32119727187 / 1000000000000) (32119727188 / 1000000000000), orderedInterval (16800092125 / 1000000000000) (16800092126 / 1000000000000)))) (orderedInterval (-14247183553 / 1000000000000) (-14247173709 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1614395787757727 / 4000000000000) 3 (IntervalRat.scale (559 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (30646423255 / 1000000000000) (30646467659 / 1000000000000), orderedInterval (-25299668056 / 1000000000000) (-25299623653 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1426367638196267 / 4000000000000) 3 (IntervalRat.scale (559 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-29249511063 / 1000000000000) (-29249492171 / 1000000000000), orderedInterval (30532905922 / 1000000000000) (30532924814 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (413416936898433 / 800000000000) 3 (IntervalRat.scale (559 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (25335701169 / 1000000000000) (25335714108 / 1000000000000), orderedInterval (-24314847300 / 1000000000000) (-24314834362 / 1000000000000)))) (orderedInterval (8463298115 / 1000000000000) (8463304101 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate408_chunkChecks3_2 :
    compactCertificate408.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1143533004402451 / 4000000000000) 3 (IntervalRat.scale (559 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-33297279893 / 1000000000000) (-33297279892 / 1000000000000), orderedInterval (-33380416506 / 1000000000000) (-33380416505 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (969385592113211 / 4000000000000) 3 (IntervalRat.scale (559 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-48282365681 / 1000000000000) (-48282365680 / 1000000000000), orderedInterval (-17096574945 / 1000000000000) (-17096574944 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (606596493528233 / 4000000000000) 3 (IntervalRat.scale (559 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (64648623532 / 1000000000000) (64648623656 / 1000000000000), orderedInterval (-4515641702 / 1000000000000) (-4515641577 / 1000000000000)))) (orderedInterval (-6289032174 / 1000000000000) (-6289032113 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (326229611668311 / 4000000000000) 3 (IntervalRat.scale (559 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (54158787532 / 1000000000000) (54158787533 / 1000000000000), orderedInterval (69472352377 / 1000000000000) (69472352378 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (885776856377933 / 4000000000000) 3 (IntervalRat.scale (559 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (39349367722 / 1000000000000) (39349427986 / 1000000000000), orderedInterval (-36509723901 / 1000000000000) (-36509663637 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1209452569991341 / 4000000000000) 3 (IntervalRat.scale (559 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (45879928944 / 1000000000000) (45879929058 / 1000000000000), orderedInterval (638256737 / 1000000000000) (638256852 / 1000000000000)))) (orderedInterval (-335163313 / 1000000000000) (-335162588 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (511403506471767 / 4000000000000) 3 (IntervalRat.scale (559 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (11938392733 / 1000000000000) (11938392804 / 1000000000000), orderedInterval (-69594540431 / 1000000000000) (-69594540360 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2078826861534007 / 4000000000000) 3 (IntervalRat.scale (559 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-29685243038 / 1000000000000) (-29685159890 / 1000000000000), orderedInterval (18568964195 / 1000000000000) (18569047343 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1388560002220313 / 4000000000000) 3 (IntervalRat.scale (559 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (30472752704 / 1000000000000) (30472778197 / 1000000000000), orderedInterval (-30132268783 / 1000000000000) (-30132243290 / 1000000000000)))) (orderedInterval (-1075579187 / 1000000000000) (-1075526153 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate408_chunkChecks3 :
    compactCertificate408.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate408.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate408_chunkChecks3_0
    compactCertificate408_chunkChecks3_1 compactCertificate408_chunkChecks3_2

theorem compactCertificate408_chunkChecks4_0 :
    compactCertificate408.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (559 / 2) 4 (IntervalRat.scale (559 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-30128119829 / 1000000000000) (-30128119828 / 1000000000000), orderedInterval (-36959702807 / 1000000000000) (-36959702806 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (823513739876659 / 4000000000000) 4 (IntervalRat.scale (559 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-35047289049 / 1000000000000) (-35047271296 / 1000000000000), orderedInterval (43258038396 / 1000000000000) (43258056149 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (266307423318547 / 800000000000) 4 (IntervalRat.scale (559 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (26829043396 / 1000000000000) (26829043397 / 1000000000000), orderedInterval (34494302896 / 1000000000000) (34494302897 / 1000000000000)))) (orderedInterval (-8948950926 / 1000000000000) (-8948950841 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (240299255423513 / 4000000000000) 4 (IntervalRat.scale (559 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-94696824615 / 1000000000000) (-94696824614 / 1000000000000), orderedInterval (-39577394432 / 1000000000000) (-39577394431 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (645477600953861 / 4000000000000) 4 (IntervalRat.scale (559 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-58739214391 / 1000000000000) (-58739209683 / 1000000000000), orderedInterval (22426079267 / 1000000000000) (22426083976 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1752597249865137 / 4000000000000) 4 (IntervalRat.scale (559 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-29585443434 / 1000000000000) (-29585402956 / 1000000000000), orderedInterval (24068653006 / 1000000000000) (24068693484 / 1000000000000)))) (orderedInterval (12418925850 / 1000000000000) (12418943448 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1290955201908281 / 4000000000000) 4 (IntervalRat.scale (559 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (2673491309 / 1000000000000) (2673491312 / 1000000000000), orderedInterval (-44337075249 / 1000000000000) (-44337075246 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2212073742096413 / 4000000000000) 4 (IntervalRat.scale (559 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (26221555575 / 1000000000000) (26221555576 / 1000000000000), orderedInterval (21507727888 / 1000000000000) (21507727889 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1629403506471767 / 4000000000000) 4 (IntervalRat.scale (559 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-10585621589 / 1000000000000) (-10585621549 / 1000000000000), orderedInterval (38102028993 / 1000000000000) (38102029033 / 1000000000000)))) (orderedInterval (-13565886367 / 1000000000000) (-13565886198 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate408_chunkChecks4_1 :
    compactCertificate408.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2499923998844441 / 4000000000000) 4 (IntervalRat.scale (559 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-17737106893 / 1000000000000) (-17737106892 / 1000000000000), orderedInterval (-26519143006 / 1000000000000) (-26519143005 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1443331793686289 / 4000000000000) 4 (IntervalRat.scale (559 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-13803347814 / 1000000000000) (-13803347813 / 1000000000000), orderedInterval (-39651706320 / 1000000000000) (-39651706319 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2561217595949701 / 4000000000000) 4 (IntervalRat.scale (559 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (6409566038 / 1000000000000) (6409566039 / 1000000000000), orderedInterval (30868336957 / 1000000000000) (30868336958 / 1000000000000)))) (orderedInterval (101755853930 / 1000000000000) (101755856333 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2393021710544569 / 4000000000000) 4 (IntervalRat.scale (559 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (27512480089 / 1000000000000) (27512534738 / 1000000000000), orderedInterval (-17549822262 / 1000000000000) (-17549767614 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1707773208986377 / 4000000000000) 4 (IntervalRat.scale (559 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (17550328074 / 1000000000000) (17550328075 / 1000000000000), orderedInterval (34375629382 / 1000000000000) (34375629383 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1936432802861583 / 4000000000000) 4 (IntervalRat.scale (559 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (32119727187 / 1000000000000) (32119727188 / 1000000000000), orderedInterval (16800092125 / 1000000000000) (16800092126 / 1000000000000)))) (orderedInterval (-2750923489 / 1000000000000) (-2750902448 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1614395787757727 / 4000000000000) 4 (IntervalRat.scale (559 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (30646423255 / 1000000000000) (30646467659 / 1000000000000), orderedInterval (-25299668056 / 1000000000000) (-25299623653 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1426367638196267 / 4000000000000) 4 (IntervalRat.scale (559 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-29249511063 / 1000000000000) (-29249492171 / 1000000000000), orderedInterval (30532905922 / 1000000000000) (30532924814 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (413416936898433 / 800000000000) 4 (IntervalRat.scale (559 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (25335701169 / 1000000000000) (25335714108 / 1000000000000), orderedInterval (-24314847300 / 1000000000000) (-24314834362 / 1000000000000)))) (orderedInterval (13493496147 / 1000000000000) (13493505296 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate408_chunkChecks4_2 :
    compactCertificate408.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1143533004402451 / 4000000000000) 4 (IntervalRat.scale (559 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-33297279893 / 1000000000000) (-33297279892 / 1000000000000), orderedInterval (-33380416506 / 1000000000000) (-33380416505 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (969385592113211 / 4000000000000) 4 (IntervalRat.scale (559 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-48282365681 / 1000000000000) (-48282365680 / 1000000000000), orderedInterval (-17096574945 / 1000000000000) (-17096574944 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (606596493528233 / 4000000000000) 4 (IntervalRat.scale (559 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (64648623532 / 1000000000000) (64648623656 / 1000000000000), orderedInterval (-4515641702 / 1000000000000) (-4515641577 / 1000000000000)))) (orderedInterval (7599176663 / 1000000000000) (7599176723 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (326229611668311 / 4000000000000) 4 (IntervalRat.scale (559 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (54158787532 / 1000000000000) (54158787533 / 1000000000000), orderedInterval (69472352377 / 1000000000000) (69472352378 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (885776856377933 / 4000000000000) 4 (IntervalRat.scale (559 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (39349367722 / 1000000000000) (39349427986 / 1000000000000), orderedInterval (-36509723901 / 1000000000000) (-36509663637 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1209452569991341 / 4000000000000) 4 (IntervalRat.scale (559 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (45879928944 / 1000000000000) (45879929058 / 1000000000000), orderedInterval (638256737 / 1000000000000) (638256852 / 1000000000000)))) (orderedInterval (-5172254316 / 1000000000000) (-5172253727 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (511403506471767 / 4000000000000) 4 (IntervalRat.scale (559 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (11938392733 / 1000000000000) (11938392804 / 1000000000000), orderedInterval (-69594540431 / 1000000000000) (-69594540360 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2078826861534007 / 4000000000000) 4 (IntervalRat.scale (559 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-29685243038 / 1000000000000) (-29685159890 / 1000000000000), orderedInterval (18568964195 / 1000000000000) (18569047343 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1388560002220313 / 4000000000000) 4 (IntervalRat.scale (559 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (30472752704 / 1000000000000) (30472778197 / 1000000000000), orderedInterval (-30132268783 / 1000000000000) (-30132243290 / 1000000000000)))) (orderedInterval (15291342937 / 1000000000000) (15291436001 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate408_chunkChecks4 :
    compactCertificate408.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate408.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate408_chunkChecks4_0
    compactCertificate408_chunkChecks4_1 compactCertificate408_chunkChecks4_2

theorem compactCertificate408_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate408.chunkCheck r b = true :=
  compactCertificate408.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate408_chunkChecks0
    · exact compactCertificate408_chunkChecks1
    · exact compactCertificate408_chunkChecks2
    · exact compactCertificate408_chunkChecks3
    · exact compactCertificate408_chunkChecks4)

theorem compactCertificate408_coefficient0 :
    compactCertificate408.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate408_coefficient1 :
    compactCertificate408.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate408_coefficient2 :
    compactCertificate408.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate408_coefficient3 :
    compactCertificate408.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate408_coefficient4 :
    compactCertificate408.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate408_coefficients : ∀ r : Fin 5,
    compactCertificate408.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate408_coefficient0
  · exact compactCertificate408_coefficient1
  · exact compactCertificate408_coefficient2
  · exact compactCertificate408_coefficient3
  · exact compactCertificate408_coefficient4

theorem compactCertificate408_lower : (1 : ℚ) ≤ compactCertificate408.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate408, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate408_proves {t : ℝ} (ht : t ∈ compactCertificate408.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate408.proves compactCertificate408_states compactCertificate408_chunks
    compactCertificate408_coefficients compactCertificate408_lower ht

end Erdos232
