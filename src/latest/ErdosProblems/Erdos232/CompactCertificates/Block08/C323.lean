/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate323 : CompactCertificate where
  left := 195
  right := 196
  center := 391 / 2
  grid := fun i =>
    match i.val with
    | 0 => 62
    | 1 => 46
    | 2 => 74
    | 3 => 13
    | 4 => 36
    | 5 => 98
    | 6 => 72
    | 7 => 123
    | 8 => 91
    | 9 => 139
    | 10 => 80
    | 11 => 143
    | 12 => 133
    | 13 => 95
    | 14 => 108
    | 15 => 90
    | 16 => 79
    | 17 => 115
    | 18 => 64
    | 19 => 54
    | 20 => 34
    | 21 => 18
    | 22 => 49
    | 23 => 67
    | 24 => 28
    | 25 => 116
    | _ => 77
  point := fun i =>
    match i.val with
    | 0 => 391 / 2
    | 1 => 576017660629291 / 4000000000000
    | 2 => 186272276417803 / 800000000000
    | 3 => 168080516763137 / 4000000000000
    | 4 => 451487910506189 / 4000000000000
    | 5 => 1225877503930713 / 4000000000000
    | 6 => 902975821012769 / 4000000000000
    | 7 => 1547264460035237 / 4000000000000
    | 8 => 1139707998265583 / 4000000000000
    | 9 => 1748605158404609 / 4000000000000
    | 10 => 1009557658911161 / 4000000000000
    | 11 => 1791477781782349 / 4000000000000
    | 12 => 1673830928126881 / 4000000000000
    | 13 => 1194524731151473 / 4000000000000
    | 14 => 1354463731518567 / 4000000000000
    | 15 => 1129210649397623 / 4000000000000
    | 16 => 997691854266083 / 4000000000000
    | 17 => 289169986274217 / 800000000000
    | 18 => 799859400217099 / 4000000000000
    | 19 => 678049671764339 / 4000000000000
    | 20 => 424292001734417 / 4000000000000
    | 21 => 228185649664239 / 4000000000000
    | 22 => 619568427269717 / 4000000000000
    | 23 => 845967718902709 / 4000000000000
    | 24 => 357707998265583 / 4000000000000
    | 25 => 1454063153595343 / 4000000000000
    | _ => 971246799406337 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (56944794102 / 1000000000000) (56944794127 / 1000000000000), orderedInterval (3548544668 / 1000000000000) (3548544693 / 1000000000000))
    | 1 => (orderedInterval (18098645271 / 1000000000000) (18098645272 / 1000000000000), orderedInterval (63916038177 / 1000000000000) (63916038178 / 1000000000000))
    | 2 => (orderedInterval (47670765735 / 1000000000000) (47670765736 / 1000000000000), orderedInterval (21383467221 / 1000000000000) (21383467222 / 1000000000000))
    | 3 => (orderedInterval (-113790722037 / 1000000000000) (-113790718595 / 1000000000000), orderedInterval (48271442941 / 1000000000000) (48271446383 / 1000000000000))
    | 4 => (orderedInterval (39824611448 / 1000000000000) (39824611449 / 1000000000000), orderedInterval (63496328663 / 1000000000000) (63496328664 / 1000000000000))
    | 5 => (orderedInterval (-26545404673 / 1000000000000) (-26545398791 / 1000000000000), orderedInterval (37092096890 / 1000000000000) (37092102771 / 1000000000000))
    | 6 => (orderedInterval (17415420488 / 1000000000000) (17415420489 / 1000000000000), orderedInterval (50129197429 / 1000000000000) (50129197430 / 1000000000000))
    | 7 => (orderedInterval (-37591041648 / 1000000000000) (-37591041647 / 1000000000000), orderedInterval (-15206144789 / 1000000000000) (-15206144788 / 1000000000000))
    | 8 => (orderedInterval (8135459005 / 1000000000000) (8135459028 / 1000000000000), orderedInterval (-46577603502 / 1000000000000) (-46577603479 / 1000000000000))
    | 9 => (orderedInterval (-36274544875 / 1000000000000) (-36274544872 / 1000000000000), orderedInterval (-11809597839 / 1000000000000) (-11809597835 / 1000000000000))
    | 10 => (orderedInterval (48320882304 / 1000000000000) (48320885368 / 1000000000000), orderedInterval (-13787298079 / 1000000000000) (-13787295016 / 1000000000000))
    | 11 => (orderedInterval (21075585546 / 1000000000000) (21075587536 / 1000000000000), orderedInterval (-31284695533 / 1000000000000) (-31284693544 / 1000000000000))
    | 12 => (orderedInterval (-38507570699 / 1000000000000) (-38507570665 / 1000000000000), orderedInterval (-6159939354 / 1000000000000) (-6159939320 / 1000000000000))
    | 13 => (orderedInterval (-37951400334 / 1000000000000) (-37951400333 / 1000000000000), orderedInterval (-26232519464 / 1000000000000) (-26232519463 / 1000000000000))
    | 14 => (orderedInterval (4714926306 / 1000000000000) (4714926307 / 1000000000000), orderedInterval (43095658593 / 1000000000000) (43095658594 / 1000000000000))
    | 15 => (orderedInterval (16027993348 / 1000000000000) (16027993349 / 1000000000000), orderedInterval (44672873346 / 1000000000000) (44672873347 / 1000000000000))
    | 16 => (orderedInterval (-45464055629 / 1000000000000) (-45464037638 / 1000000000000), orderedInterval (22122642312 / 1000000000000) (22122660304 / 1000000000000))
    | 17 => (orderedInterval (-34484129959 / 1000000000000) (-34484129958 / 1000000000000), orderedInterval (-23870441333 / 1000000000000) (-23870441332 / 1000000000000))
    | 18 => (orderedInterval (-17336480130 / 1000000000000) (-17336479828 / 1000000000000), orderedInterval (53737974972 / 1000000000000) (53737975274 / 1000000000000))
    | 19 => (orderedInterval (37139940735 / 1000000000000) (37139940736 / 1000000000000), orderedInterval (48636968008 / 1000000000000) (48636968009 / 1000000000000))
    | 20 => (orderedInterval (3335613877 / 1000000000000) (3335613881 / 1000000000000), orderedInterval (77383590643 / 1000000000000) (77383590647 / 1000000000000))
    | 21 => (orderedInterval (101231057447 / 1000000000000) (101231057448 / 1000000000000), orderedInterval (29305442028 / 1000000000000) (29305442029 / 1000000000000))
    | 22 => (orderedInterval (-63208671605 / 1000000000000) (-63208671120 / 1000000000000), orderedInterval (10915198784 / 1000000000000) (10915199270 / 1000000000000))
    | 23 => (orderedInterval (-53551436136 / 1000000000000) (-53551434860 / 1000000000000), orderedInterval (12058641842 / 1000000000000) (12058643119 / 1000000000000))
    | 24 => (orderedInterval (65838235084 / 1000000000000) (65838301493 / 1000000000000), orderedInterval (-53133409159 / 1000000000000) (-53133342750 / 1000000000000))
    | 25 => (orderedInterval (-5171965750 / 1000000000000) (-5171965744 / 1000000000000), orderedInterval (41534664226 / 1000000000000) (41534664231 / 1000000000000))
    | _ => (orderedInterval (-50816302814 / 1000000000000) (-50816302331 / 1000000000000), orderedInterval (6394643336 / 1000000000000) (6394643819 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (25536942049 / 1000000000000) (25536942073 / 1000000000000)
      | 1 => orderedInterval (4575717575 / 1000000000000) (4575718055 / 1000000000000)
      | 2 => orderedInterval (1356076113 / 1000000000000) (1356076126 / 1000000000000)
      | 3 => orderedInterval (13021747015 / 1000000000000) (13021747603 / 1000000000000)
      | 4 => orderedInterval (-2917472954 / 1000000000000) (-2917472930 / 1000000000000)
      | 5 => orderedInterval (1903911826 / 1000000000000) (1903912875 / 1000000000000)
      | 6 => orderedInterval (778444873 / 1000000000000) (778444971 / 1000000000000)
      | 7 => orderedInterval (3668884522 / 1000000000000) (3668884654 / 1000000000000)
      | _ => orderedInterval (10352387972 / 1000000000000) (10352388518 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (3339688836 / 1000000000000) (3339688862 / 1000000000000)
      | 1 => orderedInterval (-2907654571 / 1000000000000) (-2907653880 / 1000000000000)
      | 2 => orderedInterval (-712610098 / 1000000000000) (-712610077 / 1000000000000)
      | 3 => orderedInterval (-6814861308 / 1000000000000) (-6814860205 / 1000000000000)
      | 4 => orderedInterval (-3928923472 / 1000000000000) (-3928923432 / 1000000000000)
      | 5 => orderedInterval (-2000296808 / 1000000000000) (-2000295466 / 1000000000000)
      | 6 => orderedInterval (-9808571671 / 1000000000000) (-9808571576 / 1000000000000)
      | 7 => orderedInterval (-1353852519 / 1000000000000) (-1353852382 / 1000000000000)
      | _ => orderedInterval (-7923354780 / 1000000000000) (-7923354406 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-26647525397 / 1000000000000) (-26647525368 / 1000000000000)
      | 1 => orderedInterval (-5164268009 / 1000000000000) (-5164266939 / 1000000000000)
      | 2 => orderedInterval (-4953099542 / 1000000000000) (-4953099506 / 1000000000000)
      | 3 => orderedInterval (-53883520728 / 1000000000000) (-53883518512 / 1000000000000)
      | 4 => orderedInterval (5280544344 / 1000000000000) (5280544411 / 1000000000000)
      | 5 => orderedInterval (-1592350196 / 1000000000000) (-1592348472 / 1000000000000)
      | 6 => orderedInterval (-1301428035 / 1000000000000) (-1301427941 / 1000000000000)
      | 7 => orderedInterval (-5537088203 / 1000000000000) (-5537088059 / 1000000000000)
      | _ => orderedInterval (-16205759494 / 1000000000000) (-16205759154 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-3628031071 / 1000000000000) (-3628031040 / 1000000000000)
      | 1 => orderedInterval (9743381762 / 1000000000000) (9743383434 / 1000000000000)
      | 2 => orderedInterval (-122856832 / 1000000000000) (-122856768 / 1000000000000)
      | 3 => orderedInterval (32482405199 / 1000000000000) (32482409859 / 1000000000000)
      | 4 => orderedInterval (8857064719 / 1000000000000) (8857064832 / 1000000000000)
      | 5 => orderedInterval (4946851488 / 1000000000000) (4946853698 / 1000000000000)
      | 6 => orderedInterval (10593065240 / 1000000000000) (10593065335 / 1000000000000)
      | 7 => orderedInterval (1334894622 / 1000000000000) (1334894774 / 1000000000000)
      | _ => orderedInterval (24147752045 / 1000000000000) (24147752435 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (28285537511 / 1000000000000) (28285537546 / 1000000000000)
      | 1 => orderedInterval (11460502474 / 1000000000000) (11460505102 / 1000000000000)
      | 2 => orderedInterval (18658175400 / 1000000000000) (18658175518 / 1000000000000)
      | 3 => orderedInterval (253270707045 / 1000000000000) (253270717196 / 1000000000000)
      | 4 => orderedInterval (-5252127779 / 1000000000000) (-5252127581 / 1000000000000)
      | 5 => orderedInterval (-2670575577 / 1000000000000) (-2670572728 / 1000000000000)
      | 6 => orderedInterval (1746851451 / 1000000000000) (1746851547 / 1000000000000)
      | 7 => orderedInterval (6158622366 / 1000000000000) (6158622529 / 1000000000000)
      | _ => orderedInterval (27490161407 / 1000000000000) (27490161927 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (58276638991 / 1000000000000) (58276641945 / 1000000000000)
    | 1 => orderedInterval (-32110436391 / 1000000000000) (-32110432562 / 1000000000000)
    | 2 => orderedInterval (-110004495260 / 1000000000000) (-110004489540 / 1000000000000)
    | 3 => orderedInterval (88354527172 / 1000000000000) (88354536559 / 1000000000000)
    | _ => orderedInterval (339147854298 / 1000000000000) (339147871056 / 1000000000000)

theorem compactCertificate323_stateChecks0 :
    compactCertificate323.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (391 / 2)) (orderedInterval (56944794102 / 1000000000000) (56944794127 / 1000000000000), orderedInterval (3548544668 / 1000000000000) (3548544693 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (576017660629291 / 4000000000000)) (orderedInterval (18098645271 / 1000000000000) (18098645272 / 1000000000000), orderedInterval (63916038177 / 1000000000000) (63916038178 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 74 12 (186272276417803 / 800000000000)) (orderedInterval (47670765735 / 1000000000000) (47670765736 / 1000000000000), orderedInterval (21383467221 / 1000000000000) (21383467222 / 1000000000000))) = true
  rfl'

theorem compactCertificate323_stateChecks1 :
    compactCertificate323.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 13 12 (168080516763137 / 4000000000000)) (orderedInterval (-113790722037 / 1000000000000) (-113790718595 / 1000000000000), orderedInterval (48271442941 / 1000000000000) (48271446383 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 36 12 (451487910506189 / 4000000000000)) (orderedInterval (39824611448 / 1000000000000) (39824611449 / 1000000000000), orderedInterval (63496328663 / 1000000000000) (63496328664 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 98 12 (1225877503930713 / 4000000000000)) (orderedInterval (-26545404673 / 1000000000000) (-26545398791 / 1000000000000), orderedInterval (37092096890 / 1000000000000) (37092102771 / 1000000000000))) = true
  rfl'

theorem compactCertificate323_stateChecks2 :
    compactCertificate323.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 72 12 (902975821012769 / 4000000000000)) (orderedInterval (17415420488 / 1000000000000) (17415420489 / 1000000000000), orderedInterval (50129197429 / 1000000000000) (50129197430 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 123 12 (1547264460035237 / 4000000000000)) (orderedInterval (-37591041648 / 1000000000000) (-37591041647 / 1000000000000), orderedInterval (-15206144789 / 1000000000000) (-15206144788 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 91 12 (1139707998265583 / 4000000000000)) (orderedInterval (8135459005 / 1000000000000) (8135459028 / 1000000000000), orderedInterval (-46577603502 / 1000000000000) (-46577603479 / 1000000000000))) = true
  rfl'

theorem compactCertificate323_stateChecks3 :
    compactCertificate323.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 139 12 (1748605158404609 / 4000000000000)) (orderedInterval (-36274544875 / 1000000000000) (-36274544872 / 1000000000000), orderedInterval (-11809597839 / 1000000000000) (-11809597835 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 80 12 (1009557658911161 / 4000000000000)) (orderedInterval (48320882304 / 1000000000000) (48320885368 / 1000000000000), orderedInterval (-13787298079 / 1000000000000) (-13787295016 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 143 12 (1791477781782349 / 4000000000000)) (orderedInterval (21075585546 / 1000000000000) (21075587536 / 1000000000000), orderedInterval (-31284695533 / 1000000000000) (-31284693544 / 1000000000000))) = true
  rfl'

theorem compactCertificate323_stateChecks4 :
    compactCertificate323.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 133 12 (1673830928126881 / 4000000000000)) (orderedInterval (-38507570699 / 1000000000000) (-38507570665 / 1000000000000), orderedInterval (-6159939354 / 1000000000000) (-6159939320 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 95 12 (1194524731151473 / 4000000000000)) (orderedInterval (-37951400334 / 1000000000000) (-37951400333 / 1000000000000), orderedInterval (-26232519464 / 1000000000000) (-26232519463 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 108 12 (1354463731518567 / 4000000000000)) (orderedInterval (4714926306 / 1000000000000) (4714926307 / 1000000000000), orderedInterval (43095658593 / 1000000000000) (43095658594 / 1000000000000))) = true
  rfl'

theorem compactCertificate323_stateChecks5 :
    compactCertificate323.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 90 12 (1129210649397623 / 4000000000000)) (orderedInterval (16027993348 / 1000000000000) (16027993349 / 1000000000000), orderedInterval (44672873346 / 1000000000000) (44672873347 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 79 12 (997691854266083 / 4000000000000)) (orderedInterval (-45464055629 / 1000000000000) (-45464037638 / 1000000000000), orderedInterval (22122642312 / 1000000000000) (22122660304 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 115 12 (289169986274217 / 800000000000)) (orderedInterval (-34484129959 / 1000000000000) (-34484129958 / 1000000000000), orderedInterval (-23870441333 / 1000000000000) (-23870441332 / 1000000000000))) = true
  rfl'

theorem compactCertificate323_stateChecks6 :
    compactCertificate323.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (799859400217099 / 4000000000000)) (orderedInterval (-17336480130 / 1000000000000) (-17336479828 / 1000000000000), orderedInterval (53737974972 / 1000000000000) (53737975274 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (678049671764339 / 4000000000000)) (orderedInterval (37139940735 / 1000000000000) (37139940736 / 1000000000000), orderedInterval (48636968008 / 1000000000000) (48636968009 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (424292001734417 / 4000000000000)) (orderedInterval (3335613877 / 1000000000000) (3335613881 / 1000000000000), orderedInterval (77383590643 / 1000000000000) (77383590647 / 1000000000000))) = true
  rfl'

theorem compactCertificate323_stateChecks7 :
    compactCertificate323.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 18 12 (228185649664239 / 4000000000000)) (orderedInterval (101231057447 / 1000000000000) (101231057448 / 1000000000000), orderedInterval (29305442028 / 1000000000000) (29305442029 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 49 12 (619568427269717 / 4000000000000)) (orderedInterval (-63208671605 / 1000000000000) (-63208671120 / 1000000000000), orderedInterval (10915198784 / 1000000000000) (10915199270 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (845967718902709 / 4000000000000)) (orderedInterval (-53551436136 / 1000000000000) (-53551434860 / 1000000000000), orderedInterval (12058641842 / 1000000000000) (12058643119 / 1000000000000))) = true
  rfl'

theorem compactCertificate323_stateChecks8 :
    compactCertificate323.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 28 12 (357707998265583 / 4000000000000)) (orderedInterval (65838235084 / 1000000000000) (65838301493 / 1000000000000), orderedInterval (-53133409159 / 1000000000000) (-53133342750 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 116 12 (1454063153595343 / 4000000000000)) (orderedInterval (-5171965750 / 1000000000000) (-5171965744 / 1000000000000), orderedInterval (41534664226 / 1000000000000) (41534664231 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 77 12 (971246799406337 / 4000000000000)) (orderedInterval (-50816302814 / 1000000000000) (-50816302331 / 1000000000000), orderedInterval (6394643336 / 1000000000000) (6394643819 / 1000000000000))) = true
  rfl'

theorem compactCertificate323_states : ∀ j,
    BesselStateValid (compactCertificate323.point j) (compactCertificate323.state j) :=
  compactCertificate323.statesValid_of_checks3 compactCertificate323_stateChecks0
    compactCertificate323_stateChecks1 compactCertificate323_stateChecks2
    compactCertificate323_stateChecks3 compactCertificate323_stateChecks4
    compactCertificate323_stateChecks5 compactCertificate323_stateChecks6
    compactCertificate323_stateChecks7 compactCertificate323_stateChecks8

theorem compactCertificate323_chunkChecks0_0 :
    compactCertificate323.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (391 / 2) 0 (IntervalRat.scale (391 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (56944794102 / 1000000000000) (56944794127 / 1000000000000), orderedInterval (3548544668 / 1000000000000) (3548544693 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (576017660629291 / 4000000000000) 0 (IntervalRat.scale (391 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (18098645271 / 1000000000000) (18098645272 / 1000000000000), orderedInterval (63916038177 / 1000000000000) (63916038178 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (186272276417803 / 800000000000) 0 (IntervalRat.scale (391 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (47670765735 / 1000000000000) (47670765736 / 1000000000000), orderedInterval (21383467221 / 1000000000000) (21383467222 / 1000000000000)))) (orderedInterval (25536942049 / 1000000000000) (25536942073 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (168080516763137 / 4000000000000) 0 (IntervalRat.scale (391 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-113790722037 / 1000000000000) (-113790718595 / 1000000000000), orderedInterval (48271442941 / 1000000000000) (48271446383 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (451487910506189 / 4000000000000) 0 (IntervalRat.scale (391 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (39824611448 / 1000000000000) (39824611449 / 1000000000000), orderedInterval (63496328663 / 1000000000000) (63496328664 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1225877503930713 / 4000000000000) 0 (IntervalRat.scale (391 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-26545404673 / 1000000000000) (-26545398791 / 1000000000000), orderedInterval (37092096890 / 1000000000000) (37092102771 / 1000000000000)))) (orderedInterval (4575717575 / 1000000000000) (4575718055 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (902975821012769 / 4000000000000) 0 (IntervalRat.scale (391 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (17415420488 / 1000000000000) (17415420489 / 1000000000000), orderedInterval (50129197429 / 1000000000000) (50129197430 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1547264460035237 / 4000000000000) 0 (IntervalRat.scale (391 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-37591041648 / 1000000000000) (-37591041647 / 1000000000000), orderedInterval (-15206144789 / 1000000000000) (-15206144788 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1139707998265583 / 4000000000000) 0 (IntervalRat.scale (391 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (8135459005 / 1000000000000) (8135459028 / 1000000000000), orderedInterval (-46577603502 / 1000000000000) (-46577603479 / 1000000000000)))) (orderedInterval (1356076113 / 1000000000000) (1356076126 / 1000000000000))) = true
  rfl'

theorem compactCertificate323_chunkChecks0_1 :
    compactCertificate323.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1748605158404609 / 4000000000000) 0 (IntervalRat.scale (391 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-36274544875 / 1000000000000) (-36274544872 / 1000000000000), orderedInterval (-11809597839 / 1000000000000) (-11809597835 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1009557658911161 / 4000000000000) 0 (IntervalRat.scale (391 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (48320882304 / 1000000000000) (48320885368 / 1000000000000), orderedInterval (-13787298079 / 1000000000000) (-13787295016 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1791477781782349 / 4000000000000) 0 (IntervalRat.scale (391 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (21075585546 / 1000000000000) (21075587536 / 1000000000000), orderedInterval (-31284695533 / 1000000000000) (-31284693544 / 1000000000000)))) (orderedInterval (13021747015 / 1000000000000) (13021747603 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1673830928126881 / 4000000000000) 0 (IntervalRat.scale (391 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-38507570699 / 1000000000000) (-38507570665 / 1000000000000), orderedInterval (-6159939354 / 1000000000000) (-6159939320 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1194524731151473 / 4000000000000) 0 (IntervalRat.scale (391 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-37951400334 / 1000000000000) (-37951400333 / 1000000000000), orderedInterval (-26232519464 / 1000000000000) (-26232519463 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1354463731518567 / 4000000000000) 0 (IntervalRat.scale (391 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (4714926306 / 1000000000000) (4714926307 / 1000000000000), orderedInterval (43095658593 / 1000000000000) (43095658594 / 1000000000000)))) (orderedInterval (-2917472954 / 1000000000000) (-2917472930 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1129210649397623 / 4000000000000) 0 (IntervalRat.scale (391 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (16027993348 / 1000000000000) (16027993349 / 1000000000000), orderedInterval (44672873346 / 1000000000000) (44672873347 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (997691854266083 / 4000000000000) 0 (IntervalRat.scale (391 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-45464055629 / 1000000000000) (-45464037638 / 1000000000000), orderedInterval (22122642312 / 1000000000000) (22122660304 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (289169986274217 / 800000000000) 0 (IntervalRat.scale (391 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-34484129959 / 1000000000000) (-34484129958 / 1000000000000), orderedInterval (-23870441333 / 1000000000000) (-23870441332 / 1000000000000)))) (orderedInterval (1903911826 / 1000000000000) (1903912875 / 1000000000000))) = true
  rfl'

theorem compactCertificate323_chunkChecks0_2 :
    compactCertificate323.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (799859400217099 / 4000000000000) 0 (IntervalRat.scale (391 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-17336480130 / 1000000000000) (-17336479828 / 1000000000000), orderedInterval (53737974972 / 1000000000000) (53737975274 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (678049671764339 / 4000000000000) 0 (IntervalRat.scale (391 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (37139940735 / 1000000000000) (37139940736 / 1000000000000), orderedInterval (48636968008 / 1000000000000) (48636968009 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (424292001734417 / 4000000000000) 0 (IntervalRat.scale (391 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (3335613877 / 1000000000000) (3335613881 / 1000000000000), orderedInterval (77383590643 / 1000000000000) (77383590647 / 1000000000000)))) (orderedInterval (778444873 / 1000000000000) (778444971 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (228185649664239 / 4000000000000) 0 (IntervalRat.scale (391 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (101231057447 / 1000000000000) (101231057448 / 1000000000000), orderedInterval (29305442028 / 1000000000000) (29305442029 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (619568427269717 / 4000000000000) 0 (IntervalRat.scale (391 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-63208671605 / 1000000000000) (-63208671120 / 1000000000000), orderedInterval (10915198784 / 1000000000000) (10915199270 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (845967718902709 / 4000000000000) 0 (IntervalRat.scale (391 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-53551436136 / 1000000000000) (-53551434860 / 1000000000000), orderedInterval (12058641842 / 1000000000000) (12058643119 / 1000000000000)))) (orderedInterval (3668884522 / 1000000000000) (3668884654 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (357707998265583 / 4000000000000) 0 (IntervalRat.scale (391 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (65838235084 / 1000000000000) (65838301493 / 1000000000000), orderedInterval (-53133409159 / 1000000000000) (-53133342750 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1454063153595343 / 4000000000000) 0 (IntervalRat.scale (391 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-5171965750 / 1000000000000) (-5171965744 / 1000000000000), orderedInterval (41534664226 / 1000000000000) (41534664231 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (971246799406337 / 4000000000000) 0 (IntervalRat.scale (391 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-50816302814 / 1000000000000) (-50816302331 / 1000000000000), orderedInterval (6394643336 / 1000000000000) (6394643819 / 1000000000000)))) (orderedInterval (10352387972 / 1000000000000) (10352388518 / 1000000000000))) = true
  rfl'

theorem compactCertificate323_chunkChecks0 :
    compactCertificate323.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate323.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate323_chunkChecks0_0
    compactCertificate323_chunkChecks0_1 compactCertificate323_chunkChecks0_2

theorem compactCertificate323_chunkChecks1_0 :
    compactCertificate323.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (391 / 2) 1 (IntervalRat.scale (391 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (56944794102 / 1000000000000) (56944794127 / 1000000000000), orderedInterval (3548544668 / 1000000000000) (3548544693 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (576017660629291 / 4000000000000) 1 (IntervalRat.scale (391 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (18098645271 / 1000000000000) (18098645272 / 1000000000000), orderedInterval (63916038177 / 1000000000000) (63916038178 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (186272276417803 / 800000000000) 1 (IntervalRat.scale (391 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (47670765735 / 1000000000000) (47670765736 / 1000000000000), orderedInterval (21383467221 / 1000000000000) (21383467222 / 1000000000000)))) (orderedInterval (3339688836 / 1000000000000) (3339688862 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (168080516763137 / 4000000000000) 1 (IntervalRat.scale (391 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-113790722037 / 1000000000000) (-113790718595 / 1000000000000), orderedInterval (48271442941 / 1000000000000) (48271446383 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (451487910506189 / 4000000000000) 1 (IntervalRat.scale (391 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (39824611448 / 1000000000000) (39824611449 / 1000000000000), orderedInterval (63496328663 / 1000000000000) (63496328664 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1225877503930713 / 4000000000000) 1 (IntervalRat.scale (391 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-26545404673 / 1000000000000) (-26545398791 / 1000000000000), orderedInterval (37092096890 / 1000000000000) (37092102771 / 1000000000000)))) (orderedInterval (-2907654571 / 1000000000000) (-2907653880 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (902975821012769 / 4000000000000) 1 (IntervalRat.scale (391 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (17415420488 / 1000000000000) (17415420489 / 1000000000000), orderedInterval (50129197429 / 1000000000000) (50129197430 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1547264460035237 / 4000000000000) 1 (IntervalRat.scale (391 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-37591041648 / 1000000000000) (-37591041647 / 1000000000000), orderedInterval (-15206144789 / 1000000000000) (-15206144788 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1139707998265583 / 4000000000000) 1 (IntervalRat.scale (391 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (8135459005 / 1000000000000) (8135459028 / 1000000000000), orderedInterval (-46577603502 / 1000000000000) (-46577603479 / 1000000000000)))) (orderedInterval (-712610098 / 1000000000000) (-712610077 / 1000000000000))) = true
  rfl'

theorem compactCertificate323_chunkChecks1_1 :
    compactCertificate323.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1748605158404609 / 4000000000000) 1 (IntervalRat.scale (391 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-36274544875 / 1000000000000) (-36274544872 / 1000000000000), orderedInterval (-11809597839 / 1000000000000) (-11809597835 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1009557658911161 / 4000000000000) 1 (IntervalRat.scale (391 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (48320882304 / 1000000000000) (48320885368 / 1000000000000), orderedInterval (-13787298079 / 1000000000000) (-13787295016 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1791477781782349 / 4000000000000) 1 (IntervalRat.scale (391 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (21075585546 / 1000000000000) (21075587536 / 1000000000000), orderedInterval (-31284695533 / 1000000000000) (-31284693544 / 1000000000000)))) (orderedInterval (-6814861308 / 1000000000000) (-6814860205 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1673830928126881 / 4000000000000) 1 (IntervalRat.scale (391 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-38507570699 / 1000000000000) (-38507570665 / 1000000000000), orderedInterval (-6159939354 / 1000000000000) (-6159939320 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1194524731151473 / 4000000000000) 1 (IntervalRat.scale (391 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-37951400334 / 1000000000000) (-37951400333 / 1000000000000), orderedInterval (-26232519464 / 1000000000000) (-26232519463 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1354463731518567 / 4000000000000) 1 (IntervalRat.scale (391 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (4714926306 / 1000000000000) (4714926307 / 1000000000000), orderedInterval (43095658593 / 1000000000000) (43095658594 / 1000000000000)))) (orderedInterval (-3928923472 / 1000000000000) (-3928923432 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1129210649397623 / 4000000000000) 1 (IntervalRat.scale (391 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (16027993348 / 1000000000000) (16027993349 / 1000000000000), orderedInterval (44672873346 / 1000000000000) (44672873347 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (997691854266083 / 4000000000000) 1 (IntervalRat.scale (391 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-45464055629 / 1000000000000) (-45464037638 / 1000000000000), orderedInterval (22122642312 / 1000000000000) (22122660304 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (289169986274217 / 800000000000) 1 (IntervalRat.scale (391 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-34484129959 / 1000000000000) (-34484129958 / 1000000000000), orderedInterval (-23870441333 / 1000000000000) (-23870441332 / 1000000000000)))) (orderedInterval (-2000296808 / 1000000000000) (-2000295466 / 1000000000000))) = true
  rfl'

theorem compactCertificate323_chunkChecks1_2 :
    compactCertificate323.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (799859400217099 / 4000000000000) 1 (IntervalRat.scale (391 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-17336480130 / 1000000000000) (-17336479828 / 1000000000000), orderedInterval (53737974972 / 1000000000000) (53737975274 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (678049671764339 / 4000000000000) 1 (IntervalRat.scale (391 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (37139940735 / 1000000000000) (37139940736 / 1000000000000), orderedInterval (48636968008 / 1000000000000) (48636968009 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (424292001734417 / 4000000000000) 1 (IntervalRat.scale (391 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (3335613877 / 1000000000000) (3335613881 / 1000000000000), orderedInterval (77383590643 / 1000000000000) (77383590647 / 1000000000000)))) (orderedInterval (-9808571671 / 1000000000000) (-9808571576 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (228185649664239 / 4000000000000) 1 (IntervalRat.scale (391 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (101231057447 / 1000000000000) (101231057448 / 1000000000000), orderedInterval (29305442028 / 1000000000000) (29305442029 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (619568427269717 / 4000000000000) 1 (IntervalRat.scale (391 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-63208671605 / 1000000000000) (-63208671120 / 1000000000000), orderedInterval (10915198784 / 1000000000000) (10915199270 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (845967718902709 / 4000000000000) 1 (IntervalRat.scale (391 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-53551436136 / 1000000000000) (-53551434860 / 1000000000000), orderedInterval (12058641842 / 1000000000000) (12058643119 / 1000000000000)))) (orderedInterval (-1353852519 / 1000000000000) (-1353852382 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (357707998265583 / 4000000000000) 1 (IntervalRat.scale (391 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (65838235084 / 1000000000000) (65838301493 / 1000000000000), orderedInterval (-53133409159 / 1000000000000) (-53133342750 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1454063153595343 / 4000000000000) 1 (IntervalRat.scale (391 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-5171965750 / 1000000000000) (-5171965744 / 1000000000000), orderedInterval (41534664226 / 1000000000000) (41534664231 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (971246799406337 / 4000000000000) 1 (IntervalRat.scale (391 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-50816302814 / 1000000000000) (-50816302331 / 1000000000000), orderedInterval (6394643336 / 1000000000000) (6394643819 / 1000000000000)))) (orderedInterval (-7923354780 / 1000000000000) (-7923354406 / 1000000000000))) = true
  rfl'

theorem compactCertificate323_chunkChecks1 :
    compactCertificate323.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate323.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate323_chunkChecks1_0
    compactCertificate323_chunkChecks1_1 compactCertificate323_chunkChecks1_2

theorem compactCertificate323_chunkChecks2_0 :
    compactCertificate323.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (391 / 2) 2 (IntervalRat.scale (391 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (56944794102 / 1000000000000) (56944794127 / 1000000000000), orderedInterval (3548544668 / 1000000000000) (3548544693 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (576017660629291 / 4000000000000) 2 (IntervalRat.scale (391 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (18098645271 / 1000000000000) (18098645272 / 1000000000000), orderedInterval (63916038177 / 1000000000000) (63916038178 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (186272276417803 / 800000000000) 2 (IntervalRat.scale (391 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (47670765735 / 1000000000000) (47670765736 / 1000000000000), orderedInterval (21383467221 / 1000000000000) (21383467222 / 1000000000000)))) (orderedInterval (-26647525397 / 1000000000000) (-26647525368 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (168080516763137 / 4000000000000) 2 (IntervalRat.scale (391 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-113790722037 / 1000000000000) (-113790718595 / 1000000000000), orderedInterval (48271442941 / 1000000000000) (48271446383 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (451487910506189 / 4000000000000) 2 (IntervalRat.scale (391 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (39824611448 / 1000000000000) (39824611449 / 1000000000000), orderedInterval (63496328663 / 1000000000000) (63496328664 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1225877503930713 / 4000000000000) 2 (IntervalRat.scale (391 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-26545404673 / 1000000000000) (-26545398791 / 1000000000000), orderedInterval (37092096890 / 1000000000000) (37092102771 / 1000000000000)))) (orderedInterval (-5164268009 / 1000000000000) (-5164266939 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (902975821012769 / 4000000000000) 2 (IntervalRat.scale (391 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (17415420488 / 1000000000000) (17415420489 / 1000000000000), orderedInterval (50129197429 / 1000000000000) (50129197430 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1547264460035237 / 4000000000000) 2 (IntervalRat.scale (391 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-37591041648 / 1000000000000) (-37591041647 / 1000000000000), orderedInterval (-15206144789 / 1000000000000) (-15206144788 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1139707998265583 / 4000000000000) 2 (IntervalRat.scale (391 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (8135459005 / 1000000000000) (8135459028 / 1000000000000), orderedInterval (-46577603502 / 1000000000000) (-46577603479 / 1000000000000)))) (orderedInterval (-4953099542 / 1000000000000) (-4953099506 / 1000000000000))) = true
  rfl'

theorem compactCertificate323_chunkChecks2_1 :
    compactCertificate323.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1748605158404609 / 4000000000000) 2 (IntervalRat.scale (391 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-36274544875 / 1000000000000) (-36274544872 / 1000000000000), orderedInterval (-11809597839 / 1000000000000) (-11809597835 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1009557658911161 / 4000000000000) 2 (IntervalRat.scale (391 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (48320882304 / 1000000000000) (48320885368 / 1000000000000), orderedInterval (-13787298079 / 1000000000000) (-13787295016 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1791477781782349 / 4000000000000) 2 (IntervalRat.scale (391 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (21075585546 / 1000000000000) (21075587536 / 1000000000000), orderedInterval (-31284695533 / 1000000000000) (-31284693544 / 1000000000000)))) (orderedInterval (-53883520728 / 1000000000000) (-53883518512 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1673830928126881 / 4000000000000) 2 (IntervalRat.scale (391 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-38507570699 / 1000000000000) (-38507570665 / 1000000000000), orderedInterval (-6159939354 / 1000000000000) (-6159939320 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1194524731151473 / 4000000000000) 2 (IntervalRat.scale (391 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-37951400334 / 1000000000000) (-37951400333 / 1000000000000), orderedInterval (-26232519464 / 1000000000000) (-26232519463 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1354463731518567 / 4000000000000) 2 (IntervalRat.scale (391 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (4714926306 / 1000000000000) (4714926307 / 1000000000000), orderedInterval (43095658593 / 1000000000000) (43095658594 / 1000000000000)))) (orderedInterval (5280544344 / 1000000000000) (5280544411 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1129210649397623 / 4000000000000) 2 (IntervalRat.scale (391 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (16027993348 / 1000000000000) (16027993349 / 1000000000000), orderedInterval (44672873346 / 1000000000000) (44672873347 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (997691854266083 / 4000000000000) 2 (IntervalRat.scale (391 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-45464055629 / 1000000000000) (-45464037638 / 1000000000000), orderedInterval (22122642312 / 1000000000000) (22122660304 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (289169986274217 / 800000000000) 2 (IntervalRat.scale (391 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-34484129959 / 1000000000000) (-34484129958 / 1000000000000), orderedInterval (-23870441333 / 1000000000000) (-23870441332 / 1000000000000)))) (orderedInterval (-1592350196 / 1000000000000) (-1592348472 / 1000000000000))) = true
  rfl'

theorem compactCertificate323_chunkChecks2_2 :
    compactCertificate323.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (799859400217099 / 4000000000000) 2 (IntervalRat.scale (391 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-17336480130 / 1000000000000) (-17336479828 / 1000000000000), orderedInterval (53737974972 / 1000000000000) (53737975274 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (678049671764339 / 4000000000000) 2 (IntervalRat.scale (391 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (37139940735 / 1000000000000) (37139940736 / 1000000000000), orderedInterval (48636968008 / 1000000000000) (48636968009 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (424292001734417 / 4000000000000) 2 (IntervalRat.scale (391 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (3335613877 / 1000000000000) (3335613881 / 1000000000000), orderedInterval (77383590643 / 1000000000000) (77383590647 / 1000000000000)))) (orderedInterval (-1301428035 / 1000000000000) (-1301427941 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (228185649664239 / 4000000000000) 2 (IntervalRat.scale (391 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (101231057447 / 1000000000000) (101231057448 / 1000000000000), orderedInterval (29305442028 / 1000000000000) (29305442029 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (619568427269717 / 4000000000000) 2 (IntervalRat.scale (391 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-63208671605 / 1000000000000) (-63208671120 / 1000000000000), orderedInterval (10915198784 / 1000000000000) (10915199270 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (845967718902709 / 4000000000000) 2 (IntervalRat.scale (391 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-53551436136 / 1000000000000) (-53551434860 / 1000000000000), orderedInterval (12058641842 / 1000000000000) (12058643119 / 1000000000000)))) (orderedInterval (-5537088203 / 1000000000000) (-5537088059 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (357707998265583 / 4000000000000) 2 (IntervalRat.scale (391 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (65838235084 / 1000000000000) (65838301493 / 1000000000000), orderedInterval (-53133409159 / 1000000000000) (-53133342750 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1454063153595343 / 4000000000000) 2 (IntervalRat.scale (391 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-5171965750 / 1000000000000) (-5171965744 / 1000000000000), orderedInterval (41534664226 / 1000000000000) (41534664231 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (971246799406337 / 4000000000000) 2 (IntervalRat.scale (391 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-50816302814 / 1000000000000) (-50816302331 / 1000000000000), orderedInterval (6394643336 / 1000000000000) (6394643819 / 1000000000000)))) (orderedInterval (-16205759494 / 1000000000000) (-16205759154 / 1000000000000))) = true
  rfl'

theorem compactCertificate323_chunkChecks2 :
    compactCertificate323.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate323.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate323_chunkChecks2_0
    compactCertificate323_chunkChecks2_1 compactCertificate323_chunkChecks2_2

theorem compactCertificate323_chunkChecks3_0 :
    compactCertificate323.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (391 / 2) 3 (IntervalRat.scale (391 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (56944794102 / 1000000000000) (56944794127 / 1000000000000), orderedInterval (3548544668 / 1000000000000) (3548544693 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (576017660629291 / 4000000000000) 3 (IntervalRat.scale (391 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (18098645271 / 1000000000000) (18098645272 / 1000000000000), orderedInterval (63916038177 / 1000000000000) (63916038178 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (186272276417803 / 800000000000) 3 (IntervalRat.scale (391 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (47670765735 / 1000000000000) (47670765736 / 1000000000000), orderedInterval (21383467221 / 1000000000000) (21383467222 / 1000000000000)))) (orderedInterval (-3628031071 / 1000000000000) (-3628031040 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (168080516763137 / 4000000000000) 3 (IntervalRat.scale (391 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-113790722037 / 1000000000000) (-113790718595 / 1000000000000), orderedInterval (48271442941 / 1000000000000) (48271446383 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (451487910506189 / 4000000000000) 3 (IntervalRat.scale (391 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (39824611448 / 1000000000000) (39824611449 / 1000000000000), orderedInterval (63496328663 / 1000000000000) (63496328664 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1225877503930713 / 4000000000000) 3 (IntervalRat.scale (391 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-26545404673 / 1000000000000) (-26545398791 / 1000000000000), orderedInterval (37092096890 / 1000000000000) (37092102771 / 1000000000000)))) (orderedInterval (9743381762 / 1000000000000) (9743383434 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (902975821012769 / 4000000000000) 3 (IntervalRat.scale (391 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (17415420488 / 1000000000000) (17415420489 / 1000000000000), orderedInterval (50129197429 / 1000000000000) (50129197430 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1547264460035237 / 4000000000000) 3 (IntervalRat.scale (391 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-37591041648 / 1000000000000) (-37591041647 / 1000000000000), orderedInterval (-15206144789 / 1000000000000) (-15206144788 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1139707998265583 / 4000000000000) 3 (IntervalRat.scale (391 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (8135459005 / 1000000000000) (8135459028 / 1000000000000), orderedInterval (-46577603502 / 1000000000000) (-46577603479 / 1000000000000)))) (orderedInterval (-122856832 / 1000000000000) (-122856768 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate323_chunkChecks3_1 :
    compactCertificate323.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1748605158404609 / 4000000000000) 3 (IntervalRat.scale (391 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-36274544875 / 1000000000000) (-36274544872 / 1000000000000), orderedInterval (-11809597839 / 1000000000000) (-11809597835 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1009557658911161 / 4000000000000) 3 (IntervalRat.scale (391 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (48320882304 / 1000000000000) (48320885368 / 1000000000000), orderedInterval (-13787298079 / 1000000000000) (-13787295016 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1791477781782349 / 4000000000000) 3 (IntervalRat.scale (391 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (21075585546 / 1000000000000) (21075587536 / 1000000000000), orderedInterval (-31284695533 / 1000000000000) (-31284693544 / 1000000000000)))) (orderedInterval (32482405199 / 1000000000000) (32482409859 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1673830928126881 / 4000000000000) 3 (IntervalRat.scale (391 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-38507570699 / 1000000000000) (-38507570665 / 1000000000000), orderedInterval (-6159939354 / 1000000000000) (-6159939320 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1194524731151473 / 4000000000000) 3 (IntervalRat.scale (391 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-37951400334 / 1000000000000) (-37951400333 / 1000000000000), orderedInterval (-26232519464 / 1000000000000) (-26232519463 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1354463731518567 / 4000000000000) 3 (IntervalRat.scale (391 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (4714926306 / 1000000000000) (4714926307 / 1000000000000), orderedInterval (43095658593 / 1000000000000) (43095658594 / 1000000000000)))) (orderedInterval (8857064719 / 1000000000000) (8857064832 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1129210649397623 / 4000000000000) 3 (IntervalRat.scale (391 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (16027993348 / 1000000000000) (16027993349 / 1000000000000), orderedInterval (44672873346 / 1000000000000) (44672873347 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (997691854266083 / 4000000000000) 3 (IntervalRat.scale (391 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-45464055629 / 1000000000000) (-45464037638 / 1000000000000), orderedInterval (22122642312 / 1000000000000) (22122660304 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (289169986274217 / 800000000000) 3 (IntervalRat.scale (391 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-34484129959 / 1000000000000) (-34484129958 / 1000000000000), orderedInterval (-23870441333 / 1000000000000) (-23870441332 / 1000000000000)))) (orderedInterval (4946851488 / 1000000000000) (4946853698 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate323_chunkChecks3_2 :
    compactCertificate323.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (799859400217099 / 4000000000000) 3 (IntervalRat.scale (391 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-17336480130 / 1000000000000) (-17336479828 / 1000000000000), orderedInterval (53737974972 / 1000000000000) (53737975274 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (678049671764339 / 4000000000000) 3 (IntervalRat.scale (391 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (37139940735 / 1000000000000) (37139940736 / 1000000000000), orderedInterval (48636968008 / 1000000000000) (48636968009 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (424292001734417 / 4000000000000) 3 (IntervalRat.scale (391 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (3335613877 / 1000000000000) (3335613881 / 1000000000000), orderedInterval (77383590643 / 1000000000000) (77383590647 / 1000000000000)))) (orderedInterval (10593065240 / 1000000000000) (10593065335 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (228185649664239 / 4000000000000) 3 (IntervalRat.scale (391 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (101231057447 / 1000000000000) (101231057448 / 1000000000000), orderedInterval (29305442028 / 1000000000000) (29305442029 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (619568427269717 / 4000000000000) 3 (IntervalRat.scale (391 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-63208671605 / 1000000000000) (-63208671120 / 1000000000000), orderedInterval (10915198784 / 1000000000000) (10915199270 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (845967718902709 / 4000000000000) 3 (IntervalRat.scale (391 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-53551436136 / 1000000000000) (-53551434860 / 1000000000000), orderedInterval (12058641842 / 1000000000000) (12058643119 / 1000000000000)))) (orderedInterval (1334894622 / 1000000000000) (1334894774 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (357707998265583 / 4000000000000) 3 (IntervalRat.scale (391 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (65838235084 / 1000000000000) (65838301493 / 1000000000000), orderedInterval (-53133409159 / 1000000000000) (-53133342750 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1454063153595343 / 4000000000000) 3 (IntervalRat.scale (391 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-5171965750 / 1000000000000) (-5171965744 / 1000000000000), orderedInterval (41534664226 / 1000000000000) (41534664231 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (971246799406337 / 4000000000000) 3 (IntervalRat.scale (391 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-50816302814 / 1000000000000) (-50816302331 / 1000000000000), orderedInterval (6394643336 / 1000000000000) (6394643819 / 1000000000000)))) (orderedInterval (24147752045 / 1000000000000) (24147752435 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate323_chunkChecks3 :
    compactCertificate323.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate323.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate323_chunkChecks3_0
    compactCertificate323_chunkChecks3_1 compactCertificate323_chunkChecks3_2

theorem compactCertificate323_chunkChecks4_0 :
    compactCertificate323.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (391 / 2) 4 (IntervalRat.scale (391 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (56944794102 / 1000000000000) (56944794127 / 1000000000000), orderedInterval (3548544668 / 1000000000000) (3548544693 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (576017660629291 / 4000000000000) 4 (IntervalRat.scale (391 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (18098645271 / 1000000000000) (18098645272 / 1000000000000), orderedInterval (63916038177 / 1000000000000) (63916038178 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (186272276417803 / 800000000000) 4 (IntervalRat.scale (391 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (47670765735 / 1000000000000) (47670765736 / 1000000000000), orderedInterval (21383467221 / 1000000000000) (21383467222 / 1000000000000)))) (orderedInterval (28285537511 / 1000000000000) (28285537546 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (168080516763137 / 4000000000000) 4 (IntervalRat.scale (391 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-113790722037 / 1000000000000) (-113790718595 / 1000000000000), orderedInterval (48271442941 / 1000000000000) (48271446383 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (451487910506189 / 4000000000000) 4 (IntervalRat.scale (391 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (39824611448 / 1000000000000) (39824611449 / 1000000000000), orderedInterval (63496328663 / 1000000000000) (63496328664 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1225877503930713 / 4000000000000) 4 (IntervalRat.scale (391 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-26545404673 / 1000000000000) (-26545398791 / 1000000000000), orderedInterval (37092096890 / 1000000000000) (37092102771 / 1000000000000)))) (orderedInterval (11460502474 / 1000000000000) (11460505102 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (902975821012769 / 4000000000000) 4 (IntervalRat.scale (391 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (17415420488 / 1000000000000) (17415420489 / 1000000000000), orderedInterval (50129197429 / 1000000000000) (50129197430 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1547264460035237 / 4000000000000) 4 (IntervalRat.scale (391 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-37591041648 / 1000000000000) (-37591041647 / 1000000000000), orderedInterval (-15206144789 / 1000000000000) (-15206144788 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1139707998265583 / 4000000000000) 4 (IntervalRat.scale (391 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (8135459005 / 1000000000000) (8135459028 / 1000000000000), orderedInterval (-46577603502 / 1000000000000) (-46577603479 / 1000000000000)))) (orderedInterval (18658175400 / 1000000000000) (18658175518 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate323_chunkChecks4_1 :
    compactCertificate323.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1748605158404609 / 4000000000000) 4 (IntervalRat.scale (391 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-36274544875 / 1000000000000) (-36274544872 / 1000000000000), orderedInterval (-11809597839 / 1000000000000) (-11809597835 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1009557658911161 / 4000000000000) 4 (IntervalRat.scale (391 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (48320882304 / 1000000000000) (48320885368 / 1000000000000), orderedInterval (-13787298079 / 1000000000000) (-13787295016 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1791477781782349 / 4000000000000) 4 (IntervalRat.scale (391 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (21075585546 / 1000000000000) (21075587536 / 1000000000000), orderedInterval (-31284695533 / 1000000000000) (-31284693544 / 1000000000000)))) (orderedInterval (253270707045 / 1000000000000) (253270717196 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1673830928126881 / 4000000000000) 4 (IntervalRat.scale (391 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-38507570699 / 1000000000000) (-38507570665 / 1000000000000), orderedInterval (-6159939354 / 1000000000000) (-6159939320 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1194524731151473 / 4000000000000) 4 (IntervalRat.scale (391 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-37951400334 / 1000000000000) (-37951400333 / 1000000000000), orderedInterval (-26232519464 / 1000000000000) (-26232519463 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1354463731518567 / 4000000000000) 4 (IntervalRat.scale (391 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (4714926306 / 1000000000000) (4714926307 / 1000000000000), orderedInterval (43095658593 / 1000000000000) (43095658594 / 1000000000000)))) (orderedInterval (-5252127779 / 1000000000000) (-5252127581 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1129210649397623 / 4000000000000) 4 (IntervalRat.scale (391 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (16027993348 / 1000000000000) (16027993349 / 1000000000000), orderedInterval (44672873346 / 1000000000000) (44672873347 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (997691854266083 / 4000000000000) 4 (IntervalRat.scale (391 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-45464055629 / 1000000000000) (-45464037638 / 1000000000000), orderedInterval (22122642312 / 1000000000000) (22122660304 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (289169986274217 / 800000000000) 4 (IntervalRat.scale (391 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-34484129959 / 1000000000000) (-34484129958 / 1000000000000), orderedInterval (-23870441333 / 1000000000000) (-23870441332 / 1000000000000)))) (orderedInterval (-2670575577 / 1000000000000) (-2670572728 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate323_chunkChecks4_2 :
    compactCertificate323.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (799859400217099 / 4000000000000) 4 (IntervalRat.scale (391 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-17336480130 / 1000000000000) (-17336479828 / 1000000000000), orderedInterval (53737974972 / 1000000000000) (53737975274 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (678049671764339 / 4000000000000) 4 (IntervalRat.scale (391 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (37139940735 / 1000000000000) (37139940736 / 1000000000000), orderedInterval (48636968008 / 1000000000000) (48636968009 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (424292001734417 / 4000000000000) 4 (IntervalRat.scale (391 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (3335613877 / 1000000000000) (3335613881 / 1000000000000), orderedInterval (77383590643 / 1000000000000) (77383590647 / 1000000000000)))) (orderedInterval (1746851451 / 1000000000000) (1746851547 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (228185649664239 / 4000000000000) 4 (IntervalRat.scale (391 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (101231057447 / 1000000000000) (101231057448 / 1000000000000), orderedInterval (29305442028 / 1000000000000) (29305442029 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (619568427269717 / 4000000000000) 4 (IntervalRat.scale (391 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-63208671605 / 1000000000000) (-63208671120 / 1000000000000), orderedInterval (10915198784 / 1000000000000) (10915199270 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (845967718902709 / 4000000000000) 4 (IntervalRat.scale (391 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-53551436136 / 1000000000000) (-53551434860 / 1000000000000), orderedInterval (12058641842 / 1000000000000) (12058643119 / 1000000000000)))) (orderedInterval (6158622366 / 1000000000000) (6158622529 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (357707998265583 / 4000000000000) 4 (IntervalRat.scale (391 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (65838235084 / 1000000000000) (65838301493 / 1000000000000), orderedInterval (-53133409159 / 1000000000000) (-53133342750 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1454063153595343 / 4000000000000) 4 (IntervalRat.scale (391 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-5171965750 / 1000000000000) (-5171965744 / 1000000000000), orderedInterval (41534664226 / 1000000000000) (41534664231 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (971246799406337 / 4000000000000) 4 (IntervalRat.scale (391 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-50816302814 / 1000000000000) (-50816302331 / 1000000000000), orderedInterval (6394643336 / 1000000000000) (6394643819 / 1000000000000)))) (orderedInterval (27490161407 / 1000000000000) (27490161927 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate323_chunkChecks4 :
    compactCertificate323.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate323.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate323_chunkChecks4_0
    compactCertificate323_chunkChecks4_1 compactCertificate323_chunkChecks4_2

theorem compactCertificate323_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate323.chunkCheck r b = true :=
  compactCertificate323.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate323_chunkChecks0
    · exact compactCertificate323_chunkChecks1
    · exact compactCertificate323_chunkChecks2
    · exact compactCertificate323_chunkChecks3
    · exact compactCertificate323_chunkChecks4)

theorem compactCertificate323_coefficient0 :
    compactCertificate323.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate323_coefficient1 :
    compactCertificate323.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate323_coefficient2 :
    compactCertificate323.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate323_coefficient3 :
    compactCertificate323.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate323_coefficient4 :
    compactCertificate323.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate323_coefficients : ∀ r : Fin 5,
    compactCertificate323.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate323_coefficient0
  · exact compactCertificate323_coefficient1
  · exact compactCertificate323_coefficient2
  · exact compactCertificate323_coefficient3
  · exact compactCertificate323_coefficient4

theorem compactCertificate323_lower : (1 : ℚ) ≤ compactCertificate323.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate323, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate323_proves {t : ℝ} (ht : t ∈ compactCertificate323.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate323.proves compactCertificate323_states compactCertificate323_chunks
    compactCertificate323_coefficients compactCertificate323_lower ht

end Erdos232
