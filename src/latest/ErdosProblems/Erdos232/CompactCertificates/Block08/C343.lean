/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate343 : CompactCertificate where
  left := 215
  right := 216
  center := 431 / 2
  grid := fun i =>
    match i.val with
    | 0 => 69
    | 1 => 51
    | 2 => 82
    | 3 => 15
    | 4 => 40
    | 5 => 108
    | 6 => 79
    | 7 => 136
    | 8 => 100
    | 9 => 153
    | 10 => 89
    | 11 => 157
    | 12 => 147
    | 13 => 105
    | 14 => 119
    | 15 => 99
    | 16 => 88
    | 17 => 127
    | 18 => 70
    | 19 => 60
    | 20 => 37
    | 21 => 20
    | 22 => 54
    | 23 => 74
    | 24 => 31
    | 25 => 128
    | _ => 85
  point := fun i =>
    match i.val with
    | 0 => 431 / 2
    | 1 => 634945298545331 / 4000000000000
    | 2 => 205328263775123 / 800000000000
    | 3 => 185275454539417 / 4000000000000
    | 4 => 497675932041349 / 4000000000000
    | 5 => 1351286967248433 / 4000000000000
    | 6 => 995351864083129 / 4000000000000
    | 7 => 1705552384335517 / 4000000000000
    | 8 => 1256302166886103 / 4000000000000
    | 9 => 1927490596604569 / 4000000000000
    | 10 => 1112837214810001 / 4000000000000
    | 11 => 1974749166107909 / 4000000000000
    | 12 => 1845066828702521 / 4000000000000
    | 13 => 1316726749683593 / 4000000000000
    | 14 => 1493027796124047 / 4000000000000
    | 15 => 1244730920435743 / 4000000000000
    | 16 => 1099757517106603 / 4000000000000
    | 17 => 318752593565697 / 800000000000
    | 18 => 881686448832659 / 4000000000000
    | 19 => 747415367085499 / 4000000000000
    | 20 => 467697833113897 / 4000000000000
    | 21 => 251529450141399 / 4000000000000
    | 22 => 682951386581197 / 4000000000000
    | 23 => 932511731066669 / 4000000000000
    | 24 => 394302166886103 / 4000000000000
    | 25 => 1602816417390263 / 4000000000000
    | _ => 1070607085790617 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (25342978679 / 1000000000000) (25342980892 / 1000000000000), orderedInterval (-48140917836 / 1000000000000) (-48140915624 / 1000000000000))
    | 1 => (orderedInterval (40811522597 / 1000000000000) (40811548975 / 1000000000000), orderedInterval (-48553459645 / 1000000000000) (-48553433267 / 1000000000000))
    | 2 => (orderedInterval (-8197873482 / 1000000000000) (-8197873457 / 1000000000000), orderedInterval (49140275157 / 1000000000000) (49140275182 / 1000000000000))
    | 3 => (orderedInterval (2617122252 / 1000000000000) (2617122266 / 1000000000000), orderedInterval (-117238475434 / 1000000000000) (-117238475420 / 1000000000000))
    | 4 => (orderedInterval (-31777228252 / 1000000000000) (-31777225458 / 1000000000000), orderedInterval (64213378675 / 1000000000000) (64213381469 / 1000000000000))
    | 5 => (orderedInterval (-27472688808 / 1000000000000) (-27472679247 / 1000000000000), orderedInterval (33652207292 / 1000000000000) (33652216853 / 1000000000000))
    | 6 => (orderedInterval (-50128517828 / 1000000000000) (-50128517814 / 1000000000000), orderedInterval (-6644456040 / 1000000000000) (-6644456027 / 1000000000000))
    | 7 => (orderedInterval (-3218835722 / 1000000000000) (-3218835720 / 1000000000000), orderedInterval (38509521037 / 1000000000000) (38509521039 / 1000000000000))
    | 8 => (orderedInterval (29047764668 / 1000000000000) (29047764669 / 1000000000000), orderedInterval (34351309918 / 1000000000000) (34351309919 / 1000000000000))
    | 9 => (orderedInterval (-33139141027 / 1000000000000) (-33139099832 / 1000000000000), orderedInterval (14965377984 / 1000000000000) (14965419179 / 1000000000000))
    | 10 => (orderedInterval (27305265195 / 1000000000000) (27305271080 / 1000000000000), orderedInterval (-39326295451 / 1000000000000) (-39326289566 / 1000000000000))
    | 11 => (orderedInterval (-33990768786 / 1000000000000) (-33990768782 / 1000000000000), orderedInterval (-11547776048 / 1000000000000) (-11547776043 / 1000000000000))
    | 12 => (orderedInterval (-8748250452 / 1000000000000) (-8748250451 / 1000000000000), orderedInterval (-36096255097 / 1000000000000) (-36096255096 / 1000000000000))
    | 13 => (orderedInterval (-4367462123 / 1000000000000) (-4367462122 / 1000000000000), orderedInterval (-43752639066 / 1000000000000) (-43752639065 / 1000000000000))
    | 14 => (orderedInterval (-7900436568 / 1000000000000) (-7900436567 / 1000000000000), orderedInterval (-40525388796 / 1000000000000) (-40525388795 / 1000000000000))
    | 15 => (orderedInterval (-36792662396 / 1000000000000) (-36792662395 / 1000000000000), orderedInterval (-26248790763 / 1000000000000) (-26248790762 / 1000000000000))
    | 16 => (orderedInterval (-32297980573 / 1000000000000) (-32297959304 / 1000000000000), orderedInterval (35728501207 / 1000000000000) (35728522476 / 1000000000000))
    | 17 => (orderedInterval (-9639634567 / 1000000000000) (-9639634566 / 1000000000000), orderedInterval (-38780381430 / 1000000000000) (-38780381429 / 1000000000000))
    | 18 => (orderedInterval (51710228062 / 1000000000000) (51710228064 / 1000000000000), orderedInterval (14519547393 / 1000000000000) (14519547394 / 1000000000000))
    | 19 => (orderedInterval (-44120273266 / 1000000000000) (-44120180571 / 1000000000000), orderedInterval (38333851481 / 1000000000000) (38333944176 / 1000000000000))
    | 20 => (orderedInterval (-73412373518 / 1000000000000) (-73412373510 / 1000000000000), orderedInterval (-7121442715 / 1000000000000) (-7121442707 / 1000000000000))
    | 21 => (orderedInterval (74513612281 / 1000000000000) (74513612282 / 1000000000000), orderedInterval (67021682386 / 1000000000000) (67021682387 / 1000000000000))
    | 22 => (orderedInterval (58231140745 / 1000000000000) (58231143443 / 1000000000000), orderedInterval (-18548772165 / 1000000000000) (-18548769467 / 1000000000000))
    | 23 => (orderedInterval (51775231083 / 1000000000000) (51775231095 / 1000000000000), orderedInterval (6966647321 / 1000000000000) (6966647332 / 1000000000000))
    | 24 => (orderedInterval (-74034172432 / 1000000000000) (-74034167409 / 1000000000000), orderedInterval (31633717926 / 1000000000000) (31633722950 / 1000000000000))
    | 25 => (orderedInterval (-23632931774 / 1000000000000) (-23632927695 / 1000000000000), orderedInterval (32126804892 / 1000000000000) (32126808970 / 1000000000000))
    | _ => (orderedInterval (-48071547739 / 1000000000000) (-48071547730 / 1000000000000), orderedInterval (-8135760091 / 1000000000000) (-8135760083 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (9944293214 / 1000000000000) (9944294354 / 1000000000000)
      | 1 => orderedInterval (764386884 / 1000000000000) (764387693 / 1000000000000)
      | 2 => orderedInterval (801308927 / 1000000000000) (801308939 / 1000000000000)
      | 3 => orderedInterval (3079525275 / 1000000000000) (3079533117 / 1000000000000)
      | 4 => orderedInterval (-215086071 / 1000000000000) (-215086045 / 1000000000000)
      | 5 => orderedInterval (1176622629 / 1000000000000) (1176623867 / 1000000000000)
      | 6 => orderedInterval (-8160834104 / 1000000000000) (-8160828803 / 1000000000000)
      | 7 => orderedInterval (-6664979703 / 1000000000000) (-6664979614 / 1000000000000)
      | _ => orderedInterval (10496957553 / 1000000000000) (10496957978 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-15980253983 / 1000000000000) (-15980252906 / 1000000000000)
      | 1 => orderedInterval (-2123238919 / 1000000000000) (-2123237765 / 1000000000000)
      | 2 => orderedInterval (-1140194722 / 1000000000000) (-1140194700 / 1000000000000)
      | 3 => orderedInterval (-13468429028 / 1000000000000) (-13468411918 / 1000000000000)
      | 4 => orderedInterval (-4569911669 / 1000000000000) (-4569911627 / 1000000000000)
      | 5 => orderedInterval (-4882112785 / 1000000000000) (-4882111201 / 1000000000000)
      | 6 => orderedInterval (-4381660433 / 1000000000000) (-4381655833 / 1000000000000)
      | 7 => orderedInterval (-605303295 / 1000000000000) (-605303222 / 1000000000000)
      | _ => orderedInterval (-2879576089 / 1000000000000) (-2879575371 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-9494873830 / 1000000000000) (-9494872792 / 1000000000000)
      | 1 => orderedInterval (-4401501444 / 1000000000000) (-4401499693 / 1000000000000)
      | 2 => orderedInterval (-1874554279 / 1000000000000) (-1874554240 / 1000000000000)
      | 3 => orderedInterval (-7392274886 / 1000000000000) (-7392237099 / 1000000000000)
      | 4 => orderedInterval (141356861 / 1000000000000) (141356931 / 1000000000000)
      | 5 => orderedInterval (-1256228546 / 1000000000000) (-1256226512 / 1000000000000)
      | 6 => orderedInterval (7496512844 / 1000000000000) (7496516859 / 1000000000000)
      | 7 => orderedInterval (5592940210 / 1000000000000) (5592940273 / 1000000000000)
      | _ => orderedInterval (-20457755208 / 1000000000000) (-20457753924 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (14434315587 / 1000000000000) (14434316592 / 1000000000000)
      | 1 => orderedInterval (8772506960 / 1000000000000) (8772509668 / 1000000000000)
      | 2 => orderedInterval (6639120261 / 1000000000000) (6639120330 / 1000000000000)
      | 3 => orderedInterval (55770626832 / 1000000000000) (55770710622 / 1000000000000)
      | 4 => orderedInterval (7289745803 / 1000000000000) (7289745921 / 1000000000000)
      | 5 => orderedInterval (11440196326 / 1000000000000) (11440198932 / 1000000000000)
      | 6 => orderedInterval (3900805845 / 1000000000000) (3900809330 / 1000000000000)
      | 7 => orderedInterval (471445906 / 1000000000000) (471445962 / 1000000000000)
      | _ => orderedInterval (13964503445 / 1000000000000) (13964505781 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (9054921840 / 1000000000000) (9054922828 / 1000000000000)
      | 1 => orderedInterval (11583717344 / 1000000000000) (11583721579 / 1000000000000)
      | 2 => orderedInterval (4627332599 / 1000000000000) (4627332727 / 1000000000000)
      | 3 => orderedInterval (19222674828 / 1000000000000) (19222861664 / 1000000000000)
      | 4 => orderedInterval (1358686495 / 1000000000000) (1358686700 / 1000000000000)
      | 5 => orderedInterval (59309611 / 1000000000000) (59312969 / 1000000000000)
      | 6 => orderedInterval (-7881342856 / 1000000000000) (-7881339812 / 1000000000000)
      | 7 => orderedInterval (-5969273017 / 1000000000000) (-5969272965 / 1000000000000)
      | _ => orderedInterval (44308868308 / 1000000000000) (44308872610 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (11222194604 / 1000000000000) (11222211486 / 1000000000000)
    | 1 => orderedInterval (-50030680923 / 1000000000000) (-50030654543 / 1000000000000)
    | 2 => orderedInterval (-31646378278 / 1000000000000) (-31646330197 / 1000000000000)
    | 3 => orderedInterval (122683266965 / 1000000000000) (122683363138 / 1000000000000)
    | _ => orderedInterval (76364895152 / 1000000000000) (76365098300 / 1000000000000)

theorem compactCertificate343_stateChecks0 :
    compactCertificate343.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (431 / 2)) (orderedInterval (25342978679 / 1000000000000) (25342980892 / 1000000000000), orderedInterval (-48140917836 / 1000000000000) (-48140915624 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (634945298545331 / 4000000000000)) (orderedInterval (40811522597 / 1000000000000) (40811548975 / 1000000000000), orderedInterval (-48553459645 / 1000000000000) (-48553433267 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 82 12 (205328263775123 / 800000000000)) (orderedInterval (-8197873482 / 1000000000000) (-8197873457 / 1000000000000), orderedInterval (49140275157 / 1000000000000) (49140275182 / 1000000000000))) = true
  rfl'

theorem compactCertificate343_stateChecks1 :
    compactCertificate343.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 15 12 (185275454539417 / 4000000000000)) (orderedInterval (2617122252 / 1000000000000) (2617122266 / 1000000000000), orderedInterval (-117238475434 / 1000000000000) (-117238475420 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 40 12 (497675932041349 / 4000000000000)) (orderedInterval (-31777228252 / 1000000000000) (-31777225458 / 1000000000000), orderedInterval (64213378675 / 1000000000000) (64213381469 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 108 12 (1351286967248433 / 4000000000000)) (orderedInterval (-27472688808 / 1000000000000) (-27472679247 / 1000000000000), orderedInterval (33652207292 / 1000000000000) (33652216853 / 1000000000000))) = true
  rfl'

theorem compactCertificate343_stateChecks2 :
    compactCertificate343.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 79 12 (995351864083129 / 4000000000000)) (orderedInterval (-50128517828 / 1000000000000) (-50128517814 / 1000000000000), orderedInterval (-6644456040 / 1000000000000) (-6644456027 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 136 12 (1705552384335517 / 4000000000000)) (orderedInterval (-3218835722 / 1000000000000) (-3218835720 / 1000000000000), orderedInterval (38509521037 / 1000000000000) (38509521039 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 100 12 (1256302166886103 / 4000000000000)) (orderedInterval (29047764668 / 1000000000000) (29047764669 / 1000000000000), orderedInterval (34351309918 / 1000000000000) (34351309919 / 1000000000000))) = true
  rfl'

theorem compactCertificate343_stateChecks3 :
    compactCertificate343.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 153 12 (1927490596604569 / 4000000000000)) (orderedInterval (-33139141027 / 1000000000000) (-33139099832 / 1000000000000), orderedInterval (14965377984 / 1000000000000) (14965419179 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 89 12 (1112837214810001 / 4000000000000)) (orderedInterval (27305265195 / 1000000000000) (27305271080 / 1000000000000), orderedInterval (-39326295451 / 1000000000000) (-39326289566 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 157 12 (1974749166107909 / 4000000000000)) (orderedInterval (-33990768786 / 1000000000000) (-33990768782 / 1000000000000), orderedInterval (-11547776048 / 1000000000000) (-11547776043 / 1000000000000))) = true
  rfl'

theorem compactCertificate343_stateChecks4 :
    compactCertificate343.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 147 12 (1845066828702521 / 4000000000000)) (orderedInterval (-8748250452 / 1000000000000) (-8748250451 / 1000000000000), orderedInterval (-36096255097 / 1000000000000) (-36096255096 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 105 12 (1316726749683593 / 4000000000000)) (orderedInterval (-4367462123 / 1000000000000) (-4367462122 / 1000000000000), orderedInterval (-43752639066 / 1000000000000) (-43752639065 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 119 12 (1493027796124047 / 4000000000000)) (orderedInterval (-7900436568 / 1000000000000) (-7900436567 / 1000000000000), orderedInterval (-40525388796 / 1000000000000) (-40525388795 / 1000000000000))) = true
  rfl'

theorem compactCertificate343_stateChecks5 :
    compactCertificate343.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 99 12 (1244730920435743 / 4000000000000)) (orderedInterval (-36792662396 / 1000000000000) (-36792662395 / 1000000000000), orderedInterval (-26248790763 / 1000000000000) (-26248790762 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 88 12 (1099757517106603 / 4000000000000)) (orderedInterval (-32297980573 / 1000000000000) (-32297959304 / 1000000000000), orderedInterval (35728501207 / 1000000000000) (35728522476 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 127 12 (318752593565697 / 800000000000)) (orderedInterval (-9639634567 / 1000000000000) (-9639634566 / 1000000000000), orderedInterval (-38780381430 / 1000000000000) (-38780381429 / 1000000000000))) = true
  rfl'

theorem compactCertificate343_stateChecks6 :
    compactCertificate343.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (881686448832659 / 4000000000000)) (orderedInterval (51710228062 / 1000000000000) (51710228064 / 1000000000000), orderedInterval (14519547393 / 1000000000000) (14519547394 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 60 12 (747415367085499 / 4000000000000)) (orderedInterval (-44120273266 / 1000000000000) (-44120180571 / 1000000000000), orderedInterval (38333851481 / 1000000000000) (38333944176 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (467697833113897 / 4000000000000)) (orderedInterval (-73412373518 / 1000000000000) (-73412373510 / 1000000000000), orderedInterval (-7121442715 / 1000000000000) (-7121442707 / 1000000000000))) = true
  rfl'

theorem compactCertificate343_stateChecks7 :
    compactCertificate343.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 20 12 (251529450141399 / 4000000000000)) (orderedInterval (74513612281 / 1000000000000) (74513612282 / 1000000000000), orderedInterval (67021682386 / 1000000000000) (67021682387 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (682951386581197 / 4000000000000)) (orderedInterval (58231140745 / 1000000000000) (58231143443 / 1000000000000), orderedInterval (-18548772165 / 1000000000000) (-18548769467 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 74 12 (932511731066669 / 4000000000000)) (orderedInterval (51775231083 / 1000000000000) (51775231095 / 1000000000000), orderedInterval (6966647321 / 1000000000000) (6966647332 / 1000000000000))) = true
  rfl'

theorem compactCertificate343_stateChecks8 :
    compactCertificate343.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 31 12 (394302166886103 / 4000000000000)) (orderedInterval (-74034172432 / 1000000000000) (-74034167409 / 1000000000000), orderedInterval (31633717926 / 1000000000000) (31633722950 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 128 12 (1602816417390263 / 4000000000000)) (orderedInterval (-23632931774 / 1000000000000) (-23632927695 / 1000000000000), orderedInterval (32126804892 / 1000000000000) (32126808970 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 85 12 (1070607085790617 / 4000000000000)) (orderedInterval (-48071547739 / 1000000000000) (-48071547730 / 1000000000000), orderedInterval (-8135760091 / 1000000000000) (-8135760083 / 1000000000000))) = true
  rfl'

theorem compactCertificate343_states : ∀ j,
    BesselStateValid (compactCertificate343.point j) (compactCertificate343.state j) :=
  compactCertificate343.statesValid_of_checks3 compactCertificate343_stateChecks0
    compactCertificate343_stateChecks1 compactCertificate343_stateChecks2
    compactCertificate343_stateChecks3 compactCertificate343_stateChecks4
    compactCertificate343_stateChecks5 compactCertificate343_stateChecks6
    compactCertificate343_stateChecks7 compactCertificate343_stateChecks8

theorem compactCertificate343_chunkChecks0_0 :
    compactCertificate343.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (431 / 2) 0 (IntervalRat.scale (431 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (25342978679 / 1000000000000) (25342980892 / 1000000000000), orderedInterval (-48140917836 / 1000000000000) (-48140915624 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (634945298545331 / 4000000000000) 0 (IntervalRat.scale (431 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (40811522597 / 1000000000000) (40811548975 / 1000000000000), orderedInterval (-48553459645 / 1000000000000) (-48553433267 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (205328263775123 / 800000000000) 0 (IntervalRat.scale (431 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-8197873482 / 1000000000000) (-8197873457 / 1000000000000), orderedInterval (49140275157 / 1000000000000) (49140275182 / 1000000000000)))) (orderedInterval (9944293214 / 1000000000000) (9944294354 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (185275454539417 / 4000000000000) 0 (IntervalRat.scale (431 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (2617122252 / 1000000000000) (2617122266 / 1000000000000), orderedInterval (-117238475434 / 1000000000000) (-117238475420 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (497675932041349 / 4000000000000) 0 (IntervalRat.scale (431 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-31777228252 / 1000000000000) (-31777225458 / 1000000000000), orderedInterval (64213378675 / 1000000000000) (64213381469 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1351286967248433 / 4000000000000) 0 (IntervalRat.scale (431 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-27472688808 / 1000000000000) (-27472679247 / 1000000000000), orderedInterval (33652207292 / 1000000000000) (33652216853 / 1000000000000)))) (orderedInterval (764386884 / 1000000000000) (764387693 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (995351864083129 / 4000000000000) 0 (IntervalRat.scale (431 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-50128517828 / 1000000000000) (-50128517814 / 1000000000000), orderedInterval (-6644456040 / 1000000000000) (-6644456027 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1705552384335517 / 4000000000000) 0 (IntervalRat.scale (431 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-3218835722 / 1000000000000) (-3218835720 / 1000000000000), orderedInterval (38509521037 / 1000000000000) (38509521039 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1256302166886103 / 4000000000000) 0 (IntervalRat.scale (431 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (29047764668 / 1000000000000) (29047764669 / 1000000000000), orderedInterval (34351309918 / 1000000000000) (34351309919 / 1000000000000)))) (orderedInterval (801308927 / 1000000000000) (801308939 / 1000000000000))) = true
  rfl'

theorem compactCertificate343_chunkChecks0_1 :
    compactCertificate343.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1927490596604569 / 4000000000000) 0 (IntervalRat.scale (431 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-33139141027 / 1000000000000) (-33139099832 / 1000000000000), orderedInterval (14965377984 / 1000000000000) (14965419179 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1112837214810001 / 4000000000000) 0 (IntervalRat.scale (431 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (27305265195 / 1000000000000) (27305271080 / 1000000000000), orderedInterval (-39326295451 / 1000000000000) (-39326289566 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1974749166107909 / 4000000000000) 0 (IntervalRat.scale (431 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-33990768786 / 1000000000000) (-33990768782 / 1000000000000), orderedInterval (-11547776048 / 1000000000000) (-11547776043 / 1000000000000)))) (orderedInterval (3079525275 / 1000000000000) (3079533117 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1845066828702521 / 4000000000000) 0 (IntervalRat.scale (431 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-8748250452 / 1000000000000) (-8748250451 / 1000000000000), orderedInterval (-36096255097 / 1000000000000) (-36096255096 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1316726749683593 / 4000000000000) 0 (IntervalRat.scale (431 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-4367462123 / 1000000000000) (-4367462122 / 1000000000000), orderedInterval (-43752639066 / 1000000000000) (-43752639065 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1493027796124047 / 4000000000000) 0 (IntervalRat.scale (431 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-7900436568 / 1000000000000) (-7900436567 / 1000000000000), orderedInterval (-40525388796 / 1000000000000) (-40525388795 / 1000000000000)))) (orderedInterval (-215086071 / 1000000000000) (-215086045 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1244730920435743 / 4000000000000) 0 (IntervalRat.scale (431 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-36792662396 / 1000000000000) (-36792662395 / 1000000000000), orderedInterval (-26248790763 / 1000000000000) (-26248790762 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1099757517106603 / 4000000000000) 0 (IntervalRat.scale (431 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-32297980573 / 1000000000000) (-32297959304 / 1000000000000), orderedInterval (35728501207 / 1000000000000) (35728522476 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (318752593565697 / 800000000000) 0 (IntervalRat.scale (431 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-9639634567 / 1000000000000) (-9639634566 / 1000000000000), orderedInterval (-38780381430 / 1000000000000) (-38780381429 / 1000000000000)))) (orderedInterval (1176622629 / 1000000000000) (1176623867 / 1000000000000))) = true
  rfl'

theorem compactCertificate343_chunkChecks0_2 :
    compactCertificate343.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (881686448832659 / 4000000000000) 0 (IntervalRat.scale (431 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (51710228062 / 1000000000000) (51710228064 / 1000000000000), orderedInterval (14519547393 / 1000000000000) (14519547394 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (747415367085499 / 4000000000000) 0 (IntervalRat.scale (431 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-44120273266 / 1000000000000) (-44120180571 / 1000000000000), orderedInterval (38333851481 / 1000000000000) (38333944176 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (467697833113897 / 4000000000000) 0 (IntervalRat.scale (431 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-73412373518 / 1000000000000) (-73412373510 / 1000000000000), orderedInterval (-7121442715 / 1000000000000) (-7121442707 / 1000000000000)))) (orderedInterval (-8160834104 / 1000000000000) (-8160828803 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (251529450141399 / 4000000000000) 0 (IntervalRat.scale (431 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (74513612281 / 1000000000000) (74513612282 / 1000000000000), orderedInterval (67021682386 / 1000000000000) (67021682387 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (682951386581197 / 4000000000000) 0 (IntervalRat.scale (431 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (58231140745 / 1000000000000) (58231143443 / 1000000000000), orderedInterval (-18548772165 / 1000000000000) (-18548769467 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (932511731066669 / 4000000000000) 0 (IntervalRat.scale (431 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (51775231083 / 1000000000000) (51775231095 / 1000000000000), orderedInterval (6966647321 / 1000000000000) (6966647332 / 1000000000000)))) (orderedInterval (-6664979703 / 1000000000000) (-6664979614 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (394302166886103 / 4000000000000) 0 (IntervalRat.scale (431 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-74034172432 / 1000000000000) (-74034167409 / 1000000000000), orderedInterval (31633717926 / 1000000000000) (31633722950 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1602816417390263 / 4000000000000) 0 (IntervalRat.scale (431 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-23632931774 / 1000000000000) (-23632927695 / 1000000000000), orderedInterval (32126804892 / 1000000000000) (32126808970 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1070607085790617 / 4000000000000) 0 (IntervalRat.scale (431 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-48071547739 / 1000000000000) (-48071547730 / 1000000000000), orderedInterval (-8135760091 / 1000000000000) (-8135760083 / 1000000000000)))) (orderedInterval (10496957553 / 1000000000000) (10496957978 / 1000000000000))) = true
  rfl'

theorem compactCertificate343_chunkChecks0 :
    compactCertificate343.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate343.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate343_chunkChecks0_0
    compactCertificate343_chunkChecks0_1 compactCertificate343_chunkChecks0_2

theorem compactCertificate343_chunkChecks1_0 :
    compactCertificate343.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (431 / 2) 1 (IntervalRat.scale (431 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (25342978679 / 1000000000000) (25342980892 / 1000000000000), orderedInterval (-48140917836 / 1000000000000) (-48140915624 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (634945298545331 / 4000000000000) 1 (IntervalRat.scale (431 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (40811522597 / 1000000000000) (40811548975 / 1000000000000), orderedInterval (-48553459645 / 1000000000000) (-48553433267 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (205328263775123 / 800000000000) 1 (IntervalRat.scale (431 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-8197873482 / 1000000000000) (-8197873457 / 1000000000000), orderedInterval (49140275157 / 1000000000000) (49140275182 / 1000000000000)))) (orderedInterval (-15980253983 / 1000000000000) (-15980252906 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (185275454539417 / 4000000000000) 1 (IntervalRat.scale (431 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (2617122252 / 1000000000000) (2617122266 / 1000000000000), orderedInterval (-117238475434 / 1000000000000) (-117238475420 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (497675932041349 / 4000000000000) 1 (IntervalRat.scale (431 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-31777228252 / 1000000000000) (-31777225458 / 1000000000000), orderedInterval (64213378675 / 1000000000000) (64213381469 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1351286967248433 / 4000000000000) 1 (IntervalRat.scale (431 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-27472688808 / 1000000000000) (-27472679247 / 1000000000000), orderedInterval (33652207292 / 1000000000000) (33652216853 / 1000000000000)))) (orderedInterval (-2123238919 / 1000000000000) (-2123237765 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (995351864083129 / 4000000000000) 1 (IntervalRat.scale (431 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-50128517828 / 1000000000000) (-50128517814 / 1000000000000), orderedInterval (-6644456040 / 1000000000000) (-6644456027 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1705552384335517 / 4000000000000) 1 (IntervalRat.scale (431 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-3218835722 / 1000000000000) (-3218835720 / 1000000000000), orderedInterval (38509521037 / 1000000000000) (38509521039 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1256302166886103 / 4000000000000) 1 (IntervalRat.scale (431 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (29047764668 / 1000000000000) (29047764669 / 1000000000000), orderedInterval (34351309918 / 1000000000000) (34351309919 / 1000000000000)))) (orderedInterval (-1140194722 / 1000000000000) (-1140194700 / 1000000000000))) = true
  rfl'

theorem compactCertificate343_chunkChecks1_1 :
    compactCertificate343.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1927490596604569 / 4000000000000) 1 (IntervalRat.scale (431 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-33139141027 / 1000000000000) (-33139099832 / 1000000000000), orderedInterval (14965377984 / 1000000000000) (14965419179 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1112837214810001 / 4000000000000) 1 (IntervalRat.scale (431 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (27305265195 / 1000000000000) (27305271080 / 1000000000000), orderedInterval (-39326295451 / 1000000000000) (-39326289566 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1974749166107909 / 4000000000000) 1 (IntervalRat.scale (431 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-33990768786 / 1000000000000) (-33990768782 / 1000000000000), orderedInterval (-11547776048 / 1000000000000) (-11547776043 / 1000000000000)))) (orderedInterval (-13468429028 / 1000000000000) (-13468411918 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1845066828702521 / 4000000000000) 1 (IntervalRat.scale (431 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-8748250452 / 1000000000000) (-8748250451 / 1000000000000), orderedInterval (-36096255097 / 1000000000000) (-36096255096 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1316726749683593 / 4000000000000) 1 (IntervalRat.scale (431 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-4367462123 / 1000000000000) (-4367462122 / 1000000000000), orderedInterval (-43752639066 / 1000000000000) (-43752639065 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1493027796124047 / 4000000000000) 1 (IntervalRat.scale (431 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-7900436568 / 1000000000000) (-7900436567 / 1000000000000), orderedInterval (-40525388796 / 1000000000000) (-40525388795 / 1000000000000)))) (orderedInterval (-4569911669 / 1000000000000) (-4569911627 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1244730920435743 / 4000000000000) 1 (IntervalRat.scale (431 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-36792662396 / 1000000000000) (-36792662395 / 1000000000000), orderedInterval (-26248790763 / 1000000000000) (-26248790762 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1099757517106603 / 4000000000000) 1 (IntervalRat.scale (431 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-32297980573 / 1000000000000) (-32297959304 / 1000000000000), orderedInterval (35728501207 / 1000000000000) (35728522476 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (318752593565697 / 800000000000) 1 (IntervalRat.scale (431 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-9639634567 / 1000000000000) (-9639634566 / 1000000000000), orderedInterval (-38780381430 / 1000000000000) (-38780381429 / 1000000000000)))) (orderedInterval (-4882112785 / 1000000000000) (-4882111201 / 1000000000000))) = true
  rfl'

theorem compactCertificate343_chunkChecks1_2 :
    compactCertificate343.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (881686448832659 / 4000000000000) 1 (IntervalRat.scale (431 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (51710228062 / 1000000000000) (51710228064 / 1000000000000), orderedInterval (14519547393 / 1000000000000) (14519547394 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (747415367085499 / 4000000000000) 1 (IntervalRat.scale (431 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-44120273266 / 1000000000000) (-44120180571 / 1000000000000), orderedInterval (38333851481 / 1000000000000) (38333944176 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (467697833113897 / 4000000000000) 1 (IntervalRat.scale (431 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-73412373518 / 1000000000000) (-73412373510 / 1000000000000), orderedInterval (-7121442715 / 1000000000000) (-7121442707 / 1000000000000)))) (orderedInterval (-4381660433 / 1000000000000) (-4381655833 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (251529450141399 / 4000000000000) 1 (IntervalRat.scale (431 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (74513612281 / 1000000000000) (74513612282 / 1000000000000), orderedInterval (67021682386 / 1000000000000) (67021682387 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (682951386581197 / 4000000000000) 1 (IntervalRat.scale (431 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (58231140745 / 1000000000000) (58231143443 / 1000000000000), orderedInterval (-18548772165 / 1000000000000) (-18548769467 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (932511731066669 / 4000000000000) 1 (IntervalRat.scale (431 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (51775231083 / 1000000000000) (51775231095 / 1000000000000), orderedInterval (6966647321 / 1000000000000) (6966647332 / 1000000000000)))) (orderedInterval (-605303295 / 1000000000000) (-605303222 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (394302166886103 / 4000000000000) 1 (IntervalRat.scale (431 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-74034172432 / 1000000000000) (-74034167409 / 1000000000000), orderedInterval (31633717926 / 1000000000000) (31633722950 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1602816417390263 / 4000000000000) 1 (IntervalRat.scale (431 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-23632931774 / 1000000000000) (-23632927695 / 1000000000000), orderedInterval (32126804892 / 1000000000000) (32126808970 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1070607085790617 / 4000000000000) 1 (IntervalRat.scale (431 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-48071547739 / 1000000000000) (-48071547730 / 1000000000000), orderedInterval (-8135760091 / 1000000000000) (-8135760083 / 1000000000000)))) (orderedInterval (-2879576089 / 1000000000000) (-2879575371 / 1000000000000))) = true
  rfl'

theorem compactCertificate343_chunkChecks1 :
    compactCertificate343.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate343.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate343_chunkChecks1_0
    compactCertificate343_chunkChecks1_1 compactCertificate343_chunkChecks1_2

theorem compactCertificate343_chunkChecks2_0 :
    compactCertificate343.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (431 / 2) 2 (IntervalRat.scale (431 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (25342978679 / 1000000000000) (25342980892 / 1000000000000), orderedInterval (-48140917836 / 1000000000000) (-48140915624 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (634945298545331 / 4000000000000) 2 (IntervalRat.scale (431 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (40811522597 / 1000000000000) (40811548975 / 1000000000000), orderedInterval (-48553459645 / 1000000000000) (-48553433267 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (205328263775123 / 800000000000) 2 (IntervalRat.scale (431 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-8197873482 / 1000000000000) (-8197873457 / 1000000000000), orderedInterval (49140275157 / 1000000000000) (49140275182 / 1000000000000)))) (orderedInterval (-9494873830 / 1000000000000) (-9494872792 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (185275454539417 / 4000000000000) 2 (IntervalRat.scale (431 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (2617122252 / 1000000000000) (2617122266 / 1000000000000), orderedInterval (-117238475434 / 1000000000000) (-117238475420 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (497675932041349 / 4000000000000) 2 (IntervalRat.scale (431 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-31777228252 / 1000000000000) (-31777225458 / 1000000000000), orderedInterval (64213378675 / 1000000000000) (64213381469 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1351286967248433 / 4000000000000) 2 (IntervalRat.scale (431 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-27472688808 / 1000000000000) (-27472679247 / 1000000000000), orderedInterval (33652207292 / 1000000000000) (33652216853 / 1000000000000)))) (orderedInterval (-4401501444 / 1000000000000) (-4401499693 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (995351864083129 / 4000000000000) 2 (IntervalRat.scale (431 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-50128517828 / 1000000000000) (-50128517814 / 1000000000000), orderedInterval (-6644456040 / 1000000000000) (-6644456027 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1705552384335517 / 4000000000000) 2 (IntervalRat.scale (431 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-3218835722 / 1000000000000) (-3218835720 / 1000000000000), orderedInterval (38509521037 / 1000000000000) (38509521039 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1256302166886103 / 4000000000000) 2 (IntervalRat.scale (431 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (29047764668 / 1000000000000) (29047764669 / 1000000000000), orderedInterval (34351309918 / 1000000000000) (34351309919 / 1000000000000)))) (orderedInterval (-1874554279 / 1000000000000) (-1874554240 / 1000000000000))) = true
  rfl'

theorem compactCertificate343_chunkChecks2_1 :
    compactCertificate343.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1927490596604569 / 4000000000000) 2 (IntervalRat.scale (431 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-33139141027 / 1000000000000) (-33139099832 / 1000000000000), orderedInterval (14965377984 / 1000000000000) (14965419179 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1112837214810001 / 4000000000000) 2 (IntervalRat.scale (431 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (27305265195 / 1000000000000) (27305271080 / 1000000000000), orderedInterval (-39326295451 / 1000000000000) (-39326289566 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1974749166107909 / 4000000000000) 2 (IntervalRat.scale (431 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-33990768786 / 1000000000000) (-33990768782 / 1000000000000), orderedInterval (-11547776048 / 1000000000000) (-11547776043 / 1000000000000)))) (orderedInterval (-7392274886 / 1000000000000) (-7392237099 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1845066828702521 / 4000000000000) 2 (IntervalRat.scale (431 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-8748250452 / 1000000000000) (-8748250451 / 1000000000000), orderedInterval (-36096255097 / 1000000000000) (-36096255096 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1316726749683593 / 4000000000000) 2 (IntervalRat.scale (431 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-4367462123 / 1000000000000) (-4367462122 / 1000000000000), orderedInterval (-43752639066 / 1000000000000) (-43752639065 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1493027796124047 / 4000000000000) 2 (IntervalRat.scale (431 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-7900436568 / 1000000000000) (-7900436567 / 1000000000000), orderedInterval (-40525388796 / 1000000000000) (-40525388795 / 1000000000000)))) (orderedInterval (141356861 / 1000000000000) (141356931 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1244730920435743 / 4000000000000) 2 (IntervalRat.scale (431 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-36792662396 / 1000000000000) (-36792662395 / 1000000000000), orderedInterval (-26248790763 / 1000000000000) (-26248790762 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1099757517106603 / 4000000000000) 2 (IntervalRat.scale (431 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-32297980573 / 1000000000000) (-32297959304 / 1000000000000), orderedInterval (35728501207 / 1000000000000) (35728522476 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (318752593565697 / 800000000000) 2 (IntervalRat.scale (431 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-9639634567 / 1000000000000) (-9639634566 / 1000000000000), orderedInterval (-38780381430 / 1000000000000) (-38780381429 / 1000000000000)))) (orderedInterval (-1256228546 / 1000000000000) (-1256226512 / 1000000000000))) = true
  rfl'

theorem compactCertificate343_chunkChecks2_2 :
    compactCertificate343.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (881686448832659 / 4000000000000) 2 (IntervalRat.scale (431 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (51710228062 / 1000000000000) (51710228064 / 1000000000000), orderedInterval (14519547393 / 1000000000000) (14519547394 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (747415367085499 / 4000000000000) 2 (IntervalRat.scale (431 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-44120273266 / 1000000000000) (-44120180571 / 1000000000000), orderedInterval (38333851481 / 1000000000000) (38333944176 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (467697833113897 / 4000000000000) 2 (IntervalRat.scale (431 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-73412373518 / 1000000000000) (-73412373510 / 1000000000000), orderedInterval (-7121442715 / 1000000000000) (-7121442707 / 1000000000000)))) (orderedInterval (7496512844 / 1000000000000) (7496516859 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (251529450141399 / 4000000000000) 2 (IntervalRat.scale (431 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (74513612281 / 1000000000000) (74513612282 / 1000000000000), orderedInterval (67021682386 / 1000000000000) (67021682387 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (682951386581197 / 4000000000000) 2 (IntervalRat.scale (431 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (58231140745 / 1000000000000) (58231143443 / 1000000000000), orderedInterval (-18548772165 / 1000000000000) (-18548769467 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (932511731066669 / 4000000000000) 2 (IntervalRat.scale (431 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (51775231083 / 1000000000000) (51775231095 / 1000000000000), orderedInterval (6966647321 / 1000000000000) (6966647332 / 1000000000000)))) (orderedInterval (5592940210 / 1000000000000) (5592940273 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (394302166886103 / 4000000000000) 2 (IntervalRat.scale (431 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-74034172432 / 1000000000000) (-74034167409 / 1000000000000), orderedInterval (31633717926 / 1000000000000) (31633722950 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1602816417390263 / 4000000000000) 2 (IntervalRat.scale (431 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-23632931774 / 1000000000000) (-23632927695 / 1000000000000), orderedInterval (32126804892 / 1000000000000) (32126808970 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1070607085790617 / 4000000000000) 2 (IntervalRat.scale (431 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-48071547739 / 1000000000000) (-48071547730 / 1000000000000), orderedInterval (-8135760091 / 1000000000000) (-8135760083 / 1000000000000)))) (orderedInterval (-20457755208 / 1000000000000) (-20457753924 / 1000000000000))) = true
  rfl'

theorem compactCertificate343_chunkChecks2 :
    compactCertificate343.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate343.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate343_chunkChecks2_0
    compactCertificate343_chunkChecks2_1 compactCertificate343_chunkChecks2_2

theorem compactCertificate343_chunkChecks3_0 :
    compactCertificate343.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (431 / 2) 3 (IntervalRat.scale (431 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (25342978679 / 1000000000000) (25342980892 / 1000000000000), orderedInterval (-48140917836 / 1000000000000) (-48140915624 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (634945298545331 / 4000000000000) 3 (IntervalRat.scale (431 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (40811522597 / 1000000000000) (40811548975 / 1000000000000), orderedInterval (-48553459645 / 1000000000000) (-48553433267 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (205328263775123 / 800000000000) 3 (IntervalRat.scale (431 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-8197873482 / 1000000000000) (-8197873457 / 1000000000000), orderedInterval (49140275157 / 1000000000000) (49140275182 / 1000000000000)))) (orderedInterval (14434315587 / 1000000000000) (14434316592 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (185275454539417 / 4000000000000) 3 (IntervalRat.scale (431 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (2617122252 / 1000000000000) (2617122266 / 1000000000000), orderedInterval (-117238475434 / 1000000000000) (-117238475420 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (497675932041349 / 4000000000000) 3 (IntervalRat.scale (431 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-31777228252 / 1000000000000) (-31777225458 / 1000000000000), orderedInterval (64213378675 / 1000000000000) (64213381469 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1351286967248433 / 4000000000000) 3 (IntervalRat.scale (431 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-27472688808 / 1000000000000) (-27472679247 / 1000000000000), orderedInterval (33652207292 / 1000000000000) (33652216853 / 1000000000000)))) (orderedInterval (8772506960 / 1000000000000) (8772509668 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (995351864083129 / 4000000000000) 3 (IntervalRat.scale (431 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-50128517828 / 1000000000000) (-50128517814 / 1000000000000), orderedInterval (-6644456040 / 1000000000000) (-6644456027 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1705552384335517 / 4000000000000) 3 (IntervalRat.scale (431 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-3218835722 / 1000000000000) (-3218835720 / 1000000000000), orderedInterval (38509521037 / 1000000000000) (38509521039 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1256302166886103 / 4000000000000) 3 (IntervalRat.scale (431 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (29047764668 / 1000000000000) (29047764669 / 1000000000000), orderedInterval (34351309918 / 1000000000000) (34351309919 / 1000000000000)))) (orderedInterval (6639120261 / 1000000000000) (6639120330 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate343_chunkChecks3_1 :
    compactCertificate343.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1927490596604569 / 4000000000000) 3 (IntervalRat.scale (431 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-33139141027 / 1000000000000) (-33139099832 / 1000000000000), orderedInterval (14965377984 / 1000000000000) (14965419179 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1112837214810001 / 4000000000000) 3 (IntervalRat.scale (431 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (27305265195 / 1000000000000) (27305271080 / 1000000000000), orderedInterval (-39326295451 / 1000000000000) (-39326289566 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1974749166107909 / 4000000000000) 3 (IntervalRat.scale (431 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-33990768786 / 1000000000000) (-33990768782 / 1000000000000), orderedInterval (-11547776048 / 1000000000000) (-11547776043 / 1000000000000)))) (orderedInterval (55770626832 / 1000000000000) (55770710622 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1845066828702521 / 4000000000000) 3 (IntervalRat.scale (431 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-8748250452 / 1000000000000) (-8748250451 / 1000000000000), orderedInterval (-36096255097 / 1000000000000) (-36096255096 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1316726749683593 / 4000000000000) 3 (IntervalRat.scale (431 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-4367462123 / 1000000000000) (-4367462122 / 1000000000000), orderedInterval (-43752639066 / 1000000000000) (-43752639065 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1493027796124047 / 4000000000000) 3 (IntervalRat.scale (431 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-7900436568 / 1000000000000) (-7900436567 / 1000000000000), orderedInterval (-40525388796 / 1000000000000) (-40525388795 / 1000000000000)))) (orderedInterval (7289745803 / 1000000000000) (7289745921 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1244730920435743 / 4000000000000) 3 (IntervalRat.scale (431 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-36792662396 / 1000000000000) (-36792662395 / 1000000000000), orderedInterval (-26248790763 / 1000000000000) (-26248790762 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1099757517106603 / 4000000000000) 3 (IntervalRat.scale (431 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-32297980573 / 1000000000000) (-32297959304 / 1000000000000), orderedInterval (35728501207 / 1000000000000) (35728522476 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (318752593565697 / 800000000000) 3 (IntervalRat.scale (431 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-9639634567 / 1000000000000) (-9639634566 / 1000000000000), orderedInterval (-38780381430 / 1000000000000) (-38780381429 / 1000000000000)))) (orderedInterval (11440196326 / 1000000000000) (11440198932 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate343_chunkChecks3_2 :
    compactCertificate343.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (881686448832659 / 4000000000000) 3 (IntervalRat.scale (431 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (51710228062 / 1000000000000) (51710228064 / 1000000000000), orderedInterval (14519547393 / 1000000000000) (14519547394 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (747415367085499 / 4000000000000) 3 (IntervalRat.scale (431 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-44120273266 / 1000000000000) (-44120180571 / 1000000000000), orderedInterval (38333851481 / 1000000000000) (38333944176 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (467697833113897 / 4000000000000) 3 (IntervalRat.scale (431 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-73412373518 / 1000000000000) (-73412373510 / 1000000000000), orderedInterval (-7121442715 / 1000000000000) (-7121442707 / 1000000000000)))) (orderedInterval (3900805845 / 1000000000000) (3900809330 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (251529450141399 / 4000000000000) 3 (IntervalRat.scale (431 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (74513612281 / 1000000000000) (74513612282 / 1000000000000), orderedInterval (67021682386 / 1000000000000) (67021682387 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (682951386581197 / 4000000000000) 3 (IntervalRat.scale (431 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (58231140745 / 1000000000000) (58231143443 / 1000000000000), orderedInterval (-18548772165 / 1000000000000) (-18548769467 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (932511731066669 / 4000000000000) 3 (IntervalRat.scale (431 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (51775231083 / 1000000000000) (51775231095 / 1000000000000), orderedInterval (6966647321 / 1000000000000) (6966647332 / 1000000000000)))) (orderedInterval (471445906 / 1000000000000) (471445962 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (394302166886103 / 4000000000000) 3 (IntervalRat.scale (431 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-74034172432 / 1000000000000) (-74034167409 / 1000000000000), orderedInterval (31633717926 / 1000000000000) (31633722950 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1602816417390263 / 4000000000000) 3 (IntervalRat.scale (431 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-23632931774 / 1000000000000) (-23632927695 / 1000000000000), orderedInterval (32126804892 / 1000000000000) (32126808970 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1070607085790617 / 4000000000000) 3 (IntervalRat.scale (431 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-48071547739 / 1000000000000) (-48071547730 / 1000000000000), orderedInterval (-8135760091 / 1000000000000) (-8135760083 / 1000000000000)))) (orderedInterval (13964503445 / 1000000000000) (13964505781 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate343_chunkChecks3 :
    compactCertificate343.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate343.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate343_chunkChecks3_0
    compactCertificate343_chunkChecks3_1 compactCertificate343_chunkChecks3_2

theorem compactCertificate343_chunkChecks4_0 :
    compactCertificate343.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (431 / 2) 4 (IntervalRat.scale (431 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (25342978679 / 1000000000000) (25342980892 / 1000000000000), orderedInterval (-48140917836 / 1000000000000) (-48140915624 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (634945298545331 / 4000000000000) 4 (IntervalRat.scale (431 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (40811522597 / 1000000000000) (40811548975 / 1000000000000), orderedInterval (-48553459645 / 1000000000000) (-48553433267 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (205328263775123 / 800000000000) 4 (IntervalRat.scale (431 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-8197873482 / 1000000000000) (-8197873457 / 1000000000000), orderedInterval (49140275157 / 1000000000000) (49140275182 / 1000000000000)))) (orderedInterval (9054921840 / 1000000000000) (9054922828 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (185275454539417 / 4000000000000) 4 (IntervalRat.scale (431 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (2617122252 / 1000000000000) (2617122266 / 1000000000000), orderedInterval (-117238475434 / 1000000000000) (-117238475420 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (497675932041349 / 4000000000000) 4 (IntervalRat.scale (431 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-31777228252 / 1000000000000) (-31777225458 / 1000000000000), orderedInterval (64213378675 / 1000000000000) (64213381469 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1351286967248433 / 4000000000000) 4 (IntervalRat.scale (431 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-27472688808 / 1000000000000) (-27472679247 / 1000000000000), orderedInterval (33652207292 / 1000000000000) (33652216853 / 1000000000000)))) (orderedInterval (11583717344 / 1000000000000) (11583721579 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (995351864083129 / 4000000000000) 4 (IntervalRat.scale (431 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-50128517828 / 1000000000000) (-50128517814 / 1000000000000), orderedInterval (-6644456040 / 1000000000000) (-6644456027 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1705552384335517 / 4000000000000) 4 (IntervalRat.scale (431 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-3218835722 / 1000000000000) (-3218835720 / 1000000000000), orderedInterval (38509521037 / 1000000000000) (38509521039 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1256302166886103 / 4000000000000) 4 (IntervalRat.scale (431 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (29047764668 / 1000000000000) (29047764669 / 1000000000000), orderedInterval (34351309918 / 1000000000000) (34351309919 / 1000000000000)))) (orderedInterval (4627332599 / 1000000000000) (4627332727 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate343_chunkChecks4_1 :
    compactCertificate343.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1927490596604569 / 4000000000000) 4 (IntervalRat.scale (431 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-33139141027 / 1000000000000) (-33139099832 / 1000000000000), orderedInterval (14965377984 / 1000000000000) (14965419179 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1112837214810001 / 4000000000000) 4 (IntervalRat.scale (431 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (27305265195 / 1000000000000) (27305271080 / 1000000000000), orderedInterval (-39326295451 / 1000000000000) (-39326289566 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1974749166107909 / 4000000000000) 4 (IntervalRat.scale (431 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-33990768786 / 1000000000000) (-33990768782 / 1000000000000), orderedInterval (-11547776048 / 1000000000000) (-11547776043 / 1000000000000)))) (orderedInterval (19222674828 / 1000000000000) (19222861664 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1845066828702521 / 4000000000000) 4 (IntervalRat.scale (431 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-8748250452 / 1000000000000) (-8748250451 / 1000000000000), orderedInterval (-36096255097 / 1000000000000) (-36096255096 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1316726749683593 / 4000000000000) 4 (IntervalRat.scale (431 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-4367462123 / 1000000000000) (-4367462122 / 1000000000000), orderedInterval (-43752639066 / 1000000000000) (-43752639065 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1493027796124047 / 4000000000000) 4 (IntervalRat.scale (431 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-7900436568 / 1000000000000) (-7900436567 / 1000000000000), orderedInterval (-40525388796 / 1000000000000) (-40525388795 / 1000000000000)))) (orderedInterval (1358686495 / 1000000000000) (1358686700 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1244730920435743 / 4000000000000) 4 (IntervalRat.scale (431 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-36792662396 / 1000000000000) (-36792662395 / 1000000000000), orderedInterval (-26248790763 / 1000000000000) (-26248790762 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1099757517106603 / 4000000000000) 4 (IntervalRat.scale (431 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-32297980573 / 1000000000000) (-32297959304 / 1000000000000), orderedInterval (35728501207 / 1000000000000) (35728522476 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (318752593565697 / 800000000000) 4 (IntervalRat.scale (431 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-9639634567 / 1000000000000) (-9639634566 / 1000000000000), orderedInterval (-38780381430 / 1000000000000) (-38780381429 / 1000000000000)))) (orderedInterval (59309611 / 1000000000000) (59312969 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate343_chunkChecks4_2 :
    compactCertificate343.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (881686448832659 / 4000000000000) 4 (IntervalRat.scale (431 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (51710228062 / 1000000000000) (51710228064 / 1000000000000), orderedInterval (14519547393 / 1000000000000) (14519547394 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (747415367085499 / 4000000000000) 4 (IntervalRat.scale (431 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-44120273266 / 1000000000000) (-44120180571 / 1000000000000), orderedInterval (38333851481 / 1000000000000) (38333944176 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (467697833113897 / 4000000000000) 4 (IntervalRat.scale (431 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-73412373518 / 1000000000000) (-73412373510 / 1000000000000), orderedInterval (-7121442715 / 1000000000000) (-7121442707 / 1000000000000)))) (orderedInterval (-7881342856 / 1000000000000) (-7881339812 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (251529450141399 / 4000000000000) 4 (IntervalRat.scale (431 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (74513612281 / 1000000000000) (74513612282 / 1000000000000), orderedInterval (67021682386 / 1000000000000) (67021682387 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (682951386581197 / 4000000000000) 4 (IntervalRat.scale (431 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (58231140745 / 1000000000000) (58231143443 / 1000000000000), orderedInterval (-18548772165 / 1000000000000) (-18548769467 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (932511731066669 / 4000000000000) 4 (IntervalRat.scale (431 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (51775231083 / 1000000000000) (51775231095 / 1000000000000), orderedInterval (6966647321 / 1000000000000) (6966647332 / 1000000000000)))) (orderedInterval (-5969273017 / 1000000000000) (-5969272965 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (394302166886103 / 4000000000000) 4 (IntervalRat.scale (431 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-74034172432 / 1000000000000) (-74034167409 / 1000000000000), orderedInterval (31633717926 / 1000000000000) (31633722950 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1602816417390263 / 4000000000000) 4 (IntervalRat.scale (431 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-23632931774 / 1000000000000) (-23632927695 / 1000000000000), orderedInterval (32126804892 / 1000000000000) (32126808970 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1070607085790617 / 4000000000000) 4 (IntervalRat.scale (431 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-48071547739 / 1000000000000) (-48071547730 / 1000000000000), orderedInterval (-8135760091 / 1000000000000) (-8135760083 / 1000000000000)))) (orderedInterval (44308868308 / 1000000000000) (44308872610 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate343_chunkChecks4 :
    compactCertificate343.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate343.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate343_chunkChecks4_0
    compactCertificate343_chunkChecks4_1 compactCertificate343_chunkChecks4_2

theorem compactCertificate343_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate343.chunkCheck r b = true :=
  compactCertificate343.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate343_chunkChecks0
    · exact compactCertificate343_chunkChecks1
    · exact compactCertificate343_chunkChecks2
    · exact compactCertificate343_chunkChecks3
    · exact compactCertificate343_chunkChecks4)

theorem compactCertificate343_coefficient0 :
    compactCertificate343.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate343_coefficient1 :
    compactCertificate343.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate343_coefficient2 :
    compactCertificate343.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate343_coefficient3 :
    compactCertificate343.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate343_coefficient4 :
    compactCertificate343.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate343_coefficients : ∀ r : Fin 5,
    compactCertificate343.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate343_coefficient0
  · exact compactCertificate343_coefficient1
  · exact compactCertificate343_coefficient2
  · exact compactCertificate343_coefficient3
  · exact compactCertificate343_coefficient4

theorem compactCertificate343_lower : (1 : ℚ) ≤ compactCertificate343.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate343, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate343_proves {t : ℝ} (ht : t ∈ compactCertificate343.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate343.proves compactCertificate343_states compactCertificate343_chunks
    compactCertificate343_coefficients compactCertificate343_lower ht

end Erdos232
