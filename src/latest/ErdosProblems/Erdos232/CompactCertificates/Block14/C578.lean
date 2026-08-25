/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate578 : CompactCertificate where
  left := 449
  right := 450
  center := 899 / 2
  grid := fun i =>
    match i.val with
    | 0 => 143
    | 1 => 105
    | 2 => 170
    | 3 => 31
    | 4 => 83
    | 5 => 224
    | 6 => 165
    | 7 => 283
    | 8 => 209
    | 9 => 320
    | 10 => 185
    | 11 => 328
    | 12 => 306
    | 13 => 219
    | 14 => 248
    | 15 => 207
    | 16 => 183
    | 17 => 265
    | 18 => 146
    | 19 => 124
    | 20 => 78
    | 21 => 42
    | 22 => 113
    | 23 => 155
    | 24 => 65
    | 25 => 266
    | _ => 178
  point := fun i =>
    match i.val with
    | 0 => 899 / 2
    | 1 => 1324398662162999 / 4000000000000
    | 2 => 428283315855767 / 800000000000
    | 3 => 386456226521893 / 4000000000000
    | 4 => 1038075784002721 / 4000000000000
    | 5 => 2818577688065757 / 4000000000000
    | 6 => 2076151568006341 / 4000000000000
    | 7 => 3557521098648793 / 4000000000000
    | 8 => 2620453939746187 / 4000000000000
    | 9 => 4020450223544101 / 4000000000000
    | 10 => 2321208018826429 / 4000000000000
    | 11 => 4119024362716961 / 4000000000000
    | 12 => 3848526865437509 / 4000000000000
    | 13 => 2746490366509397 / 4000000000000
    | 14 => 3114227352008163 / 4000000000000
    | 15 => 2596318091581747 / 4000000000000
    | 16 => 2293925772340687 / 4000000000000
    | 17 => 664869098876013 / 800000000000
    | 18 => 1839062917634711 / 4000000000000
    | 19 => 1558994002343071 / 4000000000000
    | 20 => 975546060253813 / 4000000000000
    | 21 => 524651915724171 / 4000000000000
    | 22 => 1424532010525513 / 4000000000000
    | 23 => 1945076673385001 / 4000000000000
    | 24 => 822453939746187 / 4000000000000
    | 25 => 3343229603790827 / 4000000000000
    | _ => 2233122436486693 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-32405120301 / 1000000000000) (-32405120300 / 1000000000000), orderedInterval (-19100098369 / 1000000000000) (-19100098368 / 1000000000000))
    | 1 => (orderedInterval (-39547245186 / 1000000000000) (-39547219771 / 1000000000000), orderedInterval (19000632435 / 1000000000000) (19000657850 / 1000000000000))
    | 2 => (orderedInterval (30299550943 / 1000000000000) (30299650058 / 1000000000000), orderedInterval (-16493163559 / 1000000000000) (-16493064443 / 1000000000000))
    | 3 => (orderedInterval (-713412718 / 1000000000000) (-713412712 / 1000000000000), orderedInterval (-81168268791 / 1000000000000) (-81168268785 / 1000000000000))
    | 4 => (orderedInterval (21468578170 / 1000000000000) (21468579294 / 1000000000000), orderedInterval (-44675197964 / 1000000000000) (-44675196840 / 1000000000000))
    | 5 => (orderedInterval (29754719916 / 1000000000000) (29754728234 / 1000000000000), orderedInterval (-4277714080 / 1000000000000) (-4277705763 / 1000000000000))
    | 6 => (orderedInterval (-34808228012 / 1000000000000) (-34808227871 / 1000000000000), orderedInterval (-3829738667 / 1000000000000) (-3829738527 / 1000000000000))
    | 7 => (orderedInterval (-23780487506 / 1000000000000) (-23780487495 / 1000000000000), orderedInterval (-12245908628 / 1000000000000) (-12245908617 / 1000000000000))
    | 8 => (orderedInterval (19943054107 / 1000000000000) (19943056008 / 1000000000000), orderedInterval (-23974454471 / 1000000000000) (-23974452570 / 1000000000000))
    | 9 => (orderedInterval (13963905325 / 1000000000000) (13963905326 / 1000000000000), orderedInterval (20930841217 / 1000000000000) (20930841218 / 1000000000000))
    | 10 => (orderedInterval (3552198592 / 1000000000000) (3552198593 / 1000000000000), orderedInterval (-32933765909 / 1000000000000) (-32933765908 / 1000000000000))
    | 11 => (orderedInterval (2456960379 / 1000000000000) (2456960380 / 1000000000000), orderedInterval (24741225345 / 1000000000000) (24741225346 / 1000000000000))
    | 12 => (orderedInterval (25718500254 / 1000000000000) (25718509207 / 1000000000000), orderedInterval (-497868072 / 1000000000000) (-497859119 / 1000000000000))
    | 13 => (orderedInterval (17217817659 / 1000000000000) (17217818178 / 1000000000000), orderedInterval (-25126727924 / 1000000000000) (-25126727405 / 1000000000000))
    | 14 => (orderedInterval (6438249647 / 1000000000000) (6438249648 / 1000000000000), orderedInterval (27856970568 / 1000000000000) (27856970569 / 1000000000000))
    | 15 => (orderedInterval (13479597065 / 1000000000000) (13479597148 / 1000000000000), orderedInterval (-28278822142 / 1000000000000) (-28278822058 / 1000000000000))
    | 16 => (orderedInterval (20026327342 / 1000000000000) (20026329078 / 1000000000000), orderedInterval (-26645319611 / 1000000000000) (-26645317874 / 1000000000000))
    | 17 => (orderedInterval (16759177424 / 1000000000000) (16759177808 / 1000000000000), orderedInterval (-22035957649 / 1000000000000) (-22035957265 / 1000000000000))
    | 18 => (orderedInterval (35465210261 / 1000000000000) (35465222812 / 1000000000000), orderedInterval (-11302630399 / 1000000000000) (-11302617847 / 1000000000000))
    | 19 => (orderedInterval (33476640781 / 1000000000000) (33476640782 / 1000000000000), orderedInterval (22600501909 / 1000000000000) (22600501910 / 1000000000000))
    | 20 => (orderedInterval (-18609902163 / 1000000000000) (-18609901669 / 1000000000000), orderedInterval (47619525512 / 1000000000000) (47619526006 / 1000000000000))
    | 21 => (orderedInterval (37109289 / 1000000000000) (37109295 / 1000000000000), orderedInterval (69668275378 / 1000000000000) (69668275384 / 1000000000000))
    | 22 => (orderedInterval (-39755804699 / 1000000000000) (-39755793626 / 1000000000000), orderedInterval (14445563585 / 1000000000000) (14445574658 / 1000000000000))
    | 23 => (orderedInterval (-3880292958 / 1000000000000) (-3880292957 / 1000000000000), orderedInterval (-35970113901 / 1000000000000) (-35970113900 / 1000000000000))
    | 24 => (orderedInterval (-45158728212 / 1000000000000) (-45158657990 / 1000000000000), orderedInterval (32619560630 / 1000000000000) (32619630852 / 1000000000000))
    | 25 => (orderedInterval (22107131889 / 1000000000000) (22107131890 / 1000000000000), orderedInterval (16508187258 / 1000000000000) (16508187259 / 1000000000000))
    | _ => (orderedInterval (-4635561797 / 1000000000000) (-4635561795 / 1000000000000), orderedInterval (33453130797 / 1000000000000) (33453130799 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-11434746710 / 1000000000000) (-11434740625 / 1000000000000)
      | 1 => orderedInterval (-1323657680 / 1000000000000) (-1323656993 / 1000000000000)
      | 2 => orderedInterval (1215469637 / 1000000000000) (1215469709 / 1000000000000)
      | 3 => orderedInterval (-1868757386 / 1000000000000) (-1868757208 / 1000000000000)
      | 4 => orderedInterval (1131286447 / 1000000000000) (1131286712 / 1000000000000)
      | 5 => orderedInterval (-561281208 / 1000000000000) (-561281054 / 1000000000000)
      | 6 => orderedInterval (-8171247941 / 1000000000000) (-8171245806 / 1000000000000)
      | 7 => orderedInterval (1198630217 / 1000000000000) (1198630522 / 1000000000000)
      | _ => orderedInterval (-1202037148 / 1000000000000) (-1202036600 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-8592890722 / 1000000000000) (-8592883584 / 1000000000000)
      | 1 => orderedInterval (-275765376 / 1000000000000) (-275764364 / 1000000000000)
      | 2 => orderedInterval (-97113309 / 1000000000000) (-97113198 / 1000000000000)
      | 3 => orderedInterval (-3409150060 / 1000000000000) (-3409149690 / 1000000000000)
      | 4 => orderedInterval (-3854417717 / 1000000000000) (-3854417209 / 1000000000000)
      | 5 => orderedInterval (430684369 / 1000000000000) (430684578 / 1000000000000)
      | 6 => orderedInterval (1580462272 / 1000000000000) (1580464438 / 1000000000000)
      | 7 => orderedInterval (2347178102 / 1000000000000) (2347178350 / 1000000000000)
      | _ => orderedInterval (-10204403421 / 1000000000000) (-10204403052 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (10541230321 / 1000000000000) (10541238757 / 1000000000000)
      | 1 => orderedInterval (4937049254 / 1000000000000) (4937050808 / 1000000000000)
      | 2 => orderedInterval (-3895052211 / 1000000000000) (-3895052033 / 1000000000000)
      | 3 => orderedInterval (10141981209 / 1000000000000) (10141982002 / 1000000000000)
      | 4 => orderedInterval (-1565543619 / 1000000000000) (-1565542619 / 1000000000000)
      | 5 => orderedInterval (73029976 / 1000000000000) (73030266 / 1000000000000)
      | 6 => orderedInterval (7531943032 / 1000000000000) (7531945240 / 1000000000000)
      | 7 => orderedInterval (-919347327 / 1000000000000) (-919347120 / 1000000000000)
      | _ => orderedInterval (4959850488 / 1000000000000) (4959850836 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (9111420189 / 1000000000000) (9111430175 / 1000000000000)
      | 1 => orderedInterval (-877301568 / 1000000000000) (-877299152 / 1000000000000)
      | 2 => orderedInterval (-1123368558 / 1000000000000) (-1123368271 / 1000000000000)
      | 3 => orderedInterval (4522832659 / 1000000000000) (4522834397 / 1000000000000)
      | 4 => orderedInterval (9116633029 / 1000000000000) (9116635035 / 1000000000000)
      | 5 => orderedInterval (1382572871 / 1000000000000) (1382573286 / 1000000000000)
      | 6 => orderedInterval (-1364369369 / 1000000000000) (-1364367117 / 1000000000000)
      | 7 => orderedInterval (-3293045955 / 1000000000000) (-3293045780 / 1000000000000)
      | _ => orderedInterval (20634481762 / 1000000000000) (20634482202 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-9415717276 / 1000000000000) (-9415705404 / 1000000000000)
      | 1 => orderedInterval (-12682863206 / 1000000000000) (-12682859424 / 1000000000000)
      | 2 => orderedInterval (13421041369 / 1000000000000) (13421041845 / 1000000000000)
      | 3 => orderedInterval (-51699283201 / 1000000000000) (-51699279342 / 1000000000000)
      | 4 => orderedInterval (-1215121826 / 1000000000000) (-1215117735 / 1000000000000)
      | 5 => orderedInterval (2648701946 / 1000000000000) (2648702555 / 1000000000000)
      | 6 => orderedInterval (-7324029972 / 1000000000000) (-7324027669 / 1000000000000)
      | 7 => orderedInterval (777320406 / 1000000000000) (777320557 / 1000000000000)
      | _ => orderedInterval (-19545679680 / 1000000000000) (-19545679020 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-21016341772 / 1000000000000) (-21016331343 / 1000000000000)
    | 1 => orderedInterval (-22075415862 / 1000000000000) (-22075403731 / 1000000000000)
    | 2 => orderedInterval (31805141123 / 1000000000000) (31805156137 / 1000000000000)
    | 3 => orderedInterval (38109855060 / 1000000000000) (38109874775 / 1000000000000)
    | _ => orderedInterval (-85035631440 / 1000000000000) (-85035603637 / 1000000000000)

theorem compactCertificate578_stateChecks0 :
    compactCertificate578.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 143 12 (899 / 2)) (orderedInterval (-32405120301 / 1000000000000) (-32405120300 / 1000000000000), orderedInterval (-19100098369 / 1000000000000) (-19100098368 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 105 12 (1324398662162999 / 4000000000000)) (orderedInterval (-39547245186 / 1000000000000) (-39547219771 / 1000000000000), orderedInterval (19000632435 / 1000000000000) (19000657850 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 170 12 (428283315855767 / 800000000000)) (orderedInterval (30299550943 / 1000000000000) (30299650058 / 1000000000000), orderedInterval (-16493163559 / 1000000000000) (-16493064443 / 1000000000000))) = true
  rfl'

theorem compactCertificate578_stateChecks1 :
    compactCertificate578.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 31 12 (386456226521893 / 4000000000000)) (orderedInterval (-713412718 / 1000000000000) (-713412712 / 1000000000000), orderedInterval (-81168268791 / 1000000000000) (-81168268785 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 83 12 (1038075784002721 / 4000000000000)) (orderedInterval (21468578170 / 1000000000000) (21468579294 / 1000000000000), orderedInterval (-44675197964 / 1000000000000) (-44675196840 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 224 12 (2818577688065757 / 4000000000000)) (orderedInterval (29754719916 / 1000000000000) (29754728234 / 1000000000000), orderedInterval (-4277714080 / 1000000000000) (-4277705763 / 1000000000000))) = true
  rfl'

theorem compactCertificate578_stateChecks2 :
    compactCertificate578.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 165 12 (2076151568006341 / 4000000000000)) (orderedInterval (-34808228012 / 1000000000000) (-34808227871 / 1000000000000), orderedInterval (-3829738667 / 1000000000000) (-3829738527 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 283 12 (3557521098648793 / 4000000000000)) (orderedInterval (-23780487506 / 1000000000000) (-23780487495 / 1000000000000), orderedInterval (-12245908628 / 1000000000000) (-12245908617 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 209 12 (2620453939746187 / 4000000000000)) (orderedInterval (19943054107 / 1000000000000) (19943056008 / 1000000000000), orderedInterval (-23974454471 / 1000000000000) (-23974452570 / 1000000000000))) = true
  rfl'

theorem compactCertificate578_stateChecks3 :
    compactCertificate578.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 320 12 (4020450223544101 / 4000000000000)) (orderedInterval (13963905325 / 1000000000000) (13963905326 / 1000000000000), orderedInterval (20930841217 / 1000000000000) (20930841218 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 185 12 (2321208018826429 / 4000000000000)) (orderedInterval (3552198592 / 1000000000000) (3552198593 / 1000000000000), orderedInterval (-32933765909 / 1000000000000) (-32933765908 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 328 12 (4119024362716961 / 4000000000000)) (orderedInterval (2456960379 / 1000000000000) (2456960380 / 1000000000000), orderedInterval (24741225345 / 1000000000000) (24741225346 / 1000000000000))) = true
  rfl'

theorem compactCertificate578_stateChecks4 :
    compactCertificate578.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 306 12 (3848526865437509 / 4000000000000)) (orderedInterval (25718500254 / 1000000000000) (25718509207 / 1000000000000), orderedInterval (-497868072 / 1000000000000) (-497859119 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 219 12 (2746490366509397 / 4000000000000)) (orderedInterval (17217817659 / 1000000000000) (17217818178 / 1000000000000), orderedInterval (-25126727924 / 1000000000000) (-25126727405 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 248 12 (3114227352008163 / 4000000000000)) (orderedInterval (6438249647 / 1000000000000) (6438249648 / 1000000000000), orderedInterval (27856970568 / 1000000000000) (27856970569 / 1000000000000))) = true
  rfl'

theorem compactCertificate578_stateChecks5 :
    compactCertificate578.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 207 12 (2596318091581747 / 4000000000000)) (orderedInterval (13479597065 / 1000000000000) (13479597148 / 1000000000000), orderedInterval (-28278822142 / 1000000000000) (-28278822058 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 183 12 (2293925772340687 / 4000000000000)) (orderedInterval (20026327342 / 1000000000000) (20026329078 / 1000000000000), orderedInterval (-26645319611 / 1000000000000) (-26645317874 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 265 12 (664869098876013 / 800000000000)) (orderedInterval (16759177424 / 1000000000000) (16759177808 / 1000000000000), orderedInterval (-22035957649 / 1000000000000) (-22035957265 / 1000000000000))) = true
  rfl'

theorem compactCertificate578_stateChecks6 :
    compactCertificate578.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 146 12 (1839062917634711 / 4000000000000)) (orderedInterval (35465210261 / 1000000000000) (35465222812 / 1000000000000), orderedInterval (-11302630399 / 1000000000000) (-11302617847 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 124 12 (1558994002343071 / 4000000000000)) (orderedInterval (33476640781 / 1000000000000) (33476640782 / 1000000000000), orderedInterval (22600501909 / 1000000000000) (22600501910 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 78 12 (975546060253813 / 4000000000000)) (orderedInterval (-18609902163 / 1000000000000) (-18609901669 / 1000000000000), orderedInterval (47619525512 / 1000000000000) (47619526006 / 1000000000000))) = true
  rfl'

theorem compactCertificate578_stateChecks7 :
    compactCertificate578.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 42 12 (524651915724171 / 4000000000000)) (orderedInterval (37109289 / 1000000000000) (37109295 / 1000000000000), orderedInterval (69668275378 / 1000000000000) (69668275384 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 113 12 (1424532010525513 / 4000000000000)) (orderedInterval (-39755804699 / 1000000000000) (-39755793626 / 1000000000000), orderedInterval (14445563585 / 1000000000000) (14445574658 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 155 12 (1945076673385001 / 4000000000000)) (orderedInterval (-3880292958 / 1000000000000) (-3880292957 / 1000000000000), orderedInterval (-35970113901 / 1000000000000) (-35970113900 / 1000000000000))) = true
  rfl'

theorem compactCertificate578_stateChecks8 :
    compactCertificate578.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 65 12 (822453939746187 / 4000000000000)) (orderedInterval (-45158728212 / 1000000000000) (-45158657990 / 1000000000000), orderedInterval (32619560630 / 1000000000000) (32619630852 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 266 12 (3343229603790827 / 4000000000000)) (orderedInterval (22107131889 / 1000000000000) (22107131890 / 1000000000000), orderedInterval (16508187258 / 1000000000000) (16508187259 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 178 12 (2233122436486693 / 4000000000000)) (orderedInterval (-4635561797 / 1000000000000) (-4635561795 / 1000000000000), orderedInterval (33453130797 / 1000000000000) (33453130799 / 1000000000000))) = true
  rfl'

theorem compactCertificate578_states : ∀ j,
    BesselStateValid (compactCertificate578.point j) (compactCertificate578.state j) :=
  compactCertificate578.statesValid_of_checks3 compactCertificate578_stateChecks0
    compactCertificate578_stateChecks1 compactCertificate578_stateChecks2
    compactCertificate578_stateChecks3 compactCertificate578_stateChecks4
    compactCertificate578_stateChecks5 compactCertificate578_stateChecks6
    compactCertificate578_stateChecks7 compactCertificate578_stateChecks8

theorem compactCertificate578_chunkChecks0_0 :
    compactCertificate578.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (899 / 2) 0 (IntervalRat.scale (899 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-32405120301 / 1000000000000) (-32405120300 / 1000000000000), orderedInterval (-19100098369 / 1000000000000) (-19100098368 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1324398662162999 / 4000000000000) 0 (IntervalRat.scale (899 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-39547245186 / 1000000000000) (-39547219771 / 1000000000000), orderedInterval (19000632435 / 1000000000000) (19000657850 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (428283315855767 / 800000000000) 0 (IntervalRat.scale (899 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (30299550943 / 1000000000000) (30299650058 / 1000000000000), orderedInterval (-16493163559 / 1000000000000) (-16493064443 / 1000000000000)))) (orderedInterval (-11434746710 / 1000000000000) (-11434740625 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (386456226521893 / 4000000000000) 0 (IntervalRat.scale (899 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-713412718 / 1000000000000) (-713412712 / 1000000000000), orderedInterval (-81168268791 / 1000000000000) (-81168268785 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (1038075784002721 / 4000000000000) 0 (IntervalRat.scale (899 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (21468578170 / 1000000000000) (21468579294 / 1000000000000), orderedInterval (-44675197964 / 1000000000000) (-44675196840 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2818577688065757 / 4000000000000) 0 (IntervalRat.scale (899 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29754719916 / 1000000000000) (29754728234 / 1000000000000), orderedInterval (-4277714080 / 1000000000000) (-4277705763 / 1000000000000)))) (orderedInterval (-1323657680 / 1000000000000) (-1323656993 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (2076151568006341 / 4000000000000) 0 (IntervalRat.scale (899 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-34808228012 / 1000000000000) (-34808227871 / 1000000000000), orderedInterval (-3829738667 / 1000000000000) (-3829738527 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3557521098648793 / 4000000000000) 0 (IntervalRat.scale (899 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-23780487506 / 1000000000000) (-23780487495 / 1000000000000), orderedInterval (-12245908628 / 1000000000000) (-12245908617 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2620453939746187 / 4000000000000) 0 (IntervalRat.scale (899 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (19943054107 / 1000000000000) (19943056008 / 1000000000000), orderedInterval (-23974454471 / 1000000000000) (-23974452570 / 1000000000000)))) (orderedInterval (1215469637 / 1000000000000) (1215469709 / 1000000000000))) = true
  rfl'

theorem compactCertificate578_chunkChecks0_1 :
    compactCertificate578.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (4020450223544101 / 4000000000000) 0 (IntervalRat.scale (899 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (13963905325 / 1000000000000) (13963905326 / 1000000000000), orderedInterval (20930841217 / 1000000000000) (20930841218 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2321208018826429 / 4000000000000) 0 (IntervalRat.scale (899 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (3552198592 / 1000000000000) (3552198593 / 1000000000000), orderedInterval (-32933765909 / 1000000000000) (-32933765908 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (4119024362716961 / 4000000000000) 0 (IntervalRat.scale (899 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (2456960379 / 1000000000000) (2456960380 / 1000000000000), orderedInterval (24741225345 / 1000000000000) (24741225346 / 1000000000000)))) (orderedInterval (-1868757386 / 1000000000000) (-1868757208 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3848526865437509 / 4000000000000) 0 (IntervalRat.scale (899 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (25718500254 / 1000000000000) (25718509207 / 1000000000000), orderedInterval (-497868072 / 1000000000000) (-497859119 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2746490366509397 / 4000000000000) 0 (IntervalRat.scale (899 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (17217817659 / 1000000000000) (17217818178 / 1000000000000), orderedInterval (-25126727924 / 1000000000000) (-25126727405 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (3114227352008163 / 4000000000000) 0 (IntervalRat.scale (899 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (6438249647 / 1000000000000) (6438249648 / 1000000000000), orderedInterval (27856970568 / 1000000000000) (27856970569 / 1000000000000)))) (orderedInterval (1131286447 / 1000000000000) (1131286712 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2596318091581747 / 4000000000000) 0 (IntervalRat.scale (899 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (13479597065 / 1000000000000) (13479597148 / 1000000000000), orderedInterval (-28278822142 / 1000000000000) (-28278822058 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2293925772340687 / 4000000000000) 0 (IntervalRat.scale (899 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (20026327342 / 1000000000000) (20026329078 / 1000000000000), orderedInterval (-26645319611 / 1000000000000) (-26645317874 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (664869098876013 / 800000000000) 0 (IntervalRat.scale (899 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16759177424 / 1000000000000) (16759177808 / 1000000000000), orderedInterval (-22035957649 / 1000000000000) (-22035957265 / 1000000000000)))) (orderedInterval (-561281208 / 1000000000000) (-561281054 / 1000000000000))) = true
  rfl'

theorem compactCertificate578_chunkChecks0_2 :
    compactCertificate578.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1839062917634711 / 4000000000000) 0 (IntervalRat.scale (899 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (35465210261 / 1000000000000) (35465222812 / 1000000000000), orderedInterval (-11302630399 / 1000000000000) (-11302617847 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1558994002343071 / 4000000000000) 0 (IntervalRat.scale (899 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (33476640781 / 1000000000000) (33476640782 / 1000000000000), orderedInterval (22600501909 / 1000000000000) (22600501910 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (975546060253813 / 4000000000000) 0 (IntervalRat.scale (899 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-18609902163 / 1000000000000) (-18609901669 / 1000000000000), orderedInterval (47619525512 / 1000000000000) (47619526006 / 1000000000000)))) (orderedInterval (-8171247941 / 1000000000000) (-8171245806 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (524651915724171 / 4000000000000) 0 (IntervalRat.scale (899 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (37109289 / 1000000000000) (37109295 / 1000000000000), orderedInterval (69668275378 / 1000000000000) (69668275384 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1424532010525513 / 4000000000000) 0 (IntervalRat.scale (899 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-39755804699 / 1000000000000) (-39755793626 / 1000000000000), orderedInterval (14445563585 / 1000000000000) (14445574658 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1945076673385001 / 4000000000000) 0 (IntervalRat.scale (899 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-3880292958 / 1000000000000) (-3880292957 / 1000000000000), orderedInterval (-35970113901 / 1000000000000) (-35970113900 / 1000000000000)))) (orderedInterval (1198630217 / 1000000000000) (1198630522 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (822453939746187 / 4000000000000) 0 (IntervalRat.scale (899 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-45158728212 / 1000000000000) (-45158657990 / 1000000000000), orderedInterval (32619560630 / 1000000000000) (32619630852 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3343229603790827 / 4000000000000) 0 (IntervalRat.scale (899 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (22107131889 / 1000000000000) (22107131890 / 1000000000000), orderedInterval (16508187258 / 1000000000000) (16508187259 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2233122436486693 / 4000000000000) 0 (IntervalRat.scale (899 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-4635561797 / 1000000000000) (-4635561795 / 1000000000000), orderedInterval (33453130797 / 1000000000000) (33453130799 / 1000000000000)))) (orderedInterval (-1202037148 / 1000000000000) (-1202036600 / 1000000000000))) = true
  rfl'

theorem compactCertificate578_chunkChecks0 :
    compactCertificate578.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate578.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate578_chunkChecks0_0
    compactCertificate578_chunkChecks0_1 compactCertificate578_chunkChecks0_2

theorem compactCertificate578_chunkChecks1_0 :
    compactCertificate578.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (899 / 2) 1 (IntervalRat.scale (899 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-32405120301 / 1000000000000) (-32405120300 / 1000000000000), orderedInterval (-19100098369 / 1000000000000) (-19100098368 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1324398662162999 / 4000000000000) 1 (IntervalRat.scale (899 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-39547245186 / 1000000000000) (-39547219771 / 1000000000000), orderedInterval (19000632435 / 1000000000000) (19000657850 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (428283315855767 / 800000000000) 1 (IntervalRat.scale (899 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (30299550943 / 1000000000000) (30299650058 / 1000000000000), orderedInterval (-16493163559 / 1000000000000) (-16493064443 / 1000000000000)))) (orderedInterval (-8592890722 / 1000000000000) (-8592883584 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (386456226521893 / 4000000000000) 1 (IntervalRat.scale (899 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-713412718 / 1000000000000) (-713412712 / 1000000000000), orderedInterval (-81168268791 / 1000000000000) (-81168268785 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (1038075784002721 / 4000000000000) 1 (IntervalRat.scale (899 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (21468578170 / 1000000000000) (21468579294 / 1000000000000), orderedInterval (-44675197964 / 1000000000000) (-44675196840 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2818577688065757 / 4000000000000) 1 (IntervalRat.scale (899 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29754719916 / 1000000000000) (29754728234 / 1000000000000), orderedInterval (-4277714080 / 1000000000000) (-4277705763 / 1000000000000)))) (orderedInterval (-275765376 / 1000000000000) (-275764364 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (2076151568006341 / 4000000000000) 1 (IntervalRat.scale (899 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-34808228012 / 1000000000000) (-34808227871 / 1000000000000), orderedInterval (-3829738667 / 1000000000000) (-3829738527 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3557521098648793 / 4000000000000) 1 (IntervalRat.scale (899 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-23780487506 / 1000000000000) (-23780487495 / 1000000000000), orderedInterval (-12245908628 / 1000000000000) (-12245908617 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2620453939746187 / 4000000000000) 1 (IntervalRat.scale (899 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (19943054107 / 1000000000000) (19943056008 / 1000000000000), orderedInterval (-23974454471 / 1000000000000) (-23974452570 / 1000000000000)))) (orderedInterval (-97113309 / 1000000000000) (-97113198 / 1000000000000))) = true
  rfl'

theorem compactCertificate578_chunkChecks1_1 :
    compactCertificate578.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (4020450223544101 / 4000000000000) 1 (IntervalRat.scale (899 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (13963905325 / 1000000000000) (13963905326 / 1000000000000), orderedInterval (20930841217 / 1000000000000) (20930841218 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2321208018826429 / 4000000000000) 1 (IntervalRat.scale (899 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (3552198592 / 1000000000000) (3552198593 / 1000000000000), orderedInterval (-32933765909 / 1000000000000) (-32933765908 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (4119024362716961 / 4000000000000) 1 (IntervalRat.scale (899 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (2456960379 / 1000000000000) (2456960380 / 1000000000000), orderedInterval (24741225345 / 1000000000000) (24741225346 / 1000000000000)))) (orderedInterval (-3409150060 / 1000000000000) (-3409149690 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3848526865437509 / 4000000000000) 1 (IntervalRat.scale (899 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (25718500254 / 1000000000000) (25718509207 / 1000000000000), orderedInterval (-497868072 / 1000000000000) (-497859119 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2746490366509397 / 4000000000000) 1 (IntervalRat.scale (899 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (17217817659 / 1000000000000) (17217818178 / 1000000000000), orderedInterval (-25126727924 / 1000000000000) (-25126727405 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (3114227352008163 / 4000000000000) 1 (IntervalRat.scale (899 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (6438249647 / 1000000000000) (6438249648 / 1000000000000), orderedInterval (27856970568 / 1000000000000) (27856970569 / 1000000000000)))) (orderedInterval (-3854417717 / 1000000000000) (-3854417209 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2596318091581747 / 4000000000000) 1 (IntervalRat.scale (899 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (13479597065 / 1000000000000) (13479597148 / 1000000000000), orderedInterval (-28278822142 / 1000000000000) (-28278822058 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2293925772340687 / 4000000000000) 1 (IntervalRat.scale (899 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (20026327342 / 1000000000000) (20026329078 / 1000000000000), orderedInterval (-26645319611 / 1000000000000) (-26645317874 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (664869098876013 / 800000000000) 1 (IntervalRat.scale (899 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16759177424 / 1000000000000) (16759177808 / 1000000000000), orderedInterval (-22035957649 / 1000000000000) (-22035957265 / 1000000000000)))) (orderedInterval (430684369 / 1000000000000) (430684578 / 1000000000000))) = true
  rfl'

theorem compactCertificate578_chunkChecks1_2 :
    compactCertificate578.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1839062917634711 / 4000000000000) 1 (IntervalRat.scale (899 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (35465210261 / 1000000000000) (35465222812 / 1000000000000), orderedInterval (-11302630399 / 1000000000000) (-11302617847 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1558994002343071 / 4000000000000) 1 (IntervalRat.scale (899 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (33476640781 / 1000000000000) (33476640782 / 1000000000000), orderedInterval (22600501909 / 1000000000000) (22600501910 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (975546060253813 / 4000000000000) 1 (IntervalRat.scale (899 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-18609902163 / 1000000000000) (-18609901669 / 1000000000000), orderedInterval (47619525512 / 1000000000000) (47619526006 / 1000000000000)))) (orderedInterval (1580462272 / 1000000000000) (1580464438 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (524651915724171 / 4000000000000) 1 (IntervalRat.scale (899 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (37109289 / 1000000000000) (37109295 / 1000000000000), orderedInterval (69668275378 / 1000000000000) (69668275384 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1424532010525513 / 4000000000000) 1 (IntervalRat.scale (899 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-39755804699 / 1000000000000) (-39755793626 / 1000000000000), orderedInterval (14445563585 / 1000000000000) (14445574658 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1945076673385001 / 4000000000000) 1 (IntervalRat.scale (899 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-3880292958 / 1000000000000) (-3880292957 / 1000000000000), orderedInterval (-35970113901 / 1000000000000) (-35970113900 / 1000000000000)))) (orderedInterval (2347178102 / 1000000000000) (2347178350 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (822453939746187 / 4000000000000) 1 (IntervalRat.scale (899 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-45158728212 / 1000000000000) (-45158657990 / 1000000000000), orderedInterval (32619560630 / 1000000000000) (32619630852 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3343229603790827 / 4000000000000) 1 (IntervalRat.scale (899 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (22107131889 / 1000000000000) (22107131890 / 1000000000000), orderedInterval (16508187258 / 1000000000000) (16508187259 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2233122436486693 / 4000000000000) 1 (IntervalRat.scale (899 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-4635561797 / 1000000000000) (-4635561795 / 1000000000000), orderedInterval (33453130797 / 1000000000000) (33453130799 / 1000000000000)))) (orderedInterval (-10204403421 / 1000000000000) (-10204403052 / 1000000000000))) = true
  rfl'

theorem compactCertificate578_chunkChecks1 :
    compactCertificate578.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate578.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate578_chunkChecks1_0
    compactCertificate578_chunkChecks1_1 compactCertificate578_chunkChecks1_2

theorem compactCertificate578_chunkChecks2_0 :
    compactCertificate578.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (899 / 2) 2 (IntervalRat.scale (899 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-32405120301 / 1000000000000) (-32405120300 / 1000000000000), orderedInterval (-19100098369 / 1000000000000) (-19100098368 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1324398662162999 / 4000000000000) 2 (IntervalRat.scale (899 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-39547245186 / 1000000000000) (-39547219771 / 1000000000000), orderedInterval (19000632435 / 1000000000000) (19000657850 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (428283315855767 / 800000000000) 2 (IntervalRat.scale (899 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (30299550943 / 1000000000000) (30299650058 / 1000000000000), orderedInterval (-16493163559 / 1000000000000) (-16493064443 / 1000000000000)))) (orderedInterval (10541230321 / 1000000000000) (10541238757 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (386456226521893 / 4000000000000) 2 (IntervalRat.scale (899 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-713412718 / 1000000000000) (-713412712 / 1000000000000), orderedInterval (-81168268791 / 1000000000000) (-81168268785 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (1038075784002721 / 4000000000000) 2 (IntervalRat.scale (899 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (21468578170 / 1000000000000) (21468579294 / 1000000000000), orderedInterval (-44675197964 / 1000000000000) (-44675196840 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2818577688065757 / 4000000000000) 2 (IntervalRat.scale (899 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29754719916 / 1000000000000) (29754728234 / 1000000000000), orderedInterval (-4277714080 / 1000000000000) (-4277705763 / 1000000000000)))) (orderedInterval (4937049254 / 1000000000000) (4937050808 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (2076151568006341 / 4000000000000) 2 (IntervalRat.scale (899 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-34808228012 / 1000000000000) (-34808227871 / 1000000000000), orderedInterval (-3829738667 / 1000000000000) (-3829738527 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3557521098648793 / 4000000000000) 2 (IntervalRat.scale (899 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-23780487506 / 1000000000000) (-23780487495 / 1000000000000), orderedInterval (-12245908628 / 1000000000000) (-12245908617 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2620453939746187 / 4000000000000) 2 (IntervalRat.scale (899 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (19943054107 / 1000000000000) (19943056008 / 1000000000000), orderedInterval (-23974454471 / 1000000000000) (-23974452570 / 1000000000000)))) (orderedInterval (-3895052211 / 1000000000000) (-3895052033 / 1000000000000))) = true
  rfl'

theorem compactCertificate578_chunkChecks2_1 :
    compactCertificate578.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (4020450223544101 / 4000000000000) 2 (IntervalRat.scale (899 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (13963905325 / 1000000000000) (13963905326 / 1000000000000), orderedInterval (20930841217 / 1000000000000) (20930841218 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2321208018826429 / 4000000000000) 2 (IntervalRat.scale (899 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (3552198592 / 1000000000000) (3552198593 / 1000000000000), orderedInterval (-32933765909 / 1000000000000) (-32933765908 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (4119024362716961 / 4000000000000) 2 (IntervalRat.scale (899 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (2456960379 / 1000000000000) (2456960380 / 1000000000000), orderedInterval (24741225345 / 1000000000000) (24741225346 / 1000000000000)))) (orderedInterval (10141981209 / 1000000000000) (10141982002 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3848526865437509 / 4000000000000) 2 (IntervalRat.scale (899 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (25718500254 / 1000000000000) (25718509207 / 1000000000000), orderedInterval (-497868072 / 1000000000000) (-497859119 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2746490366509397 / 4000000000000) 2 (IntervalRat.scale (899 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (17217817659 / 1000000000000) (17217818178 / 1000000000000), orderedInterval (-25126727924 / 1000000000000) (-25126727405 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (3114227352008163 / 4000000000000) 2 (IntervalRat.scale (899 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (6438249647 / 1000000000000) (6438249648 / 1000000000000), orderedInterval (27856970568 / 1000000000000) (27856970569 / 1000000000000)))) (orderedInterval (-1565543619 / 1000000000000) (-1565542619 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2596318091581747 / 4000000000000) 2 (IntervalRat.scale (899 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (13479597065 / 1000000000000) (13479597148 / 1000000000000), orderedInterval (-28278822142 / 1000000000000) (-28278822058 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2293925772340687 / 4000000000000) 2 (IntervalRat.scale (899 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (20026327342 / 1000000000000) (20026329078 / 1000000000000), orderedInterval (-26645319611 / 1000000000000) (-26645317874 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (664869098876013 / 800000000000) 2 (IntervalRat.scale (899 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16759177424 / 1000000000000) (16759177808 / 1000000000000), orderedInterval (-22035957649 / 1000000000000) (-22035957265 / 1000000000000)))) (orderedInterval (73029976 / 1000000000000) (73030266 / 1000000000000))) = true
  rfl'

theorem compactCertificate578_chunkChecks2_2 :
    compactCertificate578.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1839062917634711 / 4000000000000) 2 (IntervalRat.scale (899 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (35465210261 / 1000000000000) (35465222812 / 1000000000000), orderedInterval (-11302630399 / 1000000000000) (-11302617847 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1558994002343071 / 4000000000000) 2 (IntervalRat.scale (899 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (33476640781 / 1000000000000) (33476640782 / 1000000000000), orderedInterval (22600501909 / 1000000000000) (22600501910 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (975546060253813 / 4000000000000) 2 (IntervalRat.scale (899 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-18609902163 / 1000000000000) (-18609901669 / 1000000000000), orderedInterval (47619525512 / 1000000000000) (47619526006 / 1000000000000)))) (orderedInterval (7531943032 / 1000000000000) (7531945240 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (524651915724171 / 4000000000000) 2 (IntervalRat.scale (899 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (37109289 / 1000000000000) (37109295 / 1000000000000), orderedInterval (69668275378 / 1000000000000) (69668275384 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1424532010525513 / 4000000000000) 2 (IntervalRat.scale (899 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-39755804699 / 1000000000000) (-39755793626 / 1000000000000), orderedInterval (14445563585 / 1000000000000) (14445574658 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1945076673385001 / 4000000000000) 2 (IntervalRat.scale (899 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-3880292958 / 1000000000000) (-3880292957 / 1000000000000), orderedInterval (-35970113901 / 1000000000000) (-35970113900 / 1000000000000)))) (orderedInterval (-919347327 / 1000000000000) (-919347120 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (822453939746187 / 4000000000000) 2 (IntervalRat.scale (899 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-45158728212 / 1000000000000) (-45158657990 / 1000000000000), orderedInterval (32619560630 / 1000000000000) (32619630852 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3343229603790827 / 4000000000000) 2 (IntervalRat.scale (899 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (22107131889 / 1000000000000) (22107131890 / 1000000000000), orderedInterval (16508187258 / 1000000000000) (16508187259 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2233122436486693 / 4000000000000) 2 (IntervalRat.scale (899 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-4635561797 / 1000000000000) (-4635561795 / 1000000000000), orderedInterval (33453130797 / 1000000000000) (33453130799 / 1000000000000)))) (orderedInterval (4959850488 / 1000000000000) (4959850836 / 1000000000000))) = true
  rfl'

theorem compactCertificate578_chunkChecks2 :
    compactCertificate578.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate578.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate578_chunkChecks2_0
    compactCertificate578_chunkChecks2_1 compactCertificate578_chunkChecks2_2

theorem compactCertificate578_chunkChecks3_0 :
    compactCertificate578.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (899 / 2) 3 (IntervalRat.scale (899 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-32405120301 / 1000000000000) (-32405120300 / 1000000000000), orderedInterval (-19100098369 / 1000000000000) (-19100098368 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1324398662162999 / 4000000000000) 3 (IntervalRat.scale (899 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-39547245186 / 1000000000000) (-39547219771 / 1000000000000), orderedInterval (19000632435 / 1000000000000) (19000657850 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (428283315855767 / 800000000000) 3 (IntervalRat.scale (899 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (30299550943 / 1000000000000) (30299650058 / 1000000000000), orderedInterval (-16493163559 / 1000000000000) (-16493064443 / 1000000000000)))) (orderedInterval (9111420189 / 1000000000000) (9111430175 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (386456226521893 / 4000000000000) 3 (IntervalRat.scale (899 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-713412718 / 1000000000000) (-713412712 / 1000000000000), orderedInterval (-81168268791 / 1000000000000) (-81168268785 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (1038075784002721 / 4000000000000) 3 (IntervalRat.scale (899 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (21468578170 / 1000000000000) (21468579294 / 1000000000000), orderedInterval (-44675197964 / 1000000000000) (-44675196840 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2818577688065757 / 4000000000000) 3 (IntervalRat.scale (899 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29754719916 / 1000000000000) (29754728234 / 1000000000000), orderedInterval (-4277714080 / 1000000000000) (-4277705763 / 1000000000000)))) (orderedInterval (-877301568 / 1000000000000) (-877299152 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (2076151568006341 / 4000000000000) 3 (IntervalRat.scale (899 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-34808228012 / 1000000000000) (-34808227871 / 1000000000000), orderedInterval (-3829738667 / 1000000000000) (-3829738527 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3557521098648793 / 4000000000000) 3 (IntervalRat.scale (899 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-23780487506 / 1000000000000) (-23780487495 / 1000000000000), orderedInterval (-12245908628 / 1000000000000) (-12245908617 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2620453939746187 / 4000000000000) 3 (IntervalRat.scale (899 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (19943054107 / 1000000000000) (19943056008 / 1000000000000), orderedInterval (-23974454471 / 1000000000000) (-23974452570 / 1000000000000)))) (orderedInterval (-1123368558 / 1000000000000) (-1123368271 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate578_chunkChecks3_1 :
    compactCertificate578.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (4020450223544101 / 4000000000000) 3 (IntervalRat.scale (899 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (13963905325 / 1000000000000) (13963905326 / 1000000000000), orderedInterval (20930841217 / 1000000000000) (20930841218 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2321208018826429 / 4000000000000) 3 (IntervalRat.scale (899 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (3552198592 / 1000000000000) (3552198593 / 1000000000000), orderedInterval (-32933765909 / 1000000000000) (-32933765908 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (4119024362716961 / 4000000000000) 3 (IntervalRat.scale (899 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (2456960379 / 1000000000000) (2456960380 / 1000000000000), orderedInterval (24741225345 / 1000000000000) (24741225346 / 1000000000000)))) (orderedInterval (4522832659 / 1000000000000) (4522834397 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3848526865437509 / 4000000000000) 3 (IntervalRat.scale (899 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (25718500254 / 1000000000000) (25718509207 / 1000000000000), orderedInterval (-497868072 / 1000000000000) (-497859119 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2746490366509397 / 4000000000000) 3 (IntervalRat.scale (899 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (17217817659 / 1000000000000) (17217818178 / 1000000000000), orderedInterval (-25126727924 / 1000000000000) (-25126727405 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (3114227352008163 / 4000000000000) 3 (IntervalRat.scale (899 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (6438249647 / 1000000000000) (6438249648 / 1000000000000), orderedInterval (27856970568 / 1000000000000) (27856970569 / 1000000000000)))) (orderedInterval (9116633029 / 1000000000000) (9116635035 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2596318091581747 / 4000000000000) 3 (IntervalRat.scale (899 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (13479597065 / 1000000000000) (13479597148 / 1000000000000), orderedInterval (-28278822142 / 1000000000000) (-28278822058 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2293925772340687 / 4000000000000) 3 (IntervalRat.scale (899 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (20026327342 / 1000000000000) (20026329078 / 1000000000000), orderedInterval (-26645319611 / 1000000000000) (-26645317874 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (664869098876013 / 800000000000) 3 (IntervalRat.scale (899 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16759177424 / 1000000000000) (16759177808 / 1000000000000), orderedInterval (-22035957649 / 1000000000000) (-22035957265 / 1000000000000)))) (orderedInterval (1382572871 / 1000000000000) (1382573286 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate578_chunkChecks3_2 :
    compactCertificate578.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1839062917634711 / 4000000000000) 3 (IntervalRat.scale (899 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (35465210261 / 1000000000000) (35465222812 / 1000000000000), orderedInterval (-11302630399 / 1000000000000) (-11302617847 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1558994002343071 / 4000000000000) 3 (IntervalRat.scale (899 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (33476640781 / 1000000000000) (33476640782 / 1000000000000), orderedInterval (22600501909 / 1000000000000) (22600501910 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (975546060253813 / 4000000000000) 3 (IntervalRat.scale (899 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-18609902163 / 1000000000000) (-18609901669 / 1000000000000), orderedInterval (47619525512 / 1000000000000) (47619526006 / 1000000000000)))) (orderedInterval (-1364369369 / 1000000000000) (-1364367117 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (524651915724171 / 4000000000000) 3 (IntervalRat.scale (899 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (37109289 / 1000000000000) (37109295 / 1000000000000), orderedInterval (69668275378 / 1000000000000) (69668275384 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1424532010525513 / 4000000000000) 3 (IntervalRat.scale (899 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-39755804699 / 1000000000000) (-39755793626 / 1000000000000), orderedInterval (14445563585 / 1000000000000) (14445574658 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1945076673385001 / 4000000000000) 3 (IntervalRat.scale (899 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-3880292958 / 1000000000000) (-3880292957 / 1000000000000), orderedInterval (-35970113901 / 1000000000000) (-35970113900 / 1000000000000)))) (orderedInterval (-3293045955 / 1000000000000) (-3293045780 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (822453939746187 / 4000000000000) 3 (IntervalRat.scale (899 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-45158728212 / 1000000000000) (-45158657990 / 1000000000000), orderedInterval (32619560630 / 1000000000000) (32619630852 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3343229603790827 / 4000000000000) 3 (IntervalRat.scale (899 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (22107131889 / 1000000000000) (22107131890 / 1000000000000), orderedInterval (16508187258 / 1000000000000) (16508187259 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2233122436486693 / 4000000000000) 3 (IntervalRat.scale (899 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-4635561797 / 1000000000000) (-4635561795 / 1000000000000), orderedInterval (33453130797 / 1000000000000) (33453130799 / 1000000000000)))) (orderedInterval (20634481762 / 1000000000000) (20634482202 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate578_chunkChecks3 :
    compactCertificate578.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate578.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate578_chunkChecks3_0
    compactCertificate578_chunkChecks3_1 compactCertificate578_chunkChecks3_2

theorem compactCertificate578_chunkChecks4_0 :
    compactCertificate578.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (899 / 2) 4 (IntervalRat.scale (899 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-32405120301 / 1000000000000) (-32405120300 / 1000000000000), orderedInterval (-19100098369 / 1000000000000) (-19100098368 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1324398662162999 / 4000000000000) 4 (IntervalRat.scale (899 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-39547245186 / 1000000000000) (-39547219771 / 1000000000000), orderedInterval (19000632435 / 1000000000000) (19000657850 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (428283315855767 / 800000000000) 4 (IntervalRat.scale (899 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (30299550943 / 1000000000000) (30299650058 / 1000000000000), orderedInterval (-16493163559 / 1000000000000) (-16493064443 / 1000000000000)))) (orderedInterval (-9415717276 / 1000000000000) (-9415705404 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (386456226521893 / 4000000000000) 4 (IntervalRat.scale (899 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-713412718 / 1000000000000) (-713412712 / 1000000000000), orderedInterval (-81168268791 / 1000000000000) (-81168268785 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (1038075784002721 / 4000000000000) 4 (IntervalRat.scale (899 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (21468578170 / 1000000000000) (21468579294 / 1000000000000), orderedInterval (-44675197964 / 1000000000000) (-44675196840 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2818577688065757 / 4000000000000) 4 (IntervalRat.scale (899 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29754719916 / 1000000000000) (29754728234 / 1000000000000), orderedInterval (-4277714080 / 1000000000000) (-4277705763 / 1000000000000)))) (orderedInterval (-12682863206 / 1000000000000) (-12682859424 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (2076151568006341 / 4000000000000) 4 (IntervalRat.scale (899 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-34808228012 / 1000000000000) (-34808227871 / 1000000000000), orderedInterval (-3829738667 / 1000000000000) (-3829738527 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3557521098648793 / 4000000000000) 4 (IntervalRat.scale (899 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-23780487506 / 1000000000000) (-23780487495 / 1000000000000), orderedInterval (-12245908628 / 1000000000000) (-12245908617 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2620453939746187 / 4000000000000) 4 (IntervalRat.scale (899 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (19943054107 / 1000000000000) (19943056008 / 1000000000000), orderedInterval (-23974454471 / 1000000000000) (-23974452570 / 1000000000000)))) (orderedInterval (13421041369 / 1000000000000) (13421041845 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate578_chunkChecks4_1 :
    compactCertificate578.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (4020450223544101 / 4000000000000) 4 (IntervalRat.scale (899 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (13963905325 / 1000000000000) (13963905326 / 1000000000000), orderedInterval (20930841217 / 1000000000000) (20930841218 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2321208018826429 / 4000000000000) 4 (IntervalRat.scale (899 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (3552198592 / 1000000000000) (3552198593 / 1000000000000), orderedInterval (-32933765909 / 1000000000000) (-32933765908 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (4119024362716961 / 4000000000000) 4 (IntervalRat.scale (899 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (2456960379 / 1000000000000) (2456960380 / 1000000000000), orderedInterval (24741225345 / 1000000000000) (24741225346 / 1000000000000)))) (orderedInterval (-51699283201 / 1000000000000) (-51699279342 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3848526865437509 / 4000000000000) 4 (IntervalRat.scale (899 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (25718500254 / 1000000000000) (25718509207 / 1000000000000), orderedInterval (-497868072 / 1000000000000) (-497859119 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2746490366509397 / 4000000000000) 4 (IntervalRat.scale (899 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (17217817659 / 1000000000000) (17217818178 / 1000000000000), orderedInterval (-25126727924 / 1000000000000) (-25126727405 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (3114227352008163 / 4000000000000) 4 (IntervalRat.scale (899 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (6438249647 / 1000000000000) (6438249648 / 1000000000000), orderedInterval (27856970568 / 1000000000000) (27856970569 / 1000000000000)))) (orderedInterval (-1215121826 / 1000000000000) (-1215117735 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2596318091581747 / 4000000000000) 4 (IntervalRat.scale (899 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (13479597065 / 1000000000000) (13479597148 / 1000000000000), orderedInterval (-28278822142 / 1000000000000) (-28278822058 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2293925772340687 / 4000000000000) 4 (IntervalRat.scale (899 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (20026327342 / 1000000000000) (20026329078 / 1000000000000), orderedInterval (-26645319611 / 1000000000000) (-26645317874 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (664869098876013 / 800000000000) 4 (IntervalRat.scale (899 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16759177424 / 1000000000000) (16759177808 / 1000000000000), orderedInterval (-22035957649 / 1000000000000) (-22035957265 / 1000000000000)))) (orderedInterval (2648701946 / 1000000000000) (2648702555 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate578_chunkChecks4_2 :
    compactCertificate578.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1839062917634711 / 4000000000000) 4 (IntervalRat.scale (899 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (35465210261 / 1000000000000) (35465222812 / 1000000000000), orderedInterval (-11302630399 / 1000000000000) (-11302617847 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1558994002343071 / 4000000000000) 4 (IntervalRat.scale (899 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (33476640781 / 1000000000000) (33476640782 / 1000000000000), orderedInterval (22600501909 / 1000000000000) (22600501910 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (975546060253813 / 4000000000000) 4 (IntervalRat.scale (899 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-18609902163 / 1000000000000) (-18609901669 / 1000000000000), orderedInterval (47619525512 / 1000000000000) (47619526006 / 1000000000000)))) (orderedInterval (-7324029972 / 1000000000000) (-7324027669 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (524651915724171 / 4000000000000) 4 (IntervalRat.scale (899 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (37109289 / 1000000000000) (37109295 / 1000000000000), orderedInterval (69668275378 / 1000000000000) (69668275384 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1424532010525513 / 4000000000000) 4 (IntervalRat.scale (899 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-39755804699 / 1000000000000) (-39755793626 / 1000000000000), orderedInterval (14445563585 / 1000000000000) (14445574658 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1945076673385001 / 4000000000000) 4 (IntervalRat.scale (899 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-3880292958 / 1000000000000) (-3880292957 / 1000000000000), orderedInterval (-35970113901 / 1000000000000) (-35970113900 / 1000000000000)))) (orderedInterval (777320406 / 1000000000000) (777320557 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (822453939746187 / 4000000000000) 4 (IntervalRat.scale (899 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-45158728212 / 1000000000000) (-45158657990 / 1000000000000), orderedInterval (32619560630 / 1000000000000) (32619630852 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3343229603790827 / 4000000000000) 4 (IntervalRat.scale (899 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (22107131889 / 1000000000000) (22107131890 / 1000000000000), orderedInterval (16508187258 / 1000000000000) (16508187259 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2233122436486693 / 4000000000000) 4 (IntervalRat.scale (899 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-4635561797 / 1000000000000) (-4635561795 / 1000000000000), orderedInterval (33453130797 / 1000000000000) (33453130799 / 1000000000000)))) (orderedInterval (-19545679680 / 1000000000000) (-19545679020 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate578_chunkChecks4 :
    compactCertificate578.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate578.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate578_chunkChecks4_0
    compactCertificate578_chunkChecks4_1 compactCertificate578_chunkChecks4_2

theorem compactCertificate578_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate578.chunkCheck r b = true :=
  compactCertificate578.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate578_chunkChecks0
    · exact compactCertificate578_chunkChecks1
    · exact compactCertificate578_chunkChecks2
    · exact compactCertificate578_chunkChecks3
    · exact compactCertificate578_chunkChecks4)

theorem compactCertificate578_coefficient0 :
    compactCertificate578.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate578_coefficient1 :
    compactCertificate578.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate578_coefficient2 :
    compactCertificate578.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate578_coefficient3 :
    compactCertificate578.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate578_coefficient4 :
    compactCertificate578.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate578_coefficients : ∀ r : Fin 5,
    compactCertificate578.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate578_coefficient0
  · exact compactCertificate578_coefficient1
  · exact compactCertificate578_coefficient2
  · exact compactCertificate578_coefficient3
  · exact compactCertificate578_coefficient4

theorem compactCertificate578_lower : (1 : ℚ) ≤ compactCertificate578.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate578, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate578_proves {t : ℝ} (ht : t ∈ compactCertificate578.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate578.proves compactCertificate578_states compactCertificate578_chunks
    compactCertificate578_coefficients compactCertificate578_lower ht

end Erdos232
