/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate357 : CompactCertificate where
  left := 228
  right := 229
  center := 457 / 2
  grid := fun i =>
    match i.val with
    | 0 => 73
    | 1 => 54
    | 2 => 87
    | 3 => 16
    | 4 => 42
    | 5 => 114
    | 6 => 84
    | 7 => 144
    | 8 => 106
    | 9 => 163
    | 10 => 94
    | 11 => 167
    | 12 => 156
    | 13 => 111
    | 14 => 126
    | 15 => 105
    | 16 => 93
    | 17 => 135
    | 18 => 74
    | 19 => 63
    | 20 => 39
    | 21 => 21
    | 22 => 58
    | 23 => 79
    | 24 => 33
    | 25 => 135
    | _ => 90
  point := fun i =>
    match i.val with
    | 0 => 457 / 2
    | 1 => 673248263190757 / 4000000000000
    | 2 => 217714655557381 / 800000000000
    | 3 => 196452164093999 / 4000000000000
    | 4 => 527698146039203 / 4000000000000
    | 5 => 1432803118404951 / 4000000000000
    | 6 => 1055396292078863 / 4000000000000
    | 7 => 1808439535130699 / 4000000000000
    | 8 => 1332088376489441 / 4000000000000
    | 9 => 2043766131434543 / 4000000000000
    | 10 => 1179968926144247 / 4000000000000
    | 11 => 2093875565919523 / 4000000000000
    | 12 => 1956370164076687 / 4000000000000
    | 13 => 1396158061729471 / 4000000000000
    | 14 => 1583094438117609 / 4000000000000
    | 15 => 1319819096610521 / 4000000000000
    | 16 => 1166100197952941 / 4000000000000
    | 17 => 337981288305159 / 800000000000
    | 18 => 934874030432773 / 4000000000000
    | 19 => 792503069044253 / 4000000000000
    | 20 => 495911623510559 / 4000000000000
    | 21 => 266702920451553 / 4000000000000
    | 22 => 724150310133659 / 4000000000000
    | 23 => 988765338973243 / 4000000000000
    | 24 => 418088376489441 / 4000000000000
    | 25 => 1699506038856961 / 4000000000000
    | _ => 1135191271940399 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (2712530141 / 1000000000000) (2712530146 / 1000000000000), orderedInterval (-52719605155 / 1000000000000) (-52719605149 / 1000000000000))
    | 1 => (orderedInterval (-32108083801 / 1000000000000) (-32108078082 / 1000000000000), orderedInterval (52549703969 / 1000000000000) (52549709688 / 1000000000000))
    | 2 => (orderedInterval (18401755806 / 1000000000000) (18401756320 / 1000000000000), orderedInterval (-44762540980 / 1000000000000) (-44762540466 / 1000000000000))
    | 3 => (orderedInterval (-41125919227 / 1000000000000) (-41125917707 / 1000000000000), orderedInterval (106585923411 / 1000000000000) (106585924931 / 1000000000000))
    | 4 => (orderedInterval (47962413329 / 1000000000000) (47962413330 / 1000000000000), orderedInterval (50070032483 / 1000000000000) (50070032484 / 1000000000000))
    | 5 => (orderedInterval (31512179666 / 1000000000000) (31512179667 / 1000000000000), orderedInterval (27960532446 / 1000000000000) (27960532447 / 1000000000000))
    | 6 => (orderedInterval (33129072261 / 1000000000000) (33129072262 / 1000000000000), orderedInterval (36204048871 / 1000000000000) (36204048872 / 1000000000000))
    | 7 => (orderedInterval (18176539118 / 1000000000000) (18176539119 / 1000000000000), orderedInterval (32808580507 / 1000000000000) (32808580508 / 1000000000000))
    | 8 => (orderedInterval (31312516761 / 1000000000000) (31312516762 / 1000000000000), orderedInterval (30468073728 / 1000000000000) (30468073729 / 1000000000000))
    | 9 => (orderedInterval (12200368656 / 1000000000000) (12200368717 / 1000000000000), orderedInterval (-33134820576 / 1000000000000) (-33134820515 / 1000000000000))
    | 10 => (orderedInterval (20935174305 / 1000000000000) (20935174306 / 1000000000000), orderedInterval (41435111126 / 1000000000000) (41435111127 / 1000000000000))
    | 11 => (orderedInterval (13320448391 / 1000000000000) (13320448487 / 1000000000000), orderedInterval (-32241932552 / 1000000000000) (-32241932455 / 1000000000000))
    | 12 => (orderedInterval (-7548030531 / 1000000000000) (-7548030522 / 1000000000000), orderedInterval (35287490336 / 1000000000000) (35287490344 / 1000000000000))
    | 13 => (orderedInterval (-38210483999 / 1000000000000) (-38210483998 / 1000000000000), orderedInterval (-19020815845 / 1000000000000) (-19020815844 / 1000000000000))
    | 14 => (orderedInterval (26385886424 / 1000000000000) (26385886425 / 1000000000000), orderedInterval (30171473909 / 1000000000000) (30171473910 / 1000000000000))
    | 15 => (orderedInterval (-33645749497 / 1000000000000) (-33645749496 / 1000000000000), orderedInterval (-28186904240 / 1000000000000) (-28186904239 / 1000000000000))
    | 16 => (orderedInterval (-6608944596 / 1000000000000) (-6608944595 / 1000000000000), orderedInterval (-46249680987 / 1000000000000) (-46249680986 / 1000000000000))
    | 17 => (orderedInterval (29247822599 / 1000000000000) (29247854220 / 1000000000000), orderedInterval (-25557944176 / 1000000000000) (-25557912556 / 1000000000000))
    | 18 => (orderedInterval (46887311338 / 1000000000000) (46887328580 / 1000000000000), orderedInterval (-23022998083 / 1000000000000) (-23022980842 / 1000000000000))
    | 19 => (orderedInterval (-47396350152 / 1000000000000) (-47396350151 / 1000000000000), orderedInterval (-30973672826 / 1000000000000) (-30973672825 / 1000000000000))
    | 20 => (orderedInterval (-56194628215 / 1000000000000) (-56194555279 / 1000000000000), orderedInterval (44691220529 / 1000000000000) (44691293465 / 1000000000000))
    | 21 => (orderedInterval (-97359810365 / 1000000000000) (-97359810358 / 1000000000000), orderedInterval (-7564599632 / 1000000000000) (-7564599625 / 1000000000000))
    | 22 => (orderedInterval (-22550045459 / 1000000000000) (-22550044559 / 1000000000000), orderedInterval (54907618424 / 1000000000000) (54907619324 / 1000000000000))
    | 23 => (orderedInterval (10558790645 / 1000000000000) (10558790698 / 1000000000000), orderedInterval (-49659344260 / 1000000000000) (-49659344207 / 1000000000000))
    | 24 => (orderedInterval (-77888380184 / 1000000000000) (-77888380099 / 1000000000000), orderedInterval (5281616490 / 1000000000000) (5281616575 / 1000000000000))
    | 25 => (orderedInterval (-38697371367 / 1000000000000) (-38697371130 / 1000000000000), orderedInterval (-890767629 / 1000000000000) (-890767392 / 1000000000000))
    | _ => (orderedInterval (45663790222 / 1000000000000) (45663793579 / 1000000000000), orderedInterval (-12651490565 / 1000000000000) (-12651487208 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (1855802939 / 1000000000000) (1855803041 / 1000000000000)
      | 1 => orderedInterval (-42811052 / 1000000000000) (-42811007 / 1000000000000)
      | 2 => orderedInterval (196124553 / 1000000000000) (196124567 / 1000000000000)
      | 3 => orderedInterval (1276846104 / 1000000000000) (1276846220 / 1000000000000)
      | 4 => orderedInterval (-3610555432 / 1000000000000) (-3610555403 / 1000000000000)
      | 5 => orderedInterval (738537702 / 1000000000000) (738538534 / 1000000000000)
      | 6 => orderedInterval (-6643729512 / 1000000000000) (-6643724322 / 1000000000000)
      | 7 => orderedInterval (1500136237 / 1000000000000) (1500136289 / 1000000000000)
      | _ => orderedInterval (-5887240959 / 1000000000000) (-5887240245 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-23663941437 / 1000000000000) (-23663941341 / 1000000000000)
      | 1 => orderedInterval (-2309030787 / 1000000000000) (-2309030751 / 1000000000000)
      | 2 => orderedInterval (-929057993 / 1000000000000) (-929057970 / 1000000000000)
      | 3 => orderedInterval (6628524799 / 1000000000000) (6628525043 / 1000000000000)
      | 4 => orderedInterval (-4375529975 / 1000000000000) (-4375529930 / 1000000000000)
      | 5 => orderedInterval (1696821953 / 1000000000000) (1696823482 / 1000000000000)
      | 6 => orderedInterval (6074750331 / 1000000000000) (6074754493 / 1000000000000)
      | 7 => orderedInterval (3170975296 / 1000000000000) (3170975341 / 1000000000000)
      | _ => orderedInterval (3097602170 / 1000000000000) (3097603078 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-2340985098 / 1000000000000) (-2340985003 / 1000000000000)
      | 1 => orderedInterval (4910864304 / 1000000000000) (4910864349 / 1000000000000)
      | 2 => orderedInterval (591445826 / 1000000000000) (591445866 / 1000000000000)
      | 3 => orderedInterval (-1712789170 / 1000000000000) (-1712788641 / 1000000000000)
      | 4 => orderedInterval (8226446895 / 1000000000000) (8226446969 / 1000000000000)
      | 5 => orderedInterval (-2372864667 / 1000000000000) (-2372861845 / 1000000000000)
      | 6 => orderedInterval (6338404243 / 1000000000000) (6338407896 / 1000000000000)
      | 7 => orderedInterval (458932539 / 1000000000000) (458932582 / 1000000000000)
      | _ => orderedInterval (2410034604 / 1000000000000) (2410035778 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (25147896502 / 1000000000000) (25147896602 / 1000000000000)
      | 1 => orderedInterval (7295368087 / 1000000000000) (7295368152 / 1000000000000)
      | 2 => orderedInterval (5556330701 / 1000000000000) (5556330774 / 1000000000000)
      | 3 => orderedInterval (-17317845539 / 1000000000000) (-17317844370 / 1000000000000)
      | 4 => orderedInterval (13415347980 / 1000000000000) (13415348106 / 1000000000000)
      | 5 => orderedInterval (-369899777 / 1000000000000) (-369894575 / 1000000000000)
      | 6 => orderedInterval (-5342043440 / 1000000000000) (-5342040046 / 1000000000000)
      | 7 => orderedInterval (-4204169798 / 1000000000000) (-4204169757 / 1000000000000)
      | _ => orderedInterval (-5027520392 / 1000000000000) (-5027518854 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (2939640233 / 1000000000000) (2939640341 / 1000000000000)
      | 1 => orderedInterval (-13396619247 / 1000000000000) (-13396619147 / 1000000000000)
      | 2 => orderedInterval (-5226655904 / 1000000000000) (-5226655769 / 1000000000000)
      | 3 => orderedInterval (2419541881 / 1000000000000) (2419544489 / 1000000000000)
      | 4 => orderedInterval (-18131132630 / 1000000000000) (-18131132410 / 1000000000000)
      | 5 => orderedInterval (8067153306 / 1000000000000) (8067162927 / 1000000000000)
      | 6 => orderedInterval (-6800995944 / 1000000000000) (-6800992643 / 1000000000000)
      | 7 => orderedInterval (-856862934 / 1000000000000) (-856862893 / 1000000000000)
      | _ => orderedInterval (17291184401 / 1000000000000) (17291186468 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-10616889420 / 1000000000000) (-10616882326 / 1000000000000)
    | 1 => orderedInterval (-10608885643 / 1000000000000) (-10608878555 / 1000000000000)
    | 2 => orderedInterval (16509489476 / 1000000000000) (16509497951 / 1000000000000)
    | 3 => orderedInterval (19153464324 / 1000000000000) (19153476032 / 1000000000000)
    | _ => orderedInterval (-13694746838 / 1000000000000) (-13694728637 / 1000000000000)

theorem compactCertificate357_stateChecks0 :
    compactCertificate357.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 73 12 (457 / 2)) (orderedInterval (2712530141 / 1000000000000) (2712530146 / 1000000000000), orderedInterval (-52719605155 / 1000000000000) (-52719605149 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (673248263190757 / 4000000000000)) (orderedInterval (-32108083801 / 1000000000000) (-32108078082 / 1000000000000), orderedInterval (52549703969 / 1000000000000) (52549709688 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 87 12 (217714655557381 / 800000000000)) (orderedInterval (18401755806 / 1000000000000) (18401756320 / 1000000000000), orderedInterval (-44762540980 / 1000000000000) (-44762540466 / 1000000000000))) = true
  rfl'

theorem compactCertificate357_stateChecks1 :
    compactCertificate357.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 16 12 (196452164093999 / 4000000000000)) (orderedInterval (-41125919227 / 1000000000000) (-41125917707 / 1000000000000), orderedInterval (106585923411 / 1000000000000) (106585924931 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 42 12 (527698146039203 / 4000000000000)) (orderedInterval (47962413329 / 1000000000000) (47962413330 / 1000000000000), orderedInterval (50070032483 / 1000000000000) (50070032484 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 114 12 (1432803118404951 / 4000000000000)) (orderedInterval (31512179666 / 1000000000000) (31512179667 / 1000000000000), orderedInterval (27960532446 / 1000000000000) (27960532447 / 1000000000000))) = true
  rfl'

theorem compactCertificate357_stateChecks2 :
    compactCertificate357.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 84 12 (1055396292078863 / 4000000000000)) (orderedInterval (33129072261 / 1000000000000) (33129072262 / 1000000000000), orderedInterval (36204048871 / 1000000000000) (36204048872 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 144 12 (1808439535130699 / 4000000000000)) (orderedInterval (18176539118 / 1000000000000) (18176539119 / 1000000000000), orderedInterval (32808580507 / 1000000000000) (32808580508 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 106 12 (1332088376489441 / 4000000000000)) (orderedInterval (31312516761 / 1000000000000) (31312516762 / 1000000000000), orderedInterval (30468073728 / 1000000000000) (30468073729 / 1000000000000))) = true
  rfl'

theorem compactCertificate357_stateChecks3 :
    compactCertificate357.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 163 12 (2043766131434543 / 4000000000000)) (orderedInterval (12200368656 / 1000000000000) (12200368717 / 1000000000000), orderedInterval (-33134820576 / 1000000000000) (-33134820515 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 94 12 (1179968926144247 / 4000000000000)) (orderedInterval (20935174305 / 1000000000000) (20935174306 / 1000000000000), orderedInterval (41435111126 / 1000000000000) (41435111127 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 167 12 (2093875565919523 / 4000000000000)) (orderedInterval (13320448391 / 1000000000000) (13320448487 / 1000000000000), orderedInterval (-32241932552 / 1000000000000) (-32241932455 / 1000000000000))) = true
  rfl'

theorem compactCertificate357_stateChecks4 :
    compactCertificate357.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 156 12 (1956370164076687 / 4000000000000)) (orderedInterval (-7548030531 / 1000000000000) (-7548030522 / 1000000000000), orderedInterval (35287490336 / 1000000000000) (35287490344 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 111 12 (1396158061729471 / 4000000000000)) (orderedInterval (-38210483999 / 1000000000000) (-38210483998 / 1000000000000), orderedInterval (-19020815845 / 1000000000000) (-19020815844 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 126 12 (1583094438117609 / 4000000000000)) (orderedInterval (26385886424 / 1000000000000) (26385886425 / 1000000000000), orderedInterval (30171473909 / 1000000000000) (30171473910 / 1000000000000))) = true
  rfl'

theorem compactCertificate357_stateChecks5 :
    compactCertificate357.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 105 12 (1319819096610521 / 4000000000000)) (orderedInterval (-33645749497 / 1000000000000) (-33645749496 / 1000000000000), orderedInterval (-28186904240 / 1000000000000) (-28186904239 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 93 12 (1166100197952941 / 4000000000000)) (orderedInterval (-6608944596 / 1000000000000) (-6608944595 / 1000000000000), orderedInterval (-46249680987 / 1000000000000) (-46249680986 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 135 12 (337981288305159 / 800000000000)) (orderedInterval (29247822599 / 1000000000000) (29247854220 / 1000000000000), orderedInterval (-25557944176 / 1000000000000) (-25557912556 / 1000000000000))) = true
  rfl'

theorem compactCertificate357_stateChecks6 :
    compactCertificate357.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 74 12 (934874030432773 / 4000000000000)) (orderedInterval (46887311338 / 1000000000000) (46887328580 / 1000000000000), orderedInterval (-23022998083 / 1000000000000) (-23022980842 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (792503069044253 / 4000000000000)) (orderedInterval (-47396350152 / 1000000000000) (-47396350151 / 1000000000000), orderedInterval (-30973672826 / 1000000000000) (-30973672825 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 39 12 (495911623510559 / 4000000000000)) (orderedInterval (-56194628215 / 1000000000000) (-56194555279 / 1000000000000), orderedInterval (44691220529 / 1000000000000) (44691293465 / 1000000000000))) = true
  rfl'

theorem compactCertificate357_stateChecks7 :
    compactCertificate357.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 21 12 (266702920451553 / 4000000000000)) (orderedInterval (-97359810365 / 1000000000000) (-97359810358 / 1000000000000), orderedInterval (-7564599632 / 1000000000000) (-7564599625 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (724150310133659 / 4000000000000)) (orderedInterval (-22550045459 / 1000000000000) (-22550044559 / 1000000000000), orderedInterval (54907618424 / 1000000000000) (54907619324 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 79 12 (988765338973243 / 4000000000000)) (orderedInterval (10558790645 / 1000000000000) (10558790698 / 1000000000000), orderedInterval (-49659344260 / 1000000000000) (-49659344207 / 1000000000000))) = true
  rfl'

theorem compactCertificate357_stateChecks8 :
    compactCertificate357.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 33 12 (418088376489441 / 4000000000000)) (orderedInterval (-77888380184 / 1000000000000) (-77888380099 / 1000000000000), orderedInterval (5281616490 / 1000000000000) (5281616575 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 135 12 (1699506038856961 / 4000000000000)) (orderedInterval (-38697371367 / 1000000000000) (-38697371130 / 1000000000000), orderedInterval (-890767629 / 1000000000000) (-890767392 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 90 12 (1135191271940399 / 4000000000000)) (orderedInterval (45663790222 / 1000000000000) (45663793579 / 1000000000000), orderedInterval (-12651490565 / 1000000000000) (-12651487208 / 1000000000000))) = true
  rfl'

theorem compactCertificate357_states : ∀ j,
    BesselStateValid (compactCertificate357.point j) (compactCertificate357.state j) :=
  compactCertificate357.statesValid_of_checks3 compactCertificate357_stateChecks0
    compactCertificate357_stateChecks1 compactCertificate357_stateChecks2
    compactCertificate357_stateChecks3 compactCertificate357_stateChecks4
    compactCertificate357_stateChecks5 compactCertificate357_stateChecks6
    compactCertificate357_stateChecks7 compactCertificate357_stateChecks8

theorem compactCertificate357_chunkChecks0_0 :
    compactCertificate357.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (457 / 2) 0 (IntervalRat.scale (457 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (2712530141 / 1000000000000) (2712530146 / 1000000000000), orderedInterval (-52719605155 / 1000000000000) (-52719605149 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (673248263190757 / 4000000000000) 0 (IntervalRat.scale (457 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-32108083801 / 1000000000000) (-32108078082 / 1000000000000), orderedInterval (52549703969 / 1000000000000) (52549709688 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (217714655557381 / 800000000000) 0 (IntervalRat.scale (457 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (18401755806 / 1000000000000) (18401756320 / 1000000000000), orderedInterval (-44762540980 / 1000000000000) (-44762540466 / 1000000000000)))) (orderedInterval (1855802939 / 1000000000000) (1855803041 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (196452164093999 / 4000000000000) 0 (IntervalRat.scale (457 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-41125919227 / 1000000000000) (-41125917707 / 1000000000000), orderedInterval (106585923411 / 1000000000000) (106585924931 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (527698146039203 / 4000000000000) 0 (IntervalRat.scale (457 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (47962413329 / 1000000000000) (47962413330 / 1000000000000), orderedInterval (50070032483 / 1000000000000) (50070032484 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1432803118404951 / 4000000000000) 0 (IntervalRat.scale (457 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (31512179666 / 1000000000000) (31512179667 / 1000000000000), orderedInterval (27960532446 / 1000000000000) (27960532447 / 1000000000000)))) (orderedInterval (-42811052 / 1000000000000) (-42811007 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1055396292078863 / 4000000000000) 0 (IntervalRat.scale (457 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (33129072261 / 1000000000000) (33129072262 / 1000000000000), orderedInterval (36204048871 / 1000000000000) (36204048872 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1808439535130699 / 4000000000000) 0 (IntervalRat.scale (457 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (18176539118 / 1000000000000) (18176539119 / 1000000000000), orderedInterval (32808580507 / 1000000000000) (32808580508 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1332088376489441 / 4000000000000) 0 (IntervalRat.scale (457 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (31312516761 / 1000000000000) (31312516762 / 1000000000000), orderedInterval (30468073728 / 1000000000000) (30468073729 / 1000000000000)))) (orderedInterval (196124553 / 1000000000000) (196124567 / 1000000000000))) = true
  rfl'

theorem compactCertificate357_chunkChecks0_1 :
    compactCertificate357.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2043766131434543 / 4000000000000) 0 (IntervalRat.scale (457 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (12200368656 / 1000000000000) (12200368717 / 1000000000000), orderedInterval (-33134820576 / 1000000000000) (-33134820515 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1179968926144247 / 4000000000000) 0 (IntervalRat.scale (457 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (20935174305 / 1000000000000) (20935174306 / 1000000000000), orderedInterval (41435111126 / 1000000000000) (41435111127 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2093875565919523 / 4000000000000) 0 (IntervalRat.scale (457 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (13320448391 / 1000000000000) (13320448487 / 1000000000000), orderedInterval (-32241932552 / 1000000000000) (-32241932455 / 1000000000000)))) (orderedInterval (1276846104 / 1000000000000) (1276846220 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1956370164076687 / 4000000000000) 0 (IntervalRat.scale (457 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-7548030531 / 1000000000000) (-7548030522 / 1000000000000), orderedInterval (35287490336 / 1000000000000) (35287490344 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1396158061729471 / 4000000000000) 0 (IntervalRat.scale (457 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-38210483999 / 1000000000000) (-38210483998 / 1000000000000), orderedInterval (-19020815845 / 1000000000000) (-19020815844 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1583094438117609 / 4000000000000) 0 (IntervalRat.scale (457 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (26385886424 / 1000000000000) (26385886425 / 1000000000000), orderedInterval (30171473909 / 1000000000000) (30171473910 / 1000000000000)))) (orderedInterval (-3610555432 / 1000000000000) (-3610555403 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1319819096610521 / 4000000000000) 0 (IntervalRat.scale (457 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-33645749497 / 1000000000000) (-33645749496 / 1000000000000), orderedInterval (-28186904240 / 1000000000000) (-28186904239 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1166100197952941 / 4000000000000) 0 (IntervalRat.scale (457 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-6608944596 / 1000000000000) (-6608944595 / 1000000000000), orderedInterval (-46249680987 / 1000000000000) (-46249680986 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (337981288305159 / 800000000000) 0 (IntervalRat.scale (457 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (29247822599 / 1000000000000) (29247854220 / 1000000000000), orderedInterval (-25557944176 / 1000000000000) (-25557912556 / 1000000000000)))) (orderedInterval (738537702 / 1000000000000) (738538534 / 1000000000000))) = true
  rfl'

theorem compactCertificate357_chunkChecks0_2 :
    compactCertificate357.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (934874030432773 / 4000000000000) 0 (IntervalRat.scale (457 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (46887311338 / 1000000000000) (46887328580 / 1000000000000), orderedInterval (-23022998083 / 1000000000000) (-23022980842 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (792503069044253 / 4000000000000) 0 (IntervalRat.scale (457 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-47396350152 / 1000000000000) (-47396350151 / 1000000000000), orderedInterval (-30973672826 / 1000000000000) (-30973672825 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (495911623510559 / 4000000000000) 0 (IntervalRat.scale (457 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-56194628215 / 1000000000000) (-56194555279 / 1000000000000), orderedInterval (44691220529 / 1000000000000) (44691293465 / 1000000000000)))) (orderedInterval (-6643729512 / 1000000000000) (-6643724322 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (266702920451553 / 4000000000000) 0 (IntervalRat.scale (457 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-97359810365 / 1000000000000) (-97359810358 / 1000000000000), orderedInterval (-7564599632 / 1000000000000) (-7564599625 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (724150310133659 / 4000000000000) 0 (IntervalRat.scale (457 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-22550045459 / 1000000000000) (-22550044559 / 1000000000000), orderedInterval (54907618424 / 1000000000000) (54907619324 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (988765338973243 / 4000000000000) 0 (IntervalRat.scale (457 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (10558790645 / 1000000000000) (10558790698 / 1000000000000), orderedInterval (-49659344260 / 1000000000000) (-49659344207 / 1000000000000)))) (orderedInterval (1500136237 / 1000000000000) (1500136289 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (418088376489441 / 4000000000000) 0 (IntervalRat.scale (457 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-77888380184 / 1000000000000) (-77888380099 / 1000000000000), orderedInterval (5281616490 / 1000000000000) (5281616575 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1699506038856961 / 4000000000000) 0 (IntervalRat.scale (457 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-38697371367 / 1000000000000) (-38697371130 / 1000000000000), orderedInterval (-890767629 / 1000000000000) (-890767392 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1135191271940399 / 4000000000000) 0 (IntervalRat.scale (457 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (45663790222 / 1000000000000) (45663793579 / 1000000000000), orderedInterval (-12651490565 / 1000000000000) (-12651487208 / 1000000000000)))) (orderedInterval (-5887240959 / 1000000000000) (-5887240245 / 1000000000000))) = true
  rfl'

theorem compactCertificate357_chunkChecks0 :
    compactCertificate357.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate357.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate357_chunkChecks0_0
    compactCertificate357_chunkChecks0_1 compactCertificate357_chunkChecks0_2

theorem compactCertificate357_chunkChecks1_0 :
    compactCertificate357.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (457 / 2) 1 (IntervalRat.scale (457 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (2712530141 / 1000000000000) (2712530146 / 1000000000000), orderedInterval (-52719605155 / 1000000000000) (-52719605149 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (673248263190757 / 4000000000000) 1 (IntervalRat.scale (457 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-32108083801 / 1000000000000) (-32108078082 / 1000000000000), orderedInterval (52549703969 / 1000000000000) (52549709688 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (217714655557381 / 800000000000) 1 (IntervalRat.scale (457 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (18401755806 / 1000000000000) (18401756320 / 1000000000000), orderedInterval (-44762540980 / 1000000000000) (-44762540466 / 1000000000000)))) (orderedInterval (-23663941437 / 1000000000000) (-23663941341 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (196452164093999 / 4000000000000) 1 (IntervalRat.scale (457 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-41125919227 / 1000000000000) (-41125917707 / 1000000000000), orderedInterval (106585923411 / 1000000000000) (106585924931 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (527698146039203 / 4000000000000) 1 (IntervalRat.scale (457 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (47962413329 / 1000000000000) (47962413330 / 1000000000000), orderedInterval (50070032483 / 1000000000000) (50070032484 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1432803118404951 / 4000000000000) 1 (IntervalRat.scale (457 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (31512179666 / 1000000000000) (31512179667 / 1000000000000), orderedInterval (27960532446 / 1000000000000) (27960532447 / 1000000000000)))) (orderedInterval (-2309030787 / 1000000000000) (-2309030751 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1055396292078863 / 4000000000000) 1 (IntervalRat.scale (457 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (33129072261 / 1000000000000) (33129072262 / 1000000000000), orderedInterval (36204048871 / 1000000000000) (36204048872 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1808439535130699 / 4000000000000) 1 (IntervalRat.scale (457 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (18176539118 / 1000000000000) (18176539119 / 1000000000000), orderedInterval (32808580507 / 1000000000000) (32808580508 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1332088376489441 / 4000000000000) 1 (IntervalRat.scale (457 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (31312516761 / 1000000000000) (31312516762 / 1000000000000), orderedInterval (30468073728 / 1000000000000) (30468073729 / 1000000000000)))) (orderedInterval (-929057993 / 1000000000000) (-929057970 / 1000000000000))) = true
  rfl'

theorem compactCertificate357_chunkChecks1_1 :
    compactCertificate357.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2043766131434543 / 4000000000000) 1 (IntervalRat.scale (457 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (12200368656 / 1000000000000) (12200368717 / 1000000000000), orderedInterval (-33134820576 / 1000000000000) (-33134820515 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1179968926144247 / 4000000000000) 1 (IntervalRat.scale (457 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (20935174305 / 1000000000000) (20935174306 / 1000000000000), orderedInterval (41435111126 / 1000000000000) (41435111127 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2093875565919523 / 4000000000000) 1 (IntervalRat.scale (457 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (13320448391 / 1000000000000) (13320448487 / 1000000000000), orderedInterval (-32241932552 / 1000000000000) (-32241932455 / 1000000000000)))) (orderedInterval (6628524799 / 1000000000000) (6628525043 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1956370164076687 / 4000000000000) 1 (IntervalRat.scale (457 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-7548030531 / 1000000000000) (-7548030522 / 1000000000000), orderedInterval (35287490336 / 1000000000000) (35287490344 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1396158061729471 / 4000000000000) 1 (IntervalRat.scale (457 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-38210483999 / 1000000000000) (-38210483998 / 1000000000000), orderedInterval (-19020815845 / 1000000000000) (-19020815844 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1583094438117609 / 4000000000000) 1 (IntervalRat.scale (457 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (26385886424 / 1000000000000) (26385886425 / 1000000000000), orderedInterval (30171473909 / 1000000000000) (30171473910 / 1000000000000)))) (orderedInterval (-4375529975 / 1000000000000) (-4375529930 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1319819096610521 / 4000000000000) 1 (IntervalRat.scale (457 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-33645749497 / 1000000000000) (-33645749496 / 1000000000000), orderedInterval (-28186904240 / 1000000000000) (-28186904239 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1166100197952941 / 4000000000000) 1 (IntervalRat.scale (457 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-6608944596 / 1000000000000) (-6608944595 / 1000000000000), orderedInterval (-46249680987 / 1000000000000) (-46249680986 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (337981288305159 / 800000000000) 1 (IntervalRat.scale (457 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (29247822599 / 1000000000000) (29247854220 / 1000000000000), orderedInterval (-25557944176 / 1000000000000) (-25557912556 / 1000000000000)))) (orderedInterval (1696821953 / 1000000000000) (1696823482 / 1000000000000))) = true
  rfl'

theorem compactCertificate357_chunkChecks1_2 :
    compactCertificate357.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (934874030432773 / 4000000000000) 1 (IntervalRat.scale (457 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (46887311338 / 1000000000000) (46887328580 / 1000000000000), orderedInterval (-23022998083 / 1000000000000) (-23022980842 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (792503069044253 / 4000000000000) 1 (IntervalRat.scale (457 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-47396350152 / 1000000000000) (-47396350151 / 1000000000000), orderedInterval (-30973672826 / 1000000000000) (-30973672825 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (495911623510559 / 4000000000000) 1 (IntervalRat.scale (457 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-56194628215 / 1000000000000) (-56194555279 / 1000000000000), orderedInterval (44691220529 / 1000000000000) (44691293465 / 1000000000000)))) (orderedInterval (6074750331 / 1000000000000) (6074754493 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (266702920451553 / 4000000000000) 1 (IntervalRat.scale (457 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-97359810365 / 1000000000000) (-97359810358 / 1000000000000), orderedInterval (-7564599632 / 1000000000000) (-7564599625 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (724150310133659 / 4000000000000) 1 (IntervalRat.scale (457 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-22550045459 / 1000000000000) (-22550044559 / 1000000000000), orderedInterval (54907618424 / 1000000000000) (54907619324 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (988765338973243 / 4000000000000) 1 (IntervalRat.scale (457 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (10558790645 / 1000000000000) (10558790698 / 1000000000000), orderedInterval (-49659344260 / 1000000000000) (-49659344207 / 1000000000000)))) (orderedInterval (3170975296 / 1000000000000) (3170975341 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (418088376489441 / 4000000000000) 1 (IntervalRat.scale (457 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-77888380184 / 1000000000000) (-77888380099 / 1000000000000), orderedInterval (5281616490 / 1000000000000) (5281616575 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1699506038856961 / 4000000000000) 1 (IntervalRat.scale (457 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-38697371367 / 1000000000000) (-38697371130 / 1000000000000), orderedInterval (-890767629 / 1000000000000) (-890767392 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1135191271940399 / 4000000000000) 1 (IntervalRat.scale (457 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (45663790222 / 1000000000000) (45663793579 / 1000000000000), orderedInterval (-12651490565 / 1000000000000) (-12651487208 / 1000000000000)))) (orderedInterval (3097602170 / 1000000000000) (3097603078 / 1000000000000))) = true
  rfl'

theorem compactCertificate357_chunkChecks1 :
    compactCertificate357.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate357.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate357_chunkChecks1_0
    compactCertificate357_chunkChecks1_1 compactCertificate357_chunkChecks1_2

theorem compactCertificate357_chunkChecks2_0 :
    compactCertificate357.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (457 / 2) 2 (IntervalRat.scale (457 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (2712530141 / 1000000000000) (2712530146 / 1000000000000), orderedInterval (-52719605155 / 1000000000000) (-52719605149 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (673248263190757 / 4000000000000) 2 (IntervalRat.scale (457 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-32108083801 / 1000000000000) (-32108078082 / 1000000000000), orderedInterval (52549703969 / 1000000000000) (52549709688 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (217714655557381 / 800000000000) 2 (IntervalRat.scale (457 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (18401755806 / 1000000000000) (18401756320 / 1000000000000), orderedInterval (-44762540980 / 1000000000000) (-44762540466 / 1000000000000)))) (orderedInterval (-2340985098 / 1000000000000) (-2340985003 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (196452164093999 / 4000000000000) 2 (IntervalRat.scale (457 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-41125919227 / 1000000000000) (-41125917707 / 1000000000000), orderedInterval (106585923411 / 1000000000000) (106585924931 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (527698146039203 / 4000000000000) 2 (IntervalRat.scale (457 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (47962413329 / 1000000000000) (47962413330 / 1000000000000), orderedInterval (50070032483 / 1000000000000) (50070032484 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1432803118404951 / 4000000000000) 2 (IntervalRat.scale (457 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (31512179666 / 1000000000000) (31512179667 / 1000000000000), orderedInterval (27960532446 / 1000000000000) (27960532447 / 1000000000000)))) (orderedInterval (4910864304 / 1000000000000) (4910864349 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1055396292078863 / 4000000000000) 2 (IntervalRat.scale (457 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (33129072261 / 1000000000000) (33129072262 / 1000000000000), orderedInterval (36204048871 / 1000000000000) (36204048872 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1808439535130699 / 4000000000000) 2 (IntervalRat.scale (457 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (18176539118 / 1000000000000) (18176539119 / 1000000000000), orderedInterval (32808580507 / 1000000000000) (32808580508 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1332088376489441 / 4000000000000) 2 (IntervalRat.scale (457 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (31312516761 / 1000000000000) (31312516762 / 1000000000000), orderedInterval (30468073728 / 1000000000000) (30468073729 / 1000000000000)))) (orderedInterval (591445826 / 1000000000000) (591445866 / 1000000000000))) = true
  rfl'

theorem compactCertificate357_chunkChecks2_1 :
    compactCertificate357.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2043766131434543 / 4000000000000) 2 (IntervalRat.scale (457 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (12200368656 / 1000000000000) (12200368717 / 1000000000000), orderedInterval (-33134820576 / 1000000000000) (-33134820515 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1179968926144247 / 4000000000000) 2 (IntervalRat.scale (457 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (20935174305 / 1000000000000) (20935174306 / 1000000000000), orderedInterval (41435111126 / 1000000000000) (41435111127 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2093875565919523 / 4000000000000) 2 (IntervalRat.scale (457 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (13320448391 / 1000000000000) (13320448487 / 1000000000000), orderedInterval (-32241932552 / 1000000000000) (-32241932455 / 1000000000000)))) (orderedInterval (-1712789170 / 1000000000000) (-1712788641 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1956370164076687 / 4000000000000) 2 (IntervalRat.scale (457 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-7548030531 / 1000000000000) (-7548030522 / 1000000000000), orderedInterval (35287490336 / 1000000000000) (35287490344 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1396158061729471 / 4000000000000) 2 (IntervalRat.scale (457 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-38210483999 / 1000000000000) (-38210483998 / 1000000000000), orderedInterval (-19020815845 / 1000000000000) (-19020815844 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1583094438117609 / 4000000000000) 2 (IntervalRat.scale (457 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (26385886424 / 1000000000000) (26385886425 / 1000000000000), orderedInterval (30171473909 / 1000000000000) (30171473910 / 1000000000000)))) (orderedInterval (8226446895 / 1000000000000) (8226446969 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1319819096610521 / 4000000000000) 2 (IntervalRat.scale (457 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-33645749497 / 1000000000000) (-33645749496 / 1000000000000), orderedInterval (-28186904240 / 1000000000000) (-28186904239 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1166100197952941 / 4000000000000) 2 (IntervalRat.scale (457 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-6608944596 / 1000000000000) (-6608944595 / 1000000000000), orderedInterval (-46249680987 / 1000000000000) (-46249680986 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (337981288305159 / 800000000000) 2 (IntervalRat.scale (457 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (29247822599 / 1000000000000) (29247854220 / 1000000000000), orderedInterval (-25557944176 / 1000000000000) (-25557912556 / 1000000000000)))) (orderedInterval (-2372864667 / 1000000000000) (-2372861845 / 1000000000000))) = true
  rfl'

theorem compactCertificate357_chunkChecks2_2 :
    compactCertificate357.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (934874030432773 / 4000000000000) 2 (IntervalRat.scale (457 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (46887311338 / 1000000000000) (46887328580 / 1000000000000), orderedInterval (-23022998083 / 1000000000000) (-23022980842 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (792503069044253 / 4000000000000) 2 (IntervalRat.scale (457 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-47396350152 / 1000000000000) (-47396350151 / 1000000000000), orderedInterval (-30973672826 / 1000000000000) (-30973672825 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (495911623510559 / 4000000000000) 2 (IntervalRat.scale (457 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-56194628215 / 1000000000000) (-56194555279 / 1000000000000), orderedInterval (44691220529 / 1000000000000) (44691293465 / 1000000000000)))) (orderedInterval (6338404243 / 1000000000000) (6338407896 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (266702920451553 / 4000000000000) 2 (IntervalRat.scale (457 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-97359810365 / 1000000000000) (-97359810358 / 1000000000000), orderedInterval (-7564599632 / 1000000000000) (-7564599625 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (724150310133659 / 4000000000000) 2 (IntervalRat.scale (457 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-22550045459 / 1000000000000) (-22550044559 / 1000000000000), orderedInterval (54907618424 / 1000000000000) (54907619324 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (988765338973243 / 4000000000000) 2 (IntervalRat.scale (457 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (10558790645 / 1000000000000) (10558790698 / 1000000000000), orderedInterval (-49659344260 / 1000000000000) (-49659344207 / 1000000000000)))) (orderedInterval (458932539 / 1000000000000) (458932582 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (418088376489441 / 4000000000000) 2 (IntervalRat.scale (457 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-77888380184 / 1000000000000) (-77888380099 / 1000000000000), orderedInterval (5281616490 / 1000000000000) (5281616575 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1699506038856961 / 4000000000000) 2 (IntervalRat.scale (457 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-38697371367 / 1000000000000) (-38697371130 / 1000000000000), orderedInterval (-890767629 / 1000000000000) (-890767392 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1135191271940399 / 4000000000000) 2 (IntervalRat.scale (457 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (45663790222 / 1000000000000) (45663793579 / 1000000000000), orderedInterval (-12651490565 / 1000000000000) (-12651487208 / 1000000000000)))) (orderedInterval (2410034604 / 1000000000000) (2410035778 / 1000000000000))) = true
  rfl'

theorem compactCertificate357_chunkChecks2 :
    compactCertificate357.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate357.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate357_chunkChecks2_0
    compactCertificate357_chunkChecks2_1 compactCertificate357_chunkChecks2_2

theorem compactCertificate357_chunkChecks3_0 :
    compactCertificate357.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (457 / 2) 3 (IntervalRat.scale (457 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (2712530141 / 1000000000000) (2712530146 / 1000000000000), orderedInterval (-52719605155 / 1000000000000) (-52719605149 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (673248263190757 / 4000000000000) 3 (IntervalRat.scale (457 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-32108083801 / 1000000000000) (-32108078082 / 1000000000000), orderedInterval (52549703969 / 1000000000000) (52549709688 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (217714655557381 / 800000000000) 3 (IntervalRat.scale (457 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (18401755806 / 1000000000000) (18401756320 / 1000000000000), orderedInterval (-44762540980 / 1000000000000) (-44762540466 / 1000000000000)))) (orderedInterval (25147896502 / 1000000000000) (25147896602 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (196452164093999 / 4000000000000) 3 (IntervalRat.scale (457 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-41125919227 / 1000000000000) (-41125917707 / 1000000000000), orderedInterval (106585923411 / 1000000000000) (106585924931 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (527698146039203 / 4000000000000) 3 (IntervalRat.scale (457 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (47962413329 / 1000000000000) (47962413330 / 1000000000000), orderedInterval (50070032483 / 1000000000000) (50070032484 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1432803118404951 / 4000000000000) 3 (IntervalRat.scale (457 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (31512179666 / 1000000000000) (31512179667 / 1000000000000), orderedInterval (27960532446 / 1000000000000) (27960532447 / 1000000000000)))) (orderedInterval (7295368087 / 1000000000000) (7295368152 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1055396292078863 / 4000000000000) 3 (IntervalRat.scale (457 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (33129072261 / 1000000000000) (33129072262 / 1000000000000), orderedInterval (36204048871 / 1000000000000) (36204048872 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1808439535130699 / 4000000000000) 3 (IntervalRat.scale (457 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (18176539118 / 1000000000000) (18176539119 / 1000000000000), orderedInterval (32808580507 / 1000000000000) (32808580508 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1332088376489441 / 4000000000000) 3 (IntervalRat.scale (457 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (31312516761 / 1000000000000) (31312516762 / 1000000000000), orderedInterval (30468073728 / 1000000000000) (30468073729 / 1000000000000)))) (orderedInterval (5556330701 / 1000000000000) (5556330774 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate357_chunkChecks3_1 :
    compactCertificate357.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2043766131434543 / 4000000000000) 3 (IntervalRat.scale (457 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (12200368656 / 1000000000000) (12200368717 / 1000000000000), orderedInterval (-33134820576 / 1000000000000) (-33134820515 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1179968926144247 / 4000000000000) 3 (IntervalRat.scale (457 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (20935174305 / 1000000000000) (20935174306 / 1000000000000), orderedInterval (41435111126 / 1000000000000) (41435111127 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2093875565919523 / 4000000000000) 3 (IntervalRat.scale (457 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (13320448391 / 1000000000000) (13320448487 / 1000000000000), orderedInterval (-32241932552 / 1000000000000) (-32241932455 / 1000000000000)))) (orderedInterval (-17317845539 / 1000000000000) (-17317844370 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1956370164076687 / 4000000000000) 3 (IntervalRat.scale (457 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-7548030531 / 1000000000000) (-7548030522 / 1000000000000), orderedInterval (35287490336 / 1000000000000) (35287490344 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1396158061729471 / 4000000000000) 3 (IntervalRat.scale (457 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-38210483999 / 1000000000000) (-38210483998 / 1000000000000), orderedInterval (-19020815845 / 1000000000000) (-19020815844 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1583094438117609 / 4000000000000) 3 (IntervalRat.scale (457 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (26385886424 / 1000000000000) (26385886425 / 1000000000000), orderedInterval (30171473909 / 1000000000000) (30171473910 / 1000000000000)))) (orderedInterval (13415347980 / 1000000000000) (13415348106 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1319819096610521 / 4000000000000) 3 (IntervalRat.scale (457 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-33645749497 / 1000000000000) (-33645749496 / 1000000000000), orderedInterval (-28186904240 / 1000000000000) (-28186904239 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1166100197952941 / 4000000000000) 3 (IntervalRat.scale (457 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-6608944596 / 1000000000000) (-6608944595 / 1000000000000), orderedInterval (-46249680987 / 1000000000000) (-46249680986 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (337981288305159 / 800000000000) 3 (IntervalRat.scale (457 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (29247822599 / 1000000000000) (29247854220 / 1000000000000), orderedInterval (-25557944176 / 1000000000000) (-25557912556 / 1000000000000)))) (orderedInterval (-369899777 / 1000000000000) (-369894575 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate357_chunkChecks3_2 :
    compactCertificate357.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (934874030432773 / 4000000000000) 3 (IntervalRat.scale (457 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (46887311338 / 1000000000000) (46887328580 / 1000000000000), orderedInterval (-23022998083 / 1000000000000) (-23022980842 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (792503069044253 / 4000000000000) 3 (IntervalRat.scale (457 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-47396350152 / 1000000000000) (-47396350151 / 1000000000000), orderedInterval (-30973672826 / 1000000000000) (-30973672825 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (495911623510559 / 4000000000000) 3 (IntervalRat.scale (457 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-56194628215 / 1000000000000) (-56194555279 / 1000000000000), orderedInterval (44691220529 / 1000000000000) (44691293465 / 1000000000000)))) (orderedInterval (-5342043440 / 1000000000000) (-5342040046 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (266702920451553 / 4000000000000) 3 (IntervalRat.scale (457 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-97359810365 / 1000000000000) (-97359810358 / 1000000000000), orderedInterval (-7564599632 / 1000000000000) (-7564599625 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (724150310133659 / 4000000000000) 3 (IntervalRat.scale (457 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-22550045459 / 1000000000000) (-22550044559 / 1000000000000), orderedInterval (54907618424 / 1000000000000) (54907619324 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (988765338973243 / 4000000000000) 3 (IntervalRat.scale (457 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (10558790645 / 1000000000000) (10558790698 / 1000000000000), orderedInterval (-49659344260 / 1000000000000) (-49659344207 / 1000000000000)))) (orderedInterval (-4204169798 / 1000000000000) (-4204169757 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (418088376489441 / 4000000000000) 3 (IntervalRat.scale (457 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-77888380184 / 1000000000000) (-77888380099 / 1000000000000), orderedInterval (5281616490 / 1000000000000) (5281616575 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1699506038856961 / 4000000000000) 3 (IntervalRat.scale (457 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-38697371367 / 1000000000000) (-38697371130 / 1000000000000), orderedInterval (-890767629 / 1000000000000) (-890767392 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1135191271940399 / 4000000000000) 3 (IntervalRat.scale (457 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (45663790222 / 1000000000000) (45663793579 / 1000000000000), orderedInterval (-12651490565 / 1000000000000) (-12651487208 / 1000000000000)))) (orderedInterval (-5027520392 / 1000000000000) (-5027518854 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate357_chunkChecks3 :
    compactCertificate357.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate357.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate357_chunkChecks3_0
    compactCertificate357_chunkChecks3_1 compactCertificate357_chunkChecks3_2

theorem compactCertificate357_chunkChecks4_0 :
    compactCertificate357.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (457 / 2) 4 (IntervalRat.scale (457 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (2712530141 / 1000000000000) (2712530146 / 1000000000000), orderedInterval (-52719605155 / 1000000000000) (-52719605149 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (673248263190757 / 4000000000000) 4 (IntervalRat.scale (457 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-32108083801 / 1000000000000) (-32108078082 / 1000000000000), orderedInterval (52549703969 / 1000000000000) (52549709688 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (217714655557381 / 800000000000) 4 (IntervalRat.scale (457 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (18401755806 / 1000000000000) (18401756320 / 1000000000000), orderedInterval (-44762540980 / 1000000000000) (-44762540466 / 1000000000000)))) (orderedInterval (2939640233 / 1000000000000) (2939640341 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (196452164093999 / 4000000000000) 4 (IntervalRat.scale (457 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-41125919227 / 1000000000000) (-41125917707 / 1000000000000), orderedInterval (106585923411 / 1000000000000) (106585924931 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (527698146039203 / 4000000000000) 4 (IntervalRat.scale (457 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (47962413329 / 1000000000000) (47962413330 / 1000000000000), orderedInterval (50070032483 / 1000000000000) (50070032484 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1432803118404951 / 4000000000000) 4 (IntervalRat.scale (457 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (31512179666 / 1000000000000) (31512179667 / 1000000000000), orderedInterval (27960532446 / 1000000000000) (27960532447 / 1000000000000)))) (orderedInterval (-13396619247 / 1000000000000) (-13396619147 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1055396292078863 / 4000000000000) 4 (IntervalRat.scale (457 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (33129072261 / 1000000000000) (33129072262 / 1000000000000), orderedInterval (36204048871 / 1000000000000) (36204048872 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1808439535130699 / 4000000000000) 4 (IntervalRat.scale (457 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (18176539118 / 1000000000000) (18176539119 / 1000000000000), orderedInterval (32808580507 / 1000000000000) (32808580508 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1332088376489441 / 4000000000000) 4 (IntervalRat.scale (457 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (31312516761 / 1000000000000) (31312516762 / 1000000000000), orderedInterval (30468073728 / 1000000000000) (30468073729 / 1000000000000)))) (orderedInterval (-5226655904 / 1000000000000) (-5226655769 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate357_chunkChecks4_1 :
    compactCertificate357.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2043766131434543 / 4000000000000) 4 (IntervalRat.scale (457 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (12200368656 / 1000000000000) (12200368717 / 1000000000000), orderedInterval (-33134820576 / 1000000000000) (-33134820515 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1179968926144247 / 4000000000000) 4 (IntervalRat.scale (457 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (20935174305 / 1000000000000) (20935174306 / 1000000000000), orderedInterval (41435111126 / 1000000000000) (41435111127 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2093875565919523 / 4000000000000) 4 (IntervalRat.scale (457 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (13320448391 / 1000000000000) (13320448487 / 1000000000000), orderedInterval (-32241932552 / 1000000000000) (-32241932455 / 1000000000000)))) (orderedInterval (2419541881 / 1000000000000) (2419544489 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1956370164076687 / 4000000000000) 4 (IntervalRat.scale (457 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-7548030531 / 1000000000000) (-7548030522 / 1000000000000), orderedInterval (35287490336 / 1000000000000) (35287490344 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1396158061729471 / 4000000000000) 4 (IntervalRat.scale (457 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-38210483999 / 1000000000000) (-38210483998 / 1000000000000), orderedInterval (-19020815845 / 1000000000000) (-19020815844 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1583094438117609 / 4000000000000) 4 (IntervalRat.scale (457 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (26385886424 / 1000000000000) (26385886425 / 1000000000000), orderedInterval (30171473909 / 1000000000000) (30171473910 / 1000000000000)))) (orderedInterval (-18131132630 / 1000000000000) (-18131132410 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1319819096610521 / 4000000000000) 4 (IntervalRat.scale (457 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-33645749497 / 1000000000000) (-33645749496 / 1000000000000), orderedInterval (-28186904240 / 1000000000000) (-28186904239 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1166100197952941 / 4000000000000) 4 (IntervalRat.scale (457 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-6608944596 / 1000000000000) (-6608944595 / 1000000000000), orderedInterval (-46249680987 / 1000000000000) (-46249680986 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (337981288305159 / 800000000000) 4 (IntervalRat.scale (457 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (29247822599 / 1000000000000) (29247854220 / 1000000000000), orderedInterval (-25557944176 / 1000000000000) (-25557912556 / 1000000000000)))) (orderedInterval (8067153306 / 1000000000000) (8067162927 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate357_chunkChecks4_2 :
    compactCertificate357.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (934874030432773 / 4000000000000) 4 (IntervalRat.scale (457 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (46887311338 / 1000000000000) (46887328580 / 1000000000000), orderedInterval (-23022998083 / 1000000000000) (-23022980842 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (792503069044253 / 4000000000000) 4 (IntervalRat.scale (457 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-47396350152 / 1000000000000) (-47396350151 / 1000000000000), orderedInterval (-30973672826 / 1000000000000) (-30973672825 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (495911623510559 / 4000000000000) 4 (IntervalRat.scale (457 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-56194628215 / 1000000000000) (-56194555279 / 1000000000000), orderedInterval (44691220529 / 1000000000000) (44691293465 / 1000000000000)))) (orderedInterval (-6800995944 / 1000000000000) (-6800992643 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (266702920451553 / 4000000000000) 4 (IntervalRat.scale (457 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-97359810365 / 1000000000000) (-97359810358 / 1000000000000), orderedInterval (-7564599632 / 1000000000000) (-7564599625 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (724150310133659 / 4000000000000) 4 (IntervalRat.scale (457 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-22550045459 / 1000000000000) (-22550044559 / 1000000000000), orderedInterval (54907618424 / 1000000000000) (54907619324 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (988765338973243 / 4000000000000) 4 (IntervalRat.scale (457 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (10558790645 / 1000000000000) (10558790698 / 1000000000000), orderedInterval (-49659344260 / 1000000000000) (-49659344207 / 1000000000000)))) (orderedInterval (-856862934 / 1000000000000) (-856862893 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (418088376489441 / 4000000000000) 4 (IntervalRat.scale (457 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-77888380184 / 1000000000000) (-77888380099 / 1000000000000), orderedInterval (5281616490 / 1000000000000) (5281616575 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1699506038856961 / 4000000000000) 4 (IntervalRat.scale (457 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-38697371367 / 1000000000000) (-38697371130 / 1000000000000), orderedInterval (-890767629 / 1000000000000) (-890767392 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1135191271940399 / 4000000000000) 4 (IntervalRat.scale (457 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (45663790222 / 1000000000000) (45663793579 / 1000000000000), orderedInterval (-12651490565 / 1000000000000) (-12651487208 / 1000000000000)))) (orderedInterval (17291184401 / 1000000000000) (17291186468 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate357_chunkChecks4 :
    compactCertificate357.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate357.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate357_chunkChecks4_0
    compactCertificate357_chunkChecks4_1 compactCertificate357_chunkChecks4_2

theorem compactCertificate357_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate357.chunkCheck r b = true :=
  compactCertificate357.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate357_chunkChecks0
    · exact compactCertificate357_chunkChecks1
    · exact compactCertificate357_chunkChecks2
    · exact compactCertificate357_chunkChecks3
    · exact compactCertificate357_chunkChecks4)

theorem compactCertificate357_coefficient0 :
    compactCertificate357.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate357_coefficient1 :
    compactCertificate357.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate357_coefficient2 :
    compactCertificate357.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate357_coefficient3 :
    compactCertificate357.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate357_coefficient4 :
    compactCertificate357.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate357_coefficients : ∀ r : Fin 5,
    compactCertificate357.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate357_coefficient0
  · exact compactCertificate357_coefficient1
  · exact compactCertificate357_coefficient2
  · exact compactCertificate357_coefficient3
  · exact compactCertificate357_coefficient4

theorem compactCertificate357_lower : (1 : ℚ) ≤ compactCertificate357.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate357, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate357_proves {t : ℝ} (ht : t ∈ compactCertificate357.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate357.proves compactCertificate357_states compactCertificate357_chunks
    compactCertificate357_coefficients compactCertificate357_lower ht

end Erdos232
