/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate354 : CompactCertificate where
  left := 225
  right := 226
  center := 451 / 2
  grid := fun i =>
    match i.val with
    | 0 => 72
    | 1 => 53
    | 2 => 86
    | 3 => 15
    | 4 => 41
    | 5 => 113
    | 6 => 83
    | 7 => 142
    | 8 => 105
    | 9 => 161
    | 10 => 93
    | 11 => 165
    | 12 => 154
    | 13 => 110
    | 14 => 124
    | 15 => 104
    | 16 => 92
    | 17 => 133
    | 18 => 73
    | 19 => 62
    | 20 => 39
    | 21 => 21
    | 22 => 57
    | 23 => 78
    | 24 => 33
    | 25 => 134
    | _ => 89
  point := fun i =>
    match i.val with
    | 0 => 451 / 2
    | 1 => 664409117503351 / 4000000000000
    | 2 => 214856257453783 / 800000000000
    | 3 => 193872923427557 / 4000000000000
    | 4 => 520769942808929 / 4000000000000
    | 5 => 1413991698907293 / 4000000000000
    | 6 => 1041539885618309 / 4000000000000
    | 7 => 1784696346485657 / 4000000000000
    | 8 => 1314599251196363 / 4000000000000
    | 9 => 2016933315704549 / 4000000000000
    | 10 => 1164476992759421 / 4000000000000
    | 11 => 2066384858270689 / 4000000000000
    | 12 => 1930684778990341 / 4000000000000
    | 13 => 1377827758949653 / 4000000000000
    | 14 => 1562309828426787 / 4000000000000
    | 15 => 1302491055954803 / 4000000000000
    | 16 => 1150790348526863 / 4000000000000
    | 17 => 333543897211437 / 800000000000
    | 18 => 922599973140439 / 4000000000000
    | 19 => 782098214746079 / 4000000000000
    | 20 => 489400748803637 / 4000000000000
    | 21 => 263201350379979 / 4000000000000
    | 22 => 714642866236937 / 4000000000000
    | 23 => 975783737148649 / 4000000000000
    | 24 => 412599251196363 / 4000000000000
    | 25 => 1677193049287723 / 4000000000000
    | _ => 1120287228982757 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (4784681529 / 1000000000000) (4784681531 / 1000000000000), orderedInterval (52906885264 / 1000000000000) (52906885266 / 1000000000000))
    | 1 => (orderedInterval (-23107666808 / 1000000000000) (-23107666807 / 1000000000000), orderedInterval (-57365149782 / 1000000000000) (-57365149781 / 1000000000000))
    | 2 => (orderedInterval (-35653995114 / 1000000000000) (-35653947180 / 1000000000000), orderedInterval (33220485172 / 1000000000000) (33220533106 / 1000000000000))
    | 3 => (orderedInterval (-97319544060 / 1000000000000) (-97319525144 / 1000000000000), orderedInterval (61529728685 / 1000000000000) (61529747602 / 1000000000000))
    | 4 => (orderedInterval (-57680605248 / 1000000000000) (-57680564113 / 1000000000000), orderedInterval (39753406979 / 1000000000000) (39753448115 / 1000000000000))
    | 5 => (orderedInterval (27886591881 / 1000000000000) (27886603990 / 1000000000000), orderedInterval (-32027776431 / 1000000000000) (-32027764322 / 1000000000000))
    | 6 => (orderedInterval (-20058220061 / 1000000000000) (-20058220060 / 1000000000000), orderedInterval (-45156487028 / 1000000000000) (-45156487027 / 1000000000000))
    | 7 => (orderedInterval (28454374601 / 1000000000000) (28454374602 / 1000000000000), orderedInterval (24811423947 / 1000000000000) (24811423948 / 1000000000000))
    | 8 => (orderedInterval (18443283227 / 1000000000000) (18443283835 / 1000000000000), orderedInterval (-39989579320 / 1000000000000) (-39989578712 / 1000000000000))
    | 9 => (orderedInterval (24937040311 / 1000000000000) (24937050709 / 1000000000000), orderedInterval (-25336661359 / 1000000000000) (-25336650961 / 1000000000000))
    | 10 => (orderedInterval (12198057002 / 1000000000000) (12198057085 / 1000000000000), orderedInterval (-45165284109 / 1000000000000) (-45165284026 / 1000000000000))
    | 11 => (orderedInterval (29181946617 / 1000000000000) (29182011208 / 1000000000000), orderedInterval (-19541020002 / 1000000000000) (-19540955411 / 1000000000000))
    | 12 => (orderedInterval (-12416792901 / 1000000000000) (-12416792831 / 1000000000000), orderedInterval (34141663275 / 1000000000000) (34141663345 / 1000000000000))
    | 13 => (orderedInterval (-14061528569 / 1000000000000) (-14061528419 / 1000000000000), orderedInterval (40646250755 / 1000000000000) (40646250906 / 1000000000000))
    | 14 => (orderedInterval (39269932810 / 1000000000000) (39269936957 / 1000000000000), orderedInterval (-9421293533 / 1000000000000) (-9421289386 / 1000000000000))
    | 15 => (orderedInterval (-13819022565 / 1000000000000) (-13819022426 / 1000000000000), orderedInterval (42022650362 / 1000000000000) (42022650501 / 1000000000000))
    | 16 => (orderedInterval (-24345318600 / 1000000000000) (-24345315763 / 1000000000000), orderedInterval (40292972980 / 1000000000000) (40292975817 / 1000000000000))
    | 17 => (orderedInterval (4555747872 / 1000000000000) (4555747876 / 1000000000000), orderedInterval (-38814858420 / 1000000000000) (-38814858416 / 1000000000000))
    | 18 => (orderedInterval (-45387655231 / 1000000000000) (-45387621649 / 1000000000000), orderedInterval (26557224742 / 1000000000000) (26557258324 / 1000000000000))
    | 19 => (orderedInterval (57014745767 / 1000000000000) (57014745803 / 1000000000000), orderedInterval (2149053153 / 1000000000000) (2149053190 / 1000000000000))
    | 20 => (orderedInterval (-41467576931 / 1000000000000) (-41467576930 / 1000000000000), orderedInterval (-58853538063 / 1000000000000) (-58853538062 / 1000000000000))
    | 21 => (orderedInterval (-56378885026 / 1000000000000) (-56378885025 / 1000000000000), orderedInterval (-80172732330 / 1000000000000) (-80172732329 / 1000000000000))
    | 22 => (orderedInterval (-21843629592 / 1000000000000) (-21843629591 / 1000000000000), orderedInterval (-55492042493 / 1000000000000) (-55492042492 / 1000000000000))
    | 23 => (orderedInterval (-15749555776 / 1000000000000) (-15749555546 / 1000000000000), orderedInterval (48628902041 / 1000000000000) (48628902270 / 1000000000000))
    | 24 => (orderedInterval (-20305759433 / 1000000000000) (-20305759432 / 1000000000000), orderedInterval (-75793184666 / 1000000000000) (-75793184665 / 1000000000000))
    | 25 => (orderedInterval (-30280184837 / 1000000000000) (-30280140162 / 1000000000000), orderedInterval (24559739845 / 1000000000000) (24559784520 / 1000000000000))
    | _ => (orderedInterval (-45319126224 / 1000000000000) (-45319126223 / 1000000000000), orderedInterval (-14725612253 / 1000000000000) (-14725612252 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-411055452 / 1000000000000) (-411052622 / 1000000000000)
      | 1 => orderedInterval (-3032620440 / 1000000000000) (-3032617844 / 1000000000000)
      | 2 => orderedInterval (-431908998 / 1000000000000) (-431908970 / 1000000000000)
      | 3 => orderedInterval (621148432 / 1000000000000) (621159557 / 1000000000000)
      | 4 => orderedInterval (-1304265527 / 1000000000000) (-1304265463 / 1000000000000)
      | 5 => orderedInterval (1350269139 / 1000000000000) (1350269325 / 1000000000000)
      | 6 => orderedInterval (2680117325 / 1000000000000) (2680122754 / 1000000000000)
      | 7 => orderedInterval (2743634245 / 1000000000000) (2743634290 / 1000000000000)
      | _ => orderedInterval (10845517667 / 1000000000000) (10845521367 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (22898456260 / 1000000000000) (22898459629 / 1000000000000)
      | 1 => orderedInterval (4263742130 / 1000000000000) (4263744422 / 1000000000000)
      | 2 => orderedInterval (-2922747847 / 1000000000000) (-2922747803 / 1000000000000)
      | 3 => orderedInterval (-617140417 / 1000000000000) (-617115057 / 1000000000000)
      | 4 => orderedInterval (4634522766 / 1000000000000) (4634522871 / 1000000000000)
      | 5 => orderedInterval (-4078582418 / 1000000000000) (-4078582177 / 1000000000000)
      | 6 => orderedInterval (-5488315625 / 1000000000000) (-5488310078 / 1000000000000)
      | 7 => orderedInterval (-2602303451 / 1000000000000) (-2602303407 / 1000000000000)
      | _ => orderedInterval (-494813240 / 1000000000000) (-494806389 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (1086562748 / 1000000000000) (1086566775 / 1000000000000)
      | 1 => orderedInterval (5506041182 / 1000000000000) (5506043861 / 1000000000000)
      | 2 => orderedInterval (2502031433 / 1000000000000) (2502031505 / 1000000000000)
      | 3 => orderedInterval (-1120055546 / 1000000000000) (-1119997600 / 1000000000000)
      | 4 => orderedInterval (2651262586 / 1000000000000) (2651262761 / 1000000000000)
      | 5 => orderedInterval (-2315660190 / 1000000000000) (-2315659874 / 1000000000000)
      | 6 => orderedInterval (-4744529000 / 1000000000000) (-4744523306 / 1000000000000)
      | 7 => orderedInterval (-1800749547 / 1000000000000) (-1800749501 / 1000000000000)
      | _ => orderedInterval (-21610875250 / 1000000000000) (-21610862516 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-24054538789 / 1000000000000) (-24054533994 / 1000000000000)
      | 1 => orderedInterval (-9068140072 / 1000000000000) (-9068136388 / 1000000000000)
      | 2 => orderedInterval (8908587877 / 1000000000000) (8908587995 / 1000000000000)
      | 3 => orderedInterval (-9730567449 / 1000000000000) (-9730435260 / 1000000000000)
      | 4 => orderedInterval (-7914589621 / 1000000000000) (-7914589325 / 1000000000000)
      | 5 => orderedInterval (9618921302 / 1000000000000) (9618921718 / 1000000000000)
      | 6 => orderedInterval (4950183436 / 1000000000000) (4950189257 / 1000000000000)
      | 7 => orderedInterval (4063330853 / 1000000000000) (4063330901 / 1000000000000)
      | _ => orderedInterval (7698627080 / 1000000000000) (7698650715 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-2163257480 / 1000000000000) (-2163251750 / 1000000000000)
      | 1 => orderedInterval (-12123118350 / 1000000000000) (-12123112853 / 1000000000000)
      | 2 => orderedInterval (-11518781777 / 1000000000000) (-11518781577 / 1000000000000)
      | 3 => orderedInterval (6082391740 / 1000000000000) (6082693942 / 1000000000000)
      | 4 => orderedInterval (-4252555086 / 1000000000000) (-4252554579 / 1000000000000)
      | 5 => orderedInterval (4275184480 / 1000000000000) (4275185035 / 1000000000000)
      | 6 => orderedInterval (5958173571 / 1000000000000) (5958179548 / 1000000000000)
      | 7 => orderedInterval (1819865406 / 1000000000000) (1819865457 / 1000000000000)
      | _ => orderedInterval (49623670934 / 1000000000000) (49623714934 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (13060836391 / 1000000000000) (13060862394 / 1000000000000)
    | 1 => orderedInterval (15592818158 / 1000000000000) (15592862011 / 1000000000000)
    | 2 => orderedInterval (-19845971584 / 1000000000000) (-19845887895 / 1000000000000)
    | 3 => orderedInterval (-15528185383 / 1000000000000) (-15528014381 / 1000000000000)
    | _ => orderedInterval (37701573438 / 1000000000000) (37701938157 / 1000000000000)

theorem compactCertificate354_stateChecks0 :
    compactCertificate354.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 72 12 (451 / 2)) (orderedInterval (4784681529 / 1000000000000) (4784681531 / 1000000000000), orderedInterval (52906885264 / 1000000000000) (52906885266 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 53 12 (664409117503351 / 4000000000000)) (orderedInterval (-23107666808 / 1000000000000) (-23107666807 / 1000000000000), orderedInterval (-57365149782 / 1000000000000) (-57365149781 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 86 12 (214856257453783 / 800000000000)) (orderedInterval (-35653995114 / 1000000000000) (-35653947180 / 1000000000000), orderedInterval (33220485172 / 1000000000000) (33220533106 / 1000000000000))) = true
  rfl'

theorem compactCertificate354_stateChecks1 :
    compactCertificate354.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 15 12 (193872923427557 / 4000000000000)) (orderedInterval (-97319544060 / 1000000000000) (-97319525144 / 1000000000000), orderedInterval (61529728685 / 1000000000000) (61529747602 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 41 12 (520769942808929 / 4000000000000)) (orderedInterval (-57680605248 / 1000000000000) (-57680564113 / 1000000000000), orderedInterval (39753406979 / 1000000000000) (39753448115 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 113 12 (1413991698907293 / 4000000000000)) (orderedInterval (27886591881 / 1000000000000) (27886603990 / 1000000000000), orderedInterval (-32027776431 / 1000000000000) (-32027764322 / 1000000000000))) = true
  rfl'

theorem compactCertificate354_stateChecks2 :
    compactCertificate354.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 83 12 (1041539885618309 / 4000000000000)) (orderedInterval (-20058220061 / 1000000000000) (-20058220060 / 1000000000000), orderedInterval (-45156487028 / 1000000000000) (-45156487027 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 142 12 (1784696346485657 / 4000000000000)) (orderedInterval (28454374601 / 1000000000000) (28454374602 / 1000000000000), orderedInterval (24811423947 / 1000000000000) (24811423948 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 105 12 (1314599251196363 / 4000000000000)) (orderedInterval (18443283227 / 1000000000000) (18443283835 / 1000000000000), orderedInterval (-39989579320 / 1000000000000) (-39989578712 / 1000000000000))) = true
  rfl'

theorem compactCertificate354_stateChecks3 :
    compactCertificate354.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 161 12 (2016933315704549 / 4000000000000)) (orderedInterval (24937040311 / 1000000000000) (24937050709 / 1000000000000), orderedInterval (-25336661359 / 1000000000000) (-25336650961 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 93 12 (1164476992759421 / 4000000000000)) (orderedInterval (12198057002 / 1000000000000) (12198057085 / 1000000000000), orderedInterval (-45165284109 / 1000000000000) (-45165284026 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 165 12 (2066384858270689 / 4000000000000)) (orderedInterval (29181946617 / 1000000000000) (29182011208 / 1000000000000), orderedInterval (-19541020002 / 1000000000000) (-19540955411 / 1000000000000))) = true
  rfl'

theorem compactCertificate354_stateChecks4 :
    compactCertificate354.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 154 12 (1930684778990341 / 4000000000000)) (orderedInterval (-12416792901 / 1000000000000) (-12416792831 / 1000000000000), orderedInterval (34141663275 / 1000000000000) (34141663345 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 110 12 (1377827758949653 / 4000000000000)) (orderedInterval (-14061528569 / 1000000000000) (-14061528419 / 1000000000000), orderedInterval (40646250755 / 1000000000000) (40646250906 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 124 12 (1562309828426787 / 4000000000000)) (orderedInterval (39269932810 / 1000000000000) (39269936957 / 1000000000000), orderedInterval (-9421293533 / 1000000000000) (-9421289386 / 1000000000000))) = true
  rfl'

theorem compactCertificate354_stateChecks5 :
    compactCertificate354.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 104 12 (1302491055954803 / 4000000000000)) (orderedInterval (-13819022565 / 1000000000000) (-13819022426 / 1000000000000), orderedInterval (42022650362 / 1000000000000) (42022650501 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 92 12 (1150790348526863 / 4000000000000)) (orderedInterval (-24345318600 / 1000000000000) (-24345315763 / 1000000000000), orderedInterval (40292972980 / 1000000000000) (40292975817 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 133 12 (333543897211437 / 800000000000)) (orderedInterval (4555747872 / 1000000000000) (4555747876 / 1000000000000), orderedInterval (-38814858420 / 1000000000000) (-38814858416 / 1000000000000))) = true
  rfl'

theorem compactCertificate354_stateChecks6 :
    compactCertificate354.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 73 12 (922599973140439 / 4000000000000)) (orderedInterval (-45387655231 / 1000000000000) (-45387621649 / 1000000000000), orderedInterval (26557224742 / 1000000000000) (26557258324 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (782098214746079 / 4000000000000)) (orderedInterval (57014745767 / 1000000000000) (57014745803 / 1000000000000), orderedInterval (2149053153 / 1000000000000) (2149053190 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 39 12 (489400748803637 / 4000000000000)) (orderedInterval (-41467576931 / 1000000000000) (-41467576930 / 1000000000000), orderedInterval (-58853538063 / 1000000000000) (-58853538062 / 1000000000000))) = true
  rfl'

theorem compactCertificate354_stateChecks7 :
    compactCertificate354.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 21 12 (263201350379979 / 4000000000000)) (orderedInterval (-56378885026 / 1000000000000) (-56378885025 / 1000000000000), orderedInterval (-80172732330 / 1000000000000) (-80172732329 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 57 12 (714642866236937 / 4000000000000)) (orderedInterval (-21843629592 / 1000000000000) (-21843629591 / 1000000000000), orderedInterval (-55492042493 / 1000000000000) (-55492042492 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 78 12 (975783737148649 / 4000000000000)) (orderedInterval (-15749555776 / 1000000000000) (-15749555546 / 1000000000000), orderedInterval (48628902041 / 1000000000000) (48628902270 / 1000000000000))) = true
  rfl'

theorem compactCertificate354_stateChecks8 :
    compactCertificate354.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 33 12 (412599251196363 / 4000000000000)) (orderedInterval (-20305759433 / 1000000000000) (-20305759432 / 1000000000000), orderedInterval (-75793184666 / 1000000000000) (-75793184665 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 134 12 (1677193049287723 / 4000000000000)) (orderedInterval (-30280184837 / 1000000000000) (-30280140162 / 1000000000000), orderedInterval (24559739845 / 1000000000000) (24559784520 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 89 12 (1120287228982757 / 4000000000000)) (orderedInterval (-45319126224 / 1000000000000) (-45319126223 / 1000000000000), orderedInterval (-14725612253 / 1000000000000) (-14725612252 / 1000000000000))) = true
  rfl'

theorem compactCertificate354_states : ∀ j,
    BesselStateValid (compactCertificate354.point j) (compactCertificate354.state j) :=
  compactCertificate354.statesValid_of_checks3 compactCertificate354_stateChecks0
    compactCertificate354_stateChecks1 compactCertificate354_stateChecks2
    compactCertificate354_stateChecks3 compactCertificate354_stateChecks4
    compactCertificate354_stateChecks5 compactCertificate354_stateChecks6
    compactCertificate354_stateChecks7 compactCertificate354_stateChecks8

theorem compactCertificate354_chunkChecks0_0 :
    compactCertificate354.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (451 / 2) 0 (IntervalRat.scale (451 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (4784681529 / 1000000000000) (4784681531 / 1000000000000), orderedInterval (52906885264 / 1000000000000) (52906885266 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (664409117503351 / 4000000000000) 0 (IntervalRat.scale (451 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-23107666808 / 1000000000000) (-23107666807 / 1000000000000), orderedInterval (-57365149782 / 1000000000000) (-57365149781 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (214856257453783 / 800000000000) 0 (IntervalRat.scale (451 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-35653995114 / 1000000000000) (-35653947180 / 1000000000000), orderedInterval (33220485172 / 1000000000000) (33220533106 / 1000000000000)))) (orderedInterval (-411055452 / 1000000000000) (-411052622 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (193872923427557 / 4000000000000) 0 (IntervalRat.scale (451 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-97319544060 / 1000000000000) (-97319525144 / 1000000000000), orderedInterval (61529728685 / 1000000000000) (61529747602 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (520769942808929 / 4000000000000) 0 (IntervalRat.scale (451 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-57680605248 / 1000000000000) (-57680564113 / 1000000000000), orderedInterval (39753406979 / 1000000000000) (39753448115 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1413991698907293 / 4000000000000) 0 (IntervalRat.scale (451 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (27886591881 / 1000000000000) (27886603990 / 1000000000000), orderedInterval (-32027776431 / 1000000000000) (-32027764322 / 1000000000000)))) (orderedInterval (-3032620440 / 1000000000000) (-3032617844 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1041539885618309 / 4000000000000) 0 (IntervalRat.scale (451 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-20058220061 / 1000000000000) (-20058220060 / 1000000000000), orderedInterval (-45156487028 / 1000000000000) (-45156487027 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1784696346485657 / 4000000000000) 0 (IntervalRat.scale (451 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (28454374601 / 1000000000000) (28454374602 / 1000000000000), orderedInterval (24811423947 / 1000000000000) (24811423948 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1314599251196363 / 4000000000000) 0 (IntervalRat.scale (451 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (18443283227 / 1000000000000) (18443283835 / 1000000000000), orderedInterval (-39989579320 / 1000000000000) (-39989578712 / 1000000000000)))) (orderedInterval (-431908998 / 1000000000000) (-431908970 / 1000000000000))) = true
  rfl'

theorem compactCertificate354_chunkChecks0_1 :
    compactCertificate354.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2016933315704549 / 4000000000000) 0 (IntervalRat.scale (451 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (24937040311 / 1000000000000) (24937050709 / 1000000000000), orderedInterval (-25336661359 / 1000000000000) (-25336650961 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1164476992759421 / 4000000000000) 0 (IntervalRat.scale (451 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (12198057002 / 1000000000000) (12198057085 / 1000000000000), orderedInterval (-45165284109 / 1000000000000) (-45165284026 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2066384858270689 / 4000000000000) 0 (IntervalRat.scale (451 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (29181946617 / 1000000000000) (29182011208 / 1000000000000), orderedInterval (-19541020002 / 1000000000000) (-19540955411 / 1000000000000)))) (orderedInterval (621148432 / 1000000000000) (621159557 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1930684778990341 / 4000000000000) 0 (IntervalRat.scale (451 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-12416792901 / 1000000000000) (-12416792831 / 1000000000000), orderedInterval (34141663275 / 1000000000000) (34141663345 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1377827758949653 / 4000000000000) 0 (IntervalRat.scale (451 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-14061528569 / 1000000000000) (-14061528419 / 1000000000000), orderedInterval (40646250755 / 1000000000000) (40646250906 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1562309828426787 / 4000000000000) 0 (IntervalRat.scale (451 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (39269932810 / 1000000000000) (39269936957 / 1000000000000), orderedInterval (-9421293533 / 1000000000000) (-9421289386 / 1000000000000)))) (orderedInterval (-1304265527 / 1000000000000) (-1304265463 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1302491055954803 / 4000000000000) 0 (IntervalRat.scale (451 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-13819022565 / 1000000000000) (-13819022426 / 1000000000000), orderedInterval (42022650362 / 1000000000000) (42022650501 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1150790348526863 / 4000000000000) 0 (IntervalRat.scale (451 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-24345318600 / 1000000000000) (-24345315763 / 1000000000000), orderedInterval (40292972980 / 1000000000000) (40292975817 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (333543897211437 / 800000000000) 0 (IntervalRat.scale (451 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (4555747872 / 1000000000000) (4555747876 / 1000000000000), orderedInterval (-38814858420 / 1000000000000) (-38814858416 / 1000000000000)))) (orderedInterval (1350269139 / 1000000000000) (1350269325 / 1000000000000))) = true
  rfl'

theorem compactCertificate354_chunkChecks0_2 :
    compactCertificate354.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (922599973140439 / 4000000000000) 0 (IntervalRat.scale (451 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-45387655231 / 1000000000000) (-45387621649 / 1000000000000), orderedInterval (26557224742 / 1000000000000) (26557258324 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (782098214746079 / 4000000000000) 0 (IntervalRat.scale (451 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (57014745767 / 1000000000000) (57014745803 / 1000000000000), orderedInterval (2149053153 / 1000000000000) (2149053190 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (489400748803637 / 4000000000000) 0 (IntervalRat.scale (451 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-41467576931 / 1000000000000) (-41467576930 / 1000000000000), orderedInterval (-58853538063 / 1000000000000) (-58853538062 / 1000000000000)))) (orderedInterval (2680117325 / 1000000000000) (2680122754 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (263201350379979 / 4000000000000) 0 (IntervalRat.scale (451 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-56378885026 / 1000000000000) (-56378885025 / 1000000000000), orderedInterval (-80172732330 / 1000000000000) (-80172732329 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (714642866236937 / 4000000000000) 0 (IntervalRat.scale (451 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-21843629592 / 1000000000000) (-21843629591 / 1000000000000), orderedInterval (-55492042493 / 1000000000000) (-55492042492 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (975783737148649 / 4000000000000) 0 (IntervalRat.scale (451 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-15749555776 / 1000000000000) (-15749555546 / 1000000000000), orderedInterval (48628902041 / 1000000000000) (48628902270 / 1000000000000)))) (orderedInterval (2743634245 / 1000000000000) (2743634290 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (412599251196363 / 4000000000000) 0 (IntervalRat.scale (451 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-20305759433 / 1000000000000) (-20305759432 / 1000000000000), orderedInterval (-75793184666 / 1000000000000) (-75793184665 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1677193049287723 / 4000000000000) 0 (IntervalRat.scale (451 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-30280184837 / 1000000000000) (-30280140162 / 1000000000000), orderedInterval (24559739845 / 1000000000000) (24559784520 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1120287228982757 / 4000000000000) 0 (IntervalRat.scale (451 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-45319126224 / 1000000000000) (-45319126223 / 1000000000000), orderedInterval (-14725612253 / 1000000000000) (-14725612252 / 1000000000000)))) (orderedInterval (10845517667 / 1000000000000) (10845521367 / 1000000000000))) = true
  rfl'

theorem compactCertificate354_chunkChecks0 :
    compactCertificate354.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate354.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate354_chunkChecks0_0
    compactCertificate354_chunkChecks0_1 compactCertificate354_chunkChecks0_2

theorem compactCertificate354_chunkChecks1_0 :
    compactCertificate354.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (451 / 2) 1 (IntervalRat.scale (451 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (4784681529 / 1000000000000) (4784681531 / 1000000000000), orderedInterval (52906885264 / 1000000000000) (52906885266 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (664409117503351 / 4000000000000) 1 (IntervalRat.scale (451 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-23107666808 / 1000000000000) (-23107666807 / 1000000000000), orderedInterval (-57365149782 / 1000000000000) (-57365149781 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (214856257453783 / 800000000000) 1 (IntervalRat.scale (451 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-35653995114 / 1000000000000) (-35653947180 / 1000000000000), orderedInterval (33220485172 / 1000000000000) (33220533106 / 1000000000000)))) (orderedInterval (22898456260 / 1000000000000) (22898459629 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (193872923427557 / 4000000000000) 1 (IntervalRat.scale (451 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-97319544060 / 1000000000000) (-97319525144 / 1000000000000), orderedInterval (61529728685 / 1000000000000) (61529747602 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (520769942808929 / 4000000000000) 1 (IntervalRat.scale (451 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-57680605248 / 1000000000000) (-57680564113 / 1000000000000), orderedInterval (39753406979 / 1000000000000) (39753448115 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1413991698907293 / 4000000000000) 1 (IntervalRat.scale (451 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (27886591881 / 1000000000000) (27886603990 / 1000000000000), orderedInterval (-32027776431 / 1000000000000) (-32027764322 / 1000000000000)))) (orderedInterval (4263742130 / 1000000000000) (4263744422 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1041539885618309 / 4000000000000) 1 (IntervalRat.scale (451 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-20058220061 / 1000000000000) (-20058220060 / 1000000000000), orderedInterval (-45156487028 / 1000000000000) (-45156487027 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1784696346485657 / 4000000000000) 1 (IntervalRat.scale (451 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (28454374601 / 1000000000000) (28454374602 / 1000000000000), orderedInterval (24811423947 / 1000000000000) (24811423948 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1314599251196363 / 4000000000000) 1 (IntervalRat.scale (451 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (18443283227 / 1000000000000) (18443283835 / 1000000000000), orderedInterval (-39989579320 / 1000000000000) (-39989578712 / 1000000000000)))) (orderedInterval (-2922747847 / 1000000000000) (-2922747803 / 1000000000000))) = true
  rfl'

theorem compactCertificate354_chunkChecks1_1 :
    compactCertificate354.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2016933315704549 / 4000000000000) 1 (IntervalRat.scale (451 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (24937040311 / 1000000000000) (24937050709 / 1000000000000), orderedInterval (-25336661359 / 1000000000000) (-25336650961 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1164476992759421 / 4000000000000) 1 (IntervalRat.scale (451 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (12198057002 / 1000000000000) (12198057085 / 1000000000000), orderedInterval (-45165284109 / 1000000000000) (-45165284026 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2066384858270689 / 4000000000000) 1 (IntervalRat.scale (451 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (29181946617 / 1000000000000) (29182011208 / 1000000000000), orderedInterval (-19541020002 / 1000000000000) (-19540955411 / 1000000000000)))) (orderedInterval (-617140417 / 1000000000000) (-617115057 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1930684778990341 / 4000000000000) 1 (IntervalRat.scale (451 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-12416792901 / 1000000000000) (-12416792831 / 1000000000000), orderedInterval (34141663275 / 1000000000000) (34141663345 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1377827758949653 / 4000000000000) 1 (IntervalRat.scale (451 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-14061528569 / 1000000000000) (-14061528419 / 1000000000000), orderedInterval (40646250755 / 1000000000000) (40646250906 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1562309828426787 / 4000000000000) 1 (IntervalRat.scale (451 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (39269932810 / 1000000000000) (39269936957 / 1000000000000), orderedInterval (-9421293533 / 1000000000000) (-9421289386 / 1000000000000)))) (orderedInterval (4634522766 / 1000000000000) (4634522871 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1302491055954803 / 4000000000000) 1 (IntervalRat.scale (451 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-13819022565 / 1000000000000) (-13819022426 / 1000000000000), orderedInterval (42022650362 / 1000000000000) (42022650501 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1150790348526863 / 4000000000000) 1 (IntervalRat.scale (451 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-24345318600 / 1000000000000) (-24345315763 / 1000000000000), orderedInterval (40292972980 / 1000000000000) (40292975817 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (333543897211437 / 800000000000) 1 (IntervalRat.scale (451 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (4555747872 / 1000000000000) (4555747876 / 1000000000000), orderedInterval (-38814858420 / 1000000000000) (-38814858416 / 1000000000000)))) (orderedInterval (-4078582418 / 1000000000000) (-4078582177 / 1000000000000))) = true
  rfl'

theorem compactCertificate354_chunkChecks1_2 :
    compactCertificate354.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (922599973140439 / 4000000000000) 1 (IntervalRat.scale (451 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-45387655231 / 1000000000000) (-45387621649 / 1000000000000), orderedInterval (26557224742 / 1000000000000) (26557258324 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (782098214746079 / 4000000000000) 1 (IntervalRat.scale (451 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (57014745767 / 1000000000000) (57014745803 / 1000000000000), orderedInterval (2149053153 / 1000000000000) (2149053190 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (489400748803637 / 4000000000000) 1 (IntervalRat.scale (451 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-41467576931 / 1000000000000) (-41467576930 / 1000000000000), orderedInterval (-58853538063 / 1000000000000) (-58853538062 / 1000000000000)))) (orderedInterval (-5488315625 / 1000000000000) (-5488310078 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (263201350379979 / 4000000000000) 1 (IntervalRat.scale (451 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-56378885026 / 1000000000000) (-56378885025 / 1000000000000), orderedInterval (-80172732330 / 1000000000000) (-80172732329 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (714642866236937 / 4000000000000) 1 (IntervalRat.scale (451 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-21843629592 / 1000000000000) (-21843629591 / 1000000000000), orderedInterval (-55492042493 / 1000000000000) (-55492042492 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (975783737148649 / 4000000000000) 1 (IntervalRat.scale (451 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-15749555776 / 1000000000000) (-15749555546 / 1000000000000), orderedInterval (48628902041 / 1000000000000) (48628902270 / 1000000000000)))) (orderedInterval (-2602303451 / 1000000000000) (-2602303407 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (412599251196363 / 4000000000000) 1 (IntervalRat.scale (451 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-20305759433 / 1000000000000) (-20305759432 / 1000000000000), orderedInterval (-75793184666 / 1000000000000) (-75793184665 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1677193049287723 / 4000000000000) 1 (IntervalRat.scale (451 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-30280184837 / 1000000000000) (-30280140162 / 1000000000000), orderedInterval (24559739845 / 1000000000000) (24559784520 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1120287228982757 / 4000000000000) 1 (IntervalRat.scale (451 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-45319126224 / 1000000000000) (-45319126223 / 1000000000000), orderedInterval (-14725612253 / 1000000000000) (-14725612252 / 1000000000000)))) (orderedInterval (-494813240 / 1000000000000) (-494806389 / 1000000000000))) = true
  rfl'

theorem compactCertificate354_chunkChecks1 :
    compactCertificate354.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate354.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate354_chunkChecks1_0
    compactCertificate354_chunkChecks1_1 compactCertificate354_chunkChecks1_2

theorem compactCertificate354_chunkChecks2_0 :
    compactCertificate354.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (451 / 2) 2 (IntervalRat.scale (451 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (4784681529 / 1000000000000) (4784681531 / 1000000000000), orderedInterval (52906885264 / 1000000000000) (52906885266 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (664409117503351 / 4000000000000) 2 (IntervalRat.scale (451 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-23107666808 / 1000000000000) (-23107666807 / 1000000000000), orderedInterval (-57365149782 / 1000000000000) (-57365149781 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (214856257453783 / 800000000000) 2 (IntervalRat.scale (451 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-35653995114 / 1000000000000) (-35653947180 / 1000000000000), orderedInterval (33220485172 / 1000000000000) (33220533106 / 1000000000000)))) (orderedInterval (1086562748 / 1000000000000) (1086566775 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (193872923427557 / 4000000000000) 2 (IntervalRat.scale (451 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-97319544060 / 1000000000000) (-97319525144 / 1000000000000), orderedInterval (61529728685 / 1000000000000) (61529747602 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (520769942808929 / 4000000000000) 2 (IntervalRat.scale (451 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-57680605248 / 1000000000000) (-57680564113 / 1000000000000), orderedInterval (39753406979 / 1000000000000) (39753448115 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1413991698907293 / 4000000000000) 2 (IntervalRat.scale (451 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (27886591881 / 1000000000000) (27886603990 / 1000000000000), orderedInterval (-32027776431 / 1000000000000) (-32027764322 / 1000000000000)))) (orderedInterval (5506041182 / 1000000000000) (5506043861 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1041539885618309 / 4000000000000) 2 (IntervalRat.scale (451 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-20058220061 / 1000000000000) (-20058220060 / 1000000000000), orderedInterval (-45156487028 / 1000000000000) (-45156487027 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1784696346485657 / 4000000000000) 2 (IntervalRat.scale (451 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (28454374601 / 1000000000000) (28454374602 / 1000000000000), orderedInterval (24811423947 / 1000000000000) (24811423948 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1314599251196363 / 4000000000000) 2 (IntervalRat.scale (451 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (18443283227 / 1000000000000) (18443283835 / 1000000000000), orderedInterval (-39989579320 / 1000000000000) (-39989578712 / 1000000000000)))) (orderedInterval (2502031433 / 1000000000000) (2502031505 / 1000000000000))) = true
  rfl'

theorem compactCertificate354_chunkChecks2_1 :
    compactCertificate354.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2016933315704549 / 4000000000000) 2 (IntervalRat.scale (451 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (24937040311 / 1000000000000) (24937050709 / 1000000000000), orderedInterval (-25336661359 / 1000000000000) (-25336650961 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1164476992759421 / 4000000000000) 2 (IntervalRat.scale (451 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (12198057002 / 1000000000000) (12198057085 / 1000000000000), orderedInterval (-45165284109 / 1000000000000) (-45165284026 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2066384858270689 / 4000000000000) 2 (IntervalRat.scale (451 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (29181946617 / 1000000000000) (29182011208 / 1000000000000), orderedInterval (-19541020002 / 1000000000000) (-19540955411 / 1000000000000)))) (orderedInterval (-1120055546 / 1000000000000) (-1119997600 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1930684778990341 / 4000000000000) 2 (IntervalRat.scale (451 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-12416792901 / 1000000000000) (-12416792831 / 1000000000000), orderedInterval (34141663275 / 1000000000000) (34141663345 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1377827758949653 / 4000000000000) 2 (IntervalRat.scale (451 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-14061528569 / 1000000000000) (-14061528419 / 1000000000000), orderedInterval (40646250755 / 1000000000000) (40646250906 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1562309828426787 / 4000000000000) 2 (IntervalRat.scale (451 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (39269932810 / 1000000000000) (39269936957 / 1000000000000), orderedInterval (-9421293533 / 1000000000000) (-9421289386 / 1000000000000)))) (orderedInterval (2651262586 / 1000000000000) (2651262761 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1302491055954803 / 4000000000000) 2 (IntervalRat.scale (451 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-13819022565 / 1000000000000) (-13819022426 / 1000000000000), orderedInterval (42022650362 / 1000000000000) (42022650501 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1150790348526863 / 4000000000000) 2 (IntervalRat.scale (451 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-24345318600 / 1000000000000) (-24345315763 / 1000000000000), orderedInterval (40292972980 / 1000000000000) (40292975817 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (333543897211437 / 800000000000) 2 (IntervalRat.scale (451 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (4555747872 / 1000000000000) (4555747876 / 1000000000000), orderedInterval (-38814858420 / 1000000000000) (-38814858416 / 1000000000000)))) (orderedInterval (-2315660190 / 1000000000000) (-2315659874 / 1000000000000))) = true
  rfl'

theorem compactCertificate354_chunkChecks2_2 :
    compactCertificate354.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (922599973140439 / 4000000000000) 2 (IntervalRat.scale (451 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-45387655231 / 1000000000000) (-45387621649 / 1000000000000), orderedInterval (26557224742 / 1000000000000) (26557258324 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (782098214746079 / 4000000000000) 2 (IntervalRat.scale (451 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (57014745767 / 1000000000000) (57014745803 / 1000000000000), orderedInterval (2149053153 / 1000000000000) (2149053190 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (489400748803637 / 4000000000000) 2 (IntervalRat.scale (451 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-41467576931 / 1000000000000) (-41467576930 / 1000000000000), orderedInterval (-58853538063 / 1000000000000) (-58853538062 / 1000000000000)))) (orderedInterval (-4744529000 / 1000000000000) (-4744523306 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (263201350379979 / 4000000000000) 2 (IntervalRat.scale (451 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-56378885026 / 1000000000000) (-56378885025 / 1000000000000), orderedInterval (-80172732330 / 1000000000000) (-80172732329 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (714642866236937 / 4000000000000) 2 (IntervalRat.scale (451 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-21843629592 / 1000000000000) (-21843629591 / 1000000000000), orderedInterval (-55492042493 / 1000000000000) (-55492042492 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (975783737148649 / 4000000000000) 2 (IntervalRat.scale (451 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-15749555776 / 1000000000000) (-15749555546 / 1000000000000), orderedInterval (48628902041 / 1000000000000) (48628902270 / 1000000000000)))) (orderedInterval (-1800749547 / 1000000000000) (-1800749501 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (412599251196363 / 4000000000000) 2 (IntervalRat.scale (451 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-20305759433 / 1000000000000) (-20305759432 / 1000000000000), orderedInterval (-75793184666 / 1000000000000) (-75793184665 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1677193049287723 / 4000000000000) 2 (IntervalRat.scale (451 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-30280184837 / 1000000000000) (-30280140162 / 1000000000000), orderedInterval (24559739845 / 1000000000000) (24559784520 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1120287228982757 / 4000000000000) 2 (IntervalRat.scale (451 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-45319126224 / 1000000000000) (-45319126223 / 1000000000000), orderedInterval (-14725612253 / 1000000000000) (-14725612252 / 1000000000000)))) (orderedInterval (-21610875250 / 1000000000000) (-21610862516 / 1000000000000))) = true
  rfl'

theorem compactCertificate354_chunkChecks2 :
    compactCertificate354.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate354.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate354_chunkChecks2_0
    compactCertificate354_chunkChecks2_1 compactCertificate354_chunkChecks2_2

theorem compactCertificate354_chunkChecks3_0 :
    compactCertificate354.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (451 / 2) 3 (IntervalRat.scale (451 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (4784681529 / 1000000000000) (4784681531 / 1000000000000), orderedInterval (52906885264 / 1000000000000) (52906885266 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (664409117503351 / 4000000000000) 3 (IntervalRat.scale (451 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-23107666808 / 1000000000000) (-23107666807 / 1000000000000), orderedInterval (-57365149782 / 1000000000000) (-57365149781 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (214856257453783 / 800000000000) 3 (IntervalRat.scale (451 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-35653995114 / 1000000000000) (-35653947180 / 1000000000000), orderedInterval (33220485172 / 1000000000000) (33220533106 / 1000000000000)))) (orderedInterval (-24054538789 / 1000000000000) (-24054533994 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (193872923427557 / 4000000000000) 3 (IntervalRat.scale (451 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-97319544060 / 1000000000000) (-97319525144 / 1000000000000), orderedInterval (61529728685 / 1000000000000) (61529747602 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (520769942808929 / 4000000000000) 3 (IntervalRat.scale (451 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-57680605248 / 1000000000000) (-57680564113 / 1000000000000), orderedInterval (39753406979 / 1000000000000) (39753448115 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1413991698907293 / 4000000000000) 3 (IntervalRat.scale (451 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (27886591881 / 1000000000000) (27886603990 / 1000000000000), orderedInterval (-32027776431 / 1000000000000) (-32027764322 / 1000000000000)))) (orderedInterval (-9068140072 / 1000000000000) (-9068136388 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1041539885618309 / 4000000000000) 3 (IntervalRat.scale (451 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-20058220061 / 1000000000000) (-20058220060 / 1000000000000), orderedInterval (-45156487028 / 1000000000000) (-45156487027 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1784696346485657 / 4000000000000) 3 (IntervalRat.scale (451 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (28454374601 / 1000000000000) (28454374602 / 1000000000000), orderedInterval (24811423947 / 1000000000000) (24811423948 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1314599251196363 / 4000000000000) 3 (IntervalRat.scale (451 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (18443283227 / 1000000000000) (18443283835 / 1000000000000), orderedInterval (-39989579320 / 1000000000000) (-39989578712 / 1000000000000)))) (orderedInterval (8908587877 / 1000000000000) (8908587995 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate354_chunkChecks3_1 :
    compactCertificate354.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2016933315704549 / 4000000000000) 3 (IntervalRat.scale (451 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (24937040311 / 1000000000000) (24937050709 / 1000000000000), orderedInterval (-25336661359 / 1000000000000) (-25336650961 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1164476992759421 / 4000000000000) 3 (IntervalRat.scale (451 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (12198057002 / 1000000000000) (12198057085 / 1000000000000), orderedInterval (-45165284109 / 1000000000000) (-45165284026 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2066384858270689 / 4000000000000) 3 (IntervalRat.scale (451 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (29181946617 / 1000000000000) (29182011208 / 1000000000000), orderedInterval (-19541020002 / 1000000000000) (-19540955411 / 1000000000000)))) (orderedInterval (-9730567449 / 1000000000000) (-9730435260 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1930684778990341 / 4000000000000) 3 (IntervalRat.scale (451 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-12416792901 / 1000000000000) (-12416792831 / 1000000000000), orderedInterval (34141663275 / 1000000000000) (34141663345 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1377827758949653 / 4000000000000) 3 (IntervalRat.scale (451 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-14061528569 / 1000000000000) (-14061528419 / 1000000000000), orderedInterval (40646250755 / 1000000000000) (40646250906 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1562309828426787 / 4000000000000) 3 (IntervalRat.scale (451 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (39269932810 / 1000000000000) (39269936957 / 1000000000000), orderedInterval (-9421293533 / 1000000000000) (-9421289386 / 1000000000000)))) (orderedInterval (-7914589621 / 1000000000000) (-7914589325 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1302491055954803 / 4000000000000) 3 (IntervalRat.scale (451 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-13819022565 / 1000000000000) (-13819022426 / 1000000000000), orderedInterval (42022650362 / 1000000000000) (42022650501 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1150790348526863 / 4000000000000) 3 (IntervalRat.scale (451 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-24345318600 / 1000000000000) (-24345315763 / 1000000000000), orderedInterval (40292972980 / 1000000000000) (40292975817 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (333543897211437 / 800000000000) 3 (IntervalRat.scale (451 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (4555747872 / 1000000000000) (4555747876 / 1000000000000), orderedInterval (-38814858420 / 1000000000000) (-38814858416 / 1000000000000)))) (orderedInterval (9618921302 / 1000000000000) (9618921718 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate354_chunkChecks3_2 :
    compactCertificate354.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (922599973140439 / 4000000000000) 3 (IntervalRat.scale (451 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-45387655231 / 1000000000000) (-45387621649 / 1000000000000), orderedInterval (26557224742 / 1000000000000) (26557258324 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (782098214746079 / 4000000000000) 3 (IntervalRat.scale (451 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (57014745767 / 1000000000000) (57014745803 / 1000000000000), orderedInterval (2149053153 / 1000000000000) (2149053190 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (489400748803637 / 4000000000000) 3 (IntervalRat.scale (451 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-41467576931 / 1000000000000) (-41467576930 / 1000000000000), orderedInterval (-58853538063 / 1000000000000) (-58853538062 / 1000000000000)))) (orderedInterval (4950183436 / 1000000000000) (4950189257 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (263201350379979 / 4000000000000) 3 (IntervalRat.scale (451 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-56378885026 / 1000000000000) (-56378885025 / 1000000000000), orderedInterval (-80172732330 / 1000000000000) (-80172732329 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (714642866236937 / 4000000000000) 3 (IntervalRat.scale (451 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-21843629592 / 1000000000000) (-21843629591 / 1000000000000), orderedInterval (-55492042493 / 1000000000000) (-55492042492 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (975783737148649 / 4000000000000) 3 (IntervalRat.scale (451 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-15749555776 / 1000000000000) (-15749555546 / 1000000000000), orderedInterval (48628902041 / 1000000000000) (48628902270 / 1000000000000)))) (orderedInterval (4063330853 / 1000000000000) (4063330901 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (412599251196363 / 4000000000000) 3 (IntervalRat.scale (451 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-20305759433 / 1000000000000) (-20305759432 / 1000000000000), orderedInterval (-75793184666 / 1000000000000) (-75793184665 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1677193049287723 / 4000000000000) 3 (IntervalRat.scale (451 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-30280184837 / 1000000000000) (-30280140162 / 1000000000000), orderedInterval (24559739845 / 1000000000000) (24559784520 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1120287228982757 / 4000000000000) 3 (IntervalRat.scale (451 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-45319126224 / 1000000000000) (-45319126223 / 1000000000000), orderedInterval (-14725612253 / 1000000000000) (-14725612252 / 1000000000000)))) (orderedInterval (7698627080 / 1000000000000) (7698650715 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate354_chunkChecks3 :
    compactCertificate354.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate354.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate354_chunkChecks3_0
    compactCertificate354_chunkChecks3_1 compactCertificate354_chunkChecks3_2

theorem compactCertificate354_chunkChecks4_0 :
    compactCertificate354.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (451 / 2) 4 (IntervalRat.scale (451 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (4784681529 / 1000000000000) (4784681531 / 1000000000000), orderedInterval (52906885264 / 1000000000000) (52906885266 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (664409117503351 / 4000000000000) 4 (IntervalRat.scale (451 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-23107666808 / 1000000000000) (-23107666807 / 1000000000000), orderedInterval (-57365149782 / 1000000000000) (-57365149781 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (214856257453783 / 800000000000) 4 (IntervalRat.scale (451 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-35653995114 / 1000000000000) (-35653947180 / 1000000000000), orderedInterval (33220485172 / 1000000000000) (33220533106 / 1000000000000)))) (orderedInterval (-2163257480 / 1000000000000) (-2163251750 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (193872923427557 / 4000000000000) 4 (IntervalRat.scale (451 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-97319544060 / 1000000000000) (-97319525144 / 1000000000000), orderedInterval (61529728685 / 1000000000000) (61529747602 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (520769942808929 / 4000000000000) 4 (IntervalRat.scale (451 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-57680605248 / 1000000000000) (-57680564113 / 1000000000000), orderedInterval (39753406979 / 1000000000000) (39753448115 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1413991698907293 / 4000000000000) 4 (IntervalRat.scale (451 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (27886591881 / 1000000000000) (27886603990 / 1000000000000), orderedInterval (-32027776431 / 1000000000000) (-32027764322 / 1000000000000)))) (orderedInterval (-12123118350 / 1000000000000) (-12123112853 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1041539885618309 / 4000000000000) 4 (IntervalRat.scale (451 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-20058220061 / 1000000000000) (-20058220060 / 1000000000000), orderedInterval (-45156487028 / 1000000000000) (-45156487027 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1784696346485657 / 4000000000000) 4 (IntervalRat.scale (451 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (28454374601 / 1000000000000) (28454374602 / 1000000000000), orderedInterval (24811423947 / 1000000000000) (24811423948 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1314599251196363 / 4000000000000) 4 (IntervalRat.scale (451 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (18443283227 / 1000000000000) (18443283835 / 1000000000000), orderedInterval (-39989579320 / 1000000000000) (-39989578712 / 1000000000000)))) (orderedInterval (-11518781777 / 1000000000000) (-11518781577 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate354_chunkChecks4_1 :
    compactCertificate354.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2016933315704549 / 4000000000000) 4 (IntervalRat.scale (451 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (24937040311 / 1000000000000) (24937050709 / 1000000000000), orderedInterval (-25336661359 / 1000000000000) (-25336650961 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1164476992759421 / 4000000000000) 4 (IntervalRat.scale (451 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (12198057002 / 1000000000000) (12198057085 / 1000000000000), orderedInterval (-45165284109 / 1000000000000) (-45165284026 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2066384858270689 / 4000000000000) 4 (IntervalRat.scale (451 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (29181946617 / 1000000000000) (29182011208 / 1000000000000), orderedInterval (-19541020002 / 1000000000000) (-19540955411 / 1000000000000)))) (orderedInterval (6082391740 / 1000000000000) (6082693942 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1930684778990341 / 4000000000000) 4 (IntervalRat.scale (451 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-12416792901 / 1000000000000) (-12416792831 / 1000000000000), orderedInterval (34141663275 / 1000000000000) (34141663345 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1377827758949653 / 4000000000000) 4 (IntervalRat.scale (451 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-14061528569 / 1000000000000) (-14061528419 / 1000000000000), orderedInterval (40646250755 / 1000000000000) (40646250906 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1562309828426787 / 4000000000000) 4 (IntervalRat.scale (451 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (39269932810 / 1000000000000) (39269936957 / 1000000000000), orderedInterval (-9421293533 / 1000000000000) (-9421289386 / 1000000000000)))) (orderedInterval (-4252555086 / 1000000000000) (-4252554579 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1302491055954803 / 4000000000000) 4 (IntervalRat.scale (451 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-13819022565 / 1000000000000) (-13819022426 / 1000000000000), orderedInterval (42022650362 / 1000000000000) (42022650501 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1150790348526863 / 4000000000000) 4 (IntervalRat.scale (451 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-24345318600 / 1000000000000) (-24345315763 / 1000000000000), orderedInterval (40292972980 / 1000000000000) (40292975817 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (333543897211437 / 800000000000) 4 (IntervalRat.scale (451 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (4555747872 / 1000000000000) (4555747876 / 1000000000000), orderedInterval (-38814858420 / 1000000000000) (-38814858416 / 1000000000000)))) (orderedInterval (4275184480 / 1000000000000) (4275185035 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate354_chunkChecks4_2 :
    compactCertificate354.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (922599973140439 / 4000000000000) 4 (IntervalRat.scale (451 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-45387655231 / 1000000000000) (-45387621649 / 1000000000000), orderedInterval (26557224742 / 1000000000000) (26557258324 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (782098214746079 / 4000000000000) 4 (IntervalRat.scale (451 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (57014745767 / 1000000000000) (57014745803 / 1000000000000), orderedInterval (2149053153 / 1000000000000) (2149053190 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (489400748803637 / 4000000000000) 4 (IntervalRat.scale (451 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-41467576931 / 1000000000000) (-41467576930 / 1000000000000), orderedInterval (-58853538063 / 1000000000000) (-58853538062 / 1000000000000)))) (orderedInterval (5958173571 / 1000000000000) (5958179548 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (263201350379979 / 4000000000000) 4 (IntervalRat.scale (451 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-56378885026 / 1000000000000) (-56378885025 / 1000000000000), orderedInterval (-80172732330 / 1000000000000) (-80172732329 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (714642866236937 / 4000000000000) 4 (IntervalRat.scale (451 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-21843629592 / 1000000000000) (-21843629591 / 1000000000000), orderedInterval (-55492042493 / 1000000000000) (-55492042492 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (975783737148649 / 4000000000000) 4 (IntervalRat.scale (451 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-15749555776 / 1000000000000) (-15749555546 / 1000000000000), orderedInterval (48628902041 / 1000000000000) (48628902270 / 1000000000000)))) (orderedInterval (1819865406 / 1000000000000) (1819865457 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (412599251196363 / 4000000000000) 4 (IntervalRat.scale (451 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-20305759433 / 1000000000000) (-20305759432 / 1000000000000), orderedInterval (-75793184666 / 1000000000000) (-75793184665 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1677193049287723 / 4000000000000) 4 (IntervalRat.scale (451 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-30280184837 / 1000000000000) (-30280140162 / 1000000000000), orderedInterval (24559739845 / 1000000000000) (24559784520 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1120287228982757 / 4000000000000) 4 (IntervalRat.scale (451 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-45319126224 / 1000000000000) (-45319126223 / 1000000000000), orderedInterval (-14725612253 / 1000000000000) (-14725612252 / 1000000000000)))) (orderedInterval (49623670934 / 1000000000000) (49623714934 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate354_chunkChecks4 :
    compactCertificate354.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate354.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate354_chunkChecks4_0
    compactCertificate354_chunkChecks4_1 compactCertificate354_chunkChecks4_2

theorem compactCertificate354_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate354.chunkCheck r b = true :=
  compactCertificate354.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate354_chunkChecks0
    · exact compactCertificate354_chunkChecks1
    · exact compactCertificate354_chunkChecks2
    · exact compactCertificate354_chunkChecks3
    · exact compactCertificate354_chunkChecks4)

theorem compactCertificate354_coefficient0 :
    compactCertificate354.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate354_coefficient1 :
    compactCertificate354.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate354_coefficient2 :
    compactCertificate354.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate354_coefficient3 :
    compactCertificate354.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate354_coefficient4 :
    compactCertificate354.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate354_coefficients : ∀ r : Fin 5,
    compactCertificate354.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate354_coefficient0
  · exact compactCertificate354_coefficient1
  · exact compactCertificate354_coefficient2
  · exact compactCertificate354_coefficient3
  · exact compactCertificate354_coefficient4

theorem compactCertificate354_lower : (1 : ℚ) ≤ compactCertificate354.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate354, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate354_proves {t : ℝ} (ht : t ∈ compactCertificate354.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate354.proves compactCertificate354_states compactCertificate354_chunks
    compactCertificate354_coefficients compactCertificate354_lower ht

end Erdos232
