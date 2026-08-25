/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate613 : CompactCertificate where
  left := 484
  right := 485
  center := 969 / 2
  grid := fun i =>
    match i.val with
    | 0 => 154
    | 1 => 114
    | 2 => 184
    | 3 => 33
    | 4 => 89
    | 5 => 242
    | 6 => 178
    | 7 => 305
    | 8 => 225
    | 9 => 345
    | 10 => 199
    | 11 => 353
    | 12 => 330
    | 13 => 236
    | 14 => 267
    | 15 => 223
    | 16 => 197
    | 17 => 285
    | 18 => 158
    | 19 => 134
    | 20 => 84
    | 21 => 45
    | 22 => 122
    | 23 => 167
    | 24 => 71
    | 25 => 287
    | _ => 192
  point := fun i =>
    match i.val with
    | 0 => 969 / 2
    | 1 => 1427522028516069 / 4000000000000
    | 2 => 461631293731077 / 800000000000
    | 3 => 416547367630383 / 4000000000000
    | 4 => 1118904821689251 / 4000000000000
    | 5 => 3038044248871767 / 4000000000000
    | 6 => 2237809643379471 / 4000000000000
    | 7 => 3834524966174283 / 4000000000000
    | 8 => 2824493734832097 / 4000000000000
    | 9 => 4333499740394031 / 4000000000000
    | 10 => 2501947241649399 / 4000000000000
    | 11 => 4439749285286691 / 4000000000000
    | 12 => 4148189691444879 / 4000000000000
    | 13 => 2960343898940607 / 4000000000000
    | 14 => 3356714465067753 / 4000000000000
    | 15 => 2798478565898457 / 4000000000000
    | 16 => 2472540682311597 / 4000000000000
    | 17 => 716638661636103 / 800000000000
    | 18 => 1982260252711941 / 4000000000000
    | 19 => 1680383969155101 / 4000000000000
    | 20 => 1051506265167903 / 4000000000000
    | 21 => 565503566559201 / 4000000000000
    | 22 => 1535452189320603 / 4000000000000
    | 23 => 2096528694671931 / 4000000000000
    | 24 => 886493734832097 / 4000000000000
    | 25 => 3603547815431937 / 4000000000000
    | _ => 2407002937659183 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (36099014767 / 1000000000000) (36099014912 / 1000000000000), orderedInterval (3254119310 / 1000000000000) (3254119455 / 1000000000000))
    | 1 => (orderedInterval (-19353784409 / 1000000000000) (-19353783540 / 1000000000000), orderedInterval (37567463690 / 1000000000000) (37567464559 / 1000000000000))
    | 2 => (orderedInterval (-7531881458 / 1000000000000) (-7531881452 / 1000000000000), orderedInterval (32356541785 / 1000000000000) (32356541790 / 1000000000000))
    | 3 => (orderedInterval (-74160893298 / 1000000000000) (-74160893297 / 1000000000000), orderedInterval (-24410963466 / 1000000000000) (-24410963465 / 1000000000000))
    | 4 => (orderedInterval (-37646811849 / 1000000000000) (-37646811848 / 1000000000000), orderedInterval (-29234314380 / 1000000000000) (-29234314379 / 1000000000000))
    | 5 => (orderedInterval (893699894 / 1000000000000) (893699895 / 1000000000000), orderedInterval (28937247134 / 1000000000000) (28937247135 / 1000000000000))
    | 6 => (orderedInterval (28990338264 / 1000000000000) (28990338265 / 1000000000000), orderedInterval (17222099243 / 1000000000000) (17222099244 / 1000000000000))
    | 7 => (orderedInterval (-24294379525 / 1000000000000) (-24294379397 / 1000000000000), orderedInterval (-8582415003 / 1000000000000) (-8582414875 / 1000000000000))
    | 8 => (orderedInterval (-1509912349 / 1000000000000) (-1509912348 / 1000000000000), orderedInterval (-29987103284 / 1000000000000) (-29987103283 / 1000000000000))
    | 9 => (orderedInterval (-7412295664 / 1000000000000) (-7412295663 / 1000000000000), orderedInterval (-23076535284 / 1000000000000) (-23076535283 / 1000000000000))
    | 10 => (orderedInterval (-28360470692 / 1000000000000) (-28360470690 / 1000000000000), orderedInterval (-14588365846 / 1000000000000) (-14588365845 / 1000000000000))
    | 11 => (orderedInterval (-23605594743 / 1000000000000) (-23605522172 / 1000000000000), orderedInterval (4053025950 / 1000000000000) (4053098521 / 1000000000000))
    | 12 => (orderedInterval (22160549670 / 1000000000000) (22160549709 / 1000000000000), orderedInterval (11070254067 / 1000000000000) (11070254105 / 1000000000000))
    | 13 => (orderedInterval (-15196270971 / 1000000000000) (-15196270796 / 1000000000000), orderedInterval (25095530910 / 1000000000000) (25095531085 / 1000000000000))
    | 14 => (orderedInterval (-25236473838 / 1000000000000) (-25236473820 / 1000000000000), orderedInterval (-11018675050 / 1000000000000) (-11018675031 / 1000000000000))
    | 15 => (orderedInterval (5112394450 / 1000000000000) (5112394451 / 1000000000000), orderedInterval (-29732678221 / 1000000000000) (-29732678219 / 1000000000000))
    | 16 => (orderedInterval (-853990979 / 1000000000000) (-853990978 / 1000000000000), orderedInterval (-32080064419 / 1000000000000) (-32080064418 / 1000000000000))
    | 17 => (orderedInterval (-25122433226 / 1000000000000) (-25122433145 / 1000000000000), orderedInterval (-8904293825 / 1000000000000) (-8904293745 / 1000000000000))
    | 18 => (orderedInterval (-768036455 / 1000000000000) (-768036453 / 1000000000000), orderedInterval (35834346598 / 1000000000000) (35834346599 / 1000000000000))
    | 19 => (orderedInterval (-3588863262 / 1000000000000) (-3588863260 / 1000000000000), orderedInterval (38766832348 / 1000000000000) (38766832351 / 1000000000000))
    | 20 => (orderedInterval (-11328927426 / 1000000000000) (-11328927361 / 1000000000000), orderedInterval (47911039596 / 1000000000000) (47911039661 / 1000000000000))
    | 21 => (orderedInterval (-47608106632 / 1000000000000) (-47608106631 / 1000000000000), orderedInterval (-47123246866 / 1000000000000) (-47123246865 / 1000000000000))
    | 22 => (orderedInterval (39936600356 / 1000000000000) (39936600370 / 1000000000000), orderedInterval (7918057722 / 1000000000000) (7918057736 / 1000000000000))
    | 23 => (orderedInterval (-9341628044 / 1000000000000) (-9341628043 / 1000000000000), orderedInterval (-33567141171 / 1000000000000) (-33567141170 / 1000000000000))
    | 24 => (orderedInterval (32213658354 / 1000000000000) (32213669823 / 1000000000000), orderedInterval (-42907375678 / 1000000000000) (-42907364208 / 1000000000000))
    | 25 => (orderedInterval (-933449835 / 1000000000000) (-933449834 / 1000000000000), orderedInterval (-26566146514 / 1000000000000) (-26566146513 / 1000000000000))
    | _ => (orderedInterval (-19680834591 / 1000000000000) (-19680833030 / 1000000000000), orderedInterval (25912507501 / 1000000000000) (25912509062 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (13686066604 / 1000000000000) (13686066704 / 1000000000000)
      | 1 => orderedInterval (-633490554 / 1000000000000) (-633490495 / 1000000000000)
      | 2 => orderedInterval (712844246 / 1000000000000) (712844278 / 1000000000000)
      | 3 => orderedInterval (-4139876530 / 1000000000000) (-4139866021 / 1000000000000)
      | 4 => orderedInterval (-1709358181 / 1000000000000) (-1709358105 / 1000000000000)
      | 5 => orderedInterval (-535326238 / 1000000000000) (-535326189 / 1000000000000)
      | 6 => orderedInterval (-42883637 / 1000000000000) (-42883512 / 1000000000000)
      | 7 => orderedInterval (688984906 / 1000000000000) (688984964 / 1000000000000)
      | _ => orderedInterval (3962825257 / 1000000000000) (3962825753 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (3809041077 / 1000000000000) (3809041179 / 1000000000000)
      | 1 => orderedInterval (-3784145083 / 1000000000000) (-3784145016 / 1000000000000)
      | 2 => orderedInterval (-532473039 / 1000000000000) (-532472983 / 1000000000000)
      | 3 => orderedInterval (9093338116 / 1000000000000) (9093362148 / 1000000000000)
      | 4 => orderedInterval (3293785330 / 1000000000000) (3293785451 / 1000000000000)
      | 5 => orderedInterval (1424883762 / 1000000000000) (1424883833 / 1000000000000)
      | 6 => orderedInterval (-6916742084 / 1000000000000) (-6916741970 / 1000000000000)
      | 7 => orderedInterval (2894562960 / 1000000000000) (2894563013 / 1000000000000)
      | _ => orderedInterval (-2135737785 / 1000000000000) (-2135737200 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-13591461636 / 1000000000000) (-13591461530 / 1000000000000)
      | 1 => orderedInterval (584950787 / 1000000000000) (584950879 / 1000000000000)
      | 2 => orderedInterval (-2854930116 / 1000000000000) (-2854930017 / 1000000000000)
      | 3 => orderedInterval (14509137314 / 1000000000000) (14509192359 / 1000000000000)
      | 4 => orderedInterval (4795987282 / 1000000000000) (4795987480 / 1000000000000)
      | 5 => orderedInterval (1993291854 / 1000000000000) (1993291962 / 1000000000000)
      | 6 => orderedInterval (-158341651 / 1000000000000) (-158341543 / 1000000000000)
      | 7 => orderedInterval (-349938263 / 1000000000000) (-349938211 / 1000000000000)
      | _ => orderedInterval (-5995112595 / 1000000000000) (-5995111849 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-4609362203 / 1000000000000) (-4609362091 / 1000000000000)
      | 1 => orderedInterval (8126297629 / 1000000000000) (8126297767 / 1000000000000)
      | 2 => orderedInterval (198971809 / 1000000000000) (198971993 / 1000000000000)
      | 3 => orderedInterval (-50475670969 / 1000000000000) (-50475544952 / 1000000000000)
      | 4 => orderedInterval (-6798056239 / 1000000000000) (-6798055910 / 1000000000000)
      | 5 => orderedInterval (-1341781357 / 1000000000000) (-1341781190 / 1000000000000)
      | 6 => orderedInterval (7312746245 / 1000000000000) (7312746350 / 1000000000000)
      | 7 => orderedInterval (-3188446371 / 1000000000000) (-3188446317 / 1000000000000)
      | _ => orderedInterval (-4550577840 / 1000000000000) (-4550576841 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (13384966474 / 1000000000000) (13384966594 / 1000000000000)
      | 1 => orderedInterval (-568224651 / 1000000000000) (-568224439 / 1000000000000)
      | 2 => orderedInterval (11318908494 / 1000000000000) (11318908837 / 1000000000000)
      | 3 => orderedInterval (-65128499901 / 1000000000000) (-65128211085 / 1000000000000)
      | 4 => orderedInterval (-15043725781 / 1000000000000) (-15043725219 / 1000000000000)
      | 5 => orderedInterval (-7125117387 / 1000000000000) (-7125117118 / 1000000000000)
      | 6 => orderedInterval (187074979 / 1000000000000) (187075082 / 1000000000000)
      | 7 => orderedInterval (643054979 / 1000000000000) (643055035 / 1000000000000)
      | _ => orderedInterval (9722331155 / 1000000000000) (9722332547 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (11989785873 / 1000000000000) (11989797377 / 1000000000000)
    | 1 => orderedInterval (7146513254 / 1000000000000) (7146538455 / 1000000000000)
    | 2 => orderedInterval (-1066417024 / 1000000000000) (-1066360470 / 1000000000000)
    | 3 => orderedInterval (-55325879296 / 1000000000000) (-55325751191 / 1000000000000)
    | _ => orderedInterval (-52609231639 / 1000000000000) (-52608939766 / 1000000000000)

theorem compactCertificate613_stateChecks0 :
    compactCertificate613.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 154 12 (969 / 2)) (orderedInterval (36099014767 / 1000000000000) (36099014912 / 1000000000000), orderedInterval (3254119310 / 1000000000000) (3254119455 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 114 12 (1427522028516069 / 4000000000000)) (orderedInterval (-19353784409 / 1000000000000) (-19353783540 / 1000000000000), orderedInterval (37567463690 / 1000000000000) (37567464559 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 184 12 (461631293731077 / 800000000000)) (orderedInterval (-7531881458 / 1000000000000) (-7531881452 / 1000000000000), orderedInterval (32356541785 / 1000000000000) (32356541790 / 1000000000000))) = true
  rfl'

theorem compactCertificate613_stateChecks1 :
    compactCertificate613.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 33 12 (416547367630383 / 4000000000000)) (orderedInterval (-74160893298 / 1000000000000) (-74160893297 / 1000000000000), orderedInterval (-24410963466 / 1000000000000) (-24410963465 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 89 12 (1118904821689251 / 4000000000000)) (orderedInterval (-37646811849 / 1000000000000) (-37646811848 / 1000000000000), orderedInterval (-29234314380 / 1000000000000) (-29234314379 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 242 12 (3038044248871767 / 4000000000000)) (orderedInterval (893699894 / 1000000000000) (893699895 / 1000000000000), orderedInterval (28937247134 / 1000000000000) (28937247135 / 1000000000000))) = true
  rfl'

theorem compactCertificate613_stateChecks2 :
    compactCertificate613.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 178 12 (2237809643379471 / 4000000000000)) (orderedInterval (28990338264 / 1000000000000) (28990338265 / 1000000000000), orderedInterval (17222099243 / 1000000000000) (17222099244 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 305 12 (3834524966174283 / 4000000000000)) (orderedInterval (-24294379525 / 1000000000000) (-24294379397 / 1000000000000), orderedInterval (-8582415003 / 1000000000000) (-8582414875 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 225 12 (2824493734832097 / 4000000000000)) (orderedInterval (-1509912349 / 1000000000000) (-1509912348 / 1000000000000), orderedInterval (-29987103284 / 1000000000000) (-29987103283 / 1000000000000))) = true
  rfl'

theorem compactCertificate613_stateChecks3 :
    compactCertificate613.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 345 12 (4333499740394031 / 4000000000000)) (orderedInterval (-7412295664 / 1000000000000) (-7412295663 / 1000000000000), orderedInterval (-23076535284 / 1000000000000) (-23076535283 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 199 12 (2501947241649399 / 4000000000000)) (orderedInterval (-28360470692 / 1000000000000) (-28360470690 / 1000000000000), orderedInterval (-14588365846 / 1000000000000) (-14588365845 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 353 12 (4439749285286691 / 4000000000000)) (orderedInterval (-23605594743 / 1000000000000) (-23605522172 / 1000000000000), orderedInterval (4053025950 / 1000000000000) (4053098521 / 1000000000000))) = true
  rfl'

theorem compactCertificate613_stateChecks4 :
    compactCertificate613.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 330 12 (4148189691444879 / 4000000000000)) (orderedInterval (22160549670 / 1000000000000) (22160549709 / 1000000000000), orderedInterval (11070254067 / 1000000000000) (11070254105 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 236 12 (2960343898940607 / 4000000000000)) (orderedInterval (-15196270971 / 1000000000000) (-15196270796 / 1000000000000), orderedInterval (25095530910 / 1000000000000) (25095531085 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 267 12 (3356714465067753 / 4000000000000)) (orderedInterval (-25236473838 / 1000000000000) (-25236473820 / 1000000000000), orderedInterval (-11018675050 / 1000000000000) (-11018675031 / 1000000000000))) = true
  rfl'

theorem compactCertificate613_stateChecks5 :
    compactCertificate613.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 223 12 (2798478565898457 / 4000000000000)) (orderedInterval (5112394450 / 1000000000000) (5112394451 / 1000000000000), orderedInterval (-29732678221 / 1000000000000) (-29732678219 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 197 12 (2472540682311597 / 4000000000000)) (orderedInterval (-853990979 / 1000000000000) (-853990978 / 1000000000000), orderedInterval (-32080064419 / 1000000000000) (-32080064418 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 285 12 (716638661636103 / 800000000000)) (orderedInterval (-25122433226 / 1000000000000) (-25122433145 / 1000000000000), orderedInterval (-8904293825 / 1000000000000) (-8904293745 / 1000000000000))) = true
  rfl'

theorem compactCertificate613_stateChecks6 :
    compactCertificate613.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 158 12 (1982260252711941 / 4000000000000)) (orderedInterval (-768036455 / 1000000000000) (-768036453 / 1000000000000), orderedInterval (35834346598 / 1000000000000) (35834346599 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 134 12 (1680383969155101 / 4000000000000)) (orderedInterval (-3588863262 / 1000000000000) (-3588863260 / 1000000000000), orderedInterval (38766832348 / 1000000000000) (38766832351 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 84 12 (1051506265167903 / 4000000000000)) (orderedInterval (-11328927426 / 1000000000000) (-11328927361 / 1000000000000), orderedInterval (47911039596 / 1000000000000) (47911039661 / 1000000000000))) = true
  rfl'

theorem compactCertificate613_stateChecks7 :
    compactCertificate613.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (565503566559201 / 4000000000000)) (orderedInterval (-47608106632 / 1000000000000) (-47608106631 / 1000000000000), orderedInterval (-47123246866 / 1000000000000) (-47123246865 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 122 12 (1535452189320603 / 4000000000000)) (orderedInterval (39936600356 / 1000000000000) (39936600370 / 1000000000000), orderedInterval (7918057722 / 1000000000000) (7918057736 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 167 12 (2096528694671931 / 4000000000000)) (orderedInterval (-9341628044 / 1000000000000) (-9341628043 / 1000000000000), orderedInterval (-33567141171 / 1000000000000) (-33567141170 / 1000000000000))) = true
  rfl'

theorem compactCertificate613_stateChecks8 :
    compactCertificate613.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (886493734832097 / 4000000000000)) (orderedInterval (32213658354 / 1000000000000) (32213669823 / 1000000000000), orderedInterval (-42907375678 / 1000000000000) (-42907364208 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 287 12 (3603547815431937 / 4000000000000)) (orderedInterval (-933449835 / 1000000000000) (-933449834 / 1000000000000), orderedInterval (-26566146514 / 1000000000000) (-26566146513 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 192 12 (2407002937659183 / 4000000000000)) (orderedInterval (-19680834591 / 1000000000000) (-19680833030 / 1000000000000), orderedInterval (25912507501 / 1000000000000) (25912509062 / 1000000000000))) = true
  rfl'

theorem compactCertificate613_states : ∀ j,
    BesselStateValid (compactCertificate613.point j) (compactCertificate613.state j) :=
  compactCertificate613.statesValid_of_checks3 compactCertificate613_stateChecks0
    compactCertificate613_stateChecks1 compactCertificate613_stateChecks2
    compactCertificate613_stateChecks3 compactCertificate613_stateChecks4
    compactCertificate613_stateChecks5 compactCertificate613_stateChecks6
    compactCertificate613_stateChecks7 compactCertificate613_stateChecks8

theorem compactCertificate613_chunkChecks0_0 :
    compactCertificate613.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (969 / 2) 0 (IntervalRat.scale (969 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (36099014767 / 1000000000000) (36099014912 / 1000000000000), orderedInterval (3254119310 / 1000000000000) (3254119455 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1427522028516069 / 4000000000000) 0 (IntervalRat.scale (969 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-19353784409 / 1000000000000) (-19353783540 / 1000000000000), orderedInterval (37567463690 / 1000000000000) (37567464559 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (461631293731077 / 800000000000) 0 (IntervalRat.scale (969 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-7531881458 / 1000000000000) (-7531881452 / 1000000000000), orderedInterval (32356541785 / 1000000000000) (32356541790 / 1000000000000)))) (orderedInterval (13686066604 / 1000000000000) (13686066704 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (416547367630383 / 4000000000000) 0 (IntervalRat.scale (969 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-74160893298 / 1000000000000) (-74160893297 / 1000000000000), orderedInterval (-24410963466 / 1000000000000) (-24410963465 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (1118904821689251 / 4000000000000) 0 (IntervalRat.scale (969 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-37646811849 / 1000000000000) (-37646811848 / 1000000000000), orderedInterval (-29234314380 / 1000000000000) (-29234314379 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (3038044248871767 / 4000000000000) 0 (IntervalRat.scale (969 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (893699894 / 1000000000000) (893699895 / 1000000000000), orderedInterval (28937247134 / 1000000000000) (28937247135 / 1000000000000)))) (orderedInterval (-633490554 / 1000000000000) (-633490495 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (2237809643379471 / 4000000000000) 0 (IntervalRat.scale (969 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (28990338264 / 1000000000000) (28990338265 / 1000000000000), orderedInterval (17222099243 / 1000000000000) (17222099244 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3834524966174283 / 4000000000000) 0 (IntervalRat.scale (969 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-24294379525 / 1000000000000) (-24294379397 / 1000000000000), orderedInterval (-8582415003 / 1000000000000) (-8582414875 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2824493734832097 / 4000000000000) 0 (IntervalRat.scale (969 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-1509912349 / 1000000000000) (-1509912348 / 1000000000000), orderedInterval (-29987103284 / 1000000000000) (-29987103283 / 1000000000000)))) (orderedInterval (712844246 / 1000000000000) (712844278 / 1000000000000))) = true
  rfl'

theorem compactCertificate613_chunkChecks0_1 :
    compactCertificate613.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (4333499740394031 / 4000000000000) 0 (IntervalRat.scale (969 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-7412295664 / 1000000000000) (-7412295663 / 1000000000000), orderedInterval (-23076535284 / 1000000000000) (-23076535283 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2501947241649399 / 4000000000000) 0 (IntervalRat.scale (969 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-28360470692 / 1000000000000) (-28360470690 / 1000000000000), orderedInterval (-14588365846 / 1000000000000) (-14588365845 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (4439749285286691 / 4000000000000) 0 (IntervalRat.scale (969 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-23605594743 / 1000000000000) (-23605522172 / 1000000000000), orderedInterval (4053025950 / 1000000000000) (4053098521 / 1000000000000)))) (orderedInterval (-4139876530 / 1000000000000) (-4139866021 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (4148189691444879 / 4000000000000) 0 (IntervalRat.scale (969 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (22160549670 / 1000000000000) (22160549709 / 1000000000000), orderedInterval (11070254067 / 1000000000000) (11070254105 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2960343898940607 / 4000000000000) 0 (IntervalRat.scale (969 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-15196270971 / 1000000000000) (-15196270796 / 1000000000000), orderedInterval (25095530910 / 1000000000000) (25095531085 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (3356714465067753 / 4000000000000) 0 (IntervalRat.scale (969 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-25236473838 / 1000000000000) (-25236473820 / 1000000000000), orderedInterval (-11018675050 / 1000000000000) (-11018675031 / 1000000000000)))) (orderedInterval (-1709358181 / 1000000000000) (-1709358105 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2798478565898457 / 4000000000000) 0 (IntervalRat.scale (969 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (5112394450 / 1000000000000) (5112394451 / 1000000000000), orderedInterval (-29732678221 / 1000000000000) (-29732678219 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2472540682311597 / 4000000000000) 0 (IntervalRat.scale (969 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-853990979 / 1000000000000) (-853990978 / 1000000000000), orderedInterval (-32080064419 / 1000000000000) (-32080064418 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (716638661636103 / 800000000000) 0 (IntervalRat.scale (969 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-25122433226 / 1000000000000) (-25122433145 / 1000000000000), orderedInterval (-8904293825 / 1000000000000) (-8904293745 / 1000000000000)))) (orderedInterval (-535326238 / 1000000000000) (-535326189 / 1000000000000))) = true
  rfl'

theorem compactCertificate613_chunkChecks0_2 :
    compactCertificate613.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1982260252711941 / 4000000000000) 0 (IntervalRat.scale (969 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-768036455 / 1000000000000) (-768036453 / 1000000000000), orderedInterval (35834346598 / 1000000000000) (35834346599 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1680383969155101 / 4000000000000) 0 (IntervalRat.scale (969 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-3588863262 / 1000000000000) (-3588863260 / 1000000000000), orderedInterval (38766832348 / 1000000000000) (38766832351 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (1051506265167903 / 4000000000000) 0 (IntervalRat.scale (969 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-11328927426 / 1000000000000) (-11328927361 / 1000000000000), orderedInterval (47911039596 / 1000000000000) (47911039661 / 1000000000000)))) (orderedInterval (-42883637 / 1000000000000) (-42883512 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (565503566559201 / 4000000000000) 0 (IntervalRat.scale (969 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-47608106632 / 1000000000000) (-47608106631 / 1000000000000), orderedInterval (-47123246866 / 1000000000000) (-47123246865 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1535452189320603 / 4000000000000) 0 (IntervalRat.scale (969 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (39936600356 / 1000000000000) (39936600370 / 1000000000000), orderedInterval (7918057722 / 1000000000000) (7918057736 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (2096528694671931 / 4000000000000) 0 (IntervalRat.scale (969 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-9341628044 / 1000000000000) (-9341628043 / 1000000000000), orderedInterval (-33567141171 / 1000000000000) (-33567141170 / 1000000000000)))) (orderedInterval (688984906 / 1000000000000) (688984964 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (886493734832097 / 4000000000000) 0 (IntervalRat.scale (969 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (32213658354 / 1000000000000) (32213669823 / 1000000000000), orderedInterval (-42907375678 / 1000000000000) (-42907364208 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3603547815431937 / 4000000000000) 0 (IntervalRat.scale (969 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-933449835 / 1000000000000) (-933449834 / 1000000000000), orderedInterval (-26566146514 / 1000000000000) (-26566146513 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2407002937659183 / 4000000000000) 0 (IntervalRat.scale (969 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-19680834591 / 1000000000000) (-19680833030 / 1000000000000), orderedInterval (25912507501 / 1000000000000) (25912509062 / 1000000000000)))) (orderedInterval (3962825257 / 1000000000000) (3962825753 / 1000000000000))) = true
  rfl'

theorem compactCertificate613_chunkChecks0 :
    compactCertificate613.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate613.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate613_chunkChecks0_0
    compactCertificate613_chunkChecks0_1 compactCertificate613_chunkChecks0_2

theorem compactCertificate613_chunkChecks1_0 :
    compactCertificate613.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (969 / 2) 1 (IntervalRat.scale (969 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (36099014767 / 1000000000000) (36099014912 / 1000000000000), orderedInterval (3254119310 / 1000000000000) (3254119455 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1427522028516069 / 4000000000000) 1 (IntervalRat.scale (969 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-19353784409 / 1000000000000) (-19353783540 / 1000000000000), orderedInterval (37567463690 / 1000000000000) (37567464559 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (461631293731077 / 800000000000) 1 (IntervalRat.scale (969 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-7531881458 / 1000000000000) (-7531881452 / 1000000000000), orderedInterval (32356541785 / 1000000000000) (32356541790 / 1000000000000)))) (orderedInterval (3809041077 / 1000000000000) (3809041179 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (416547367630383 / 4000000000000) 1 (IntervalRat.scale (969 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-74160893298 / 1000000000000) (-74160893297 / 1000000000000), orderedInterval (-24410963466 / 1000000000000) (-24410963465 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (1118904821689251 / 4000000000000) 1 (IntervalRat.scale (969 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-37646811849 / 1000000000000) (-37646811848 / 1000000000000), orderedInterval (-29234314380 / 1000000000000) (-29234314379 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (3038044248871767 / 4000000000000) 1 (IntervalRat.scale (969 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (893699894 / 1000000000000) (893699895 / 1000000000000), orderedInterval (28937247134 / 1000000000000) (28937247135 / 1000000000000)))) (orderedInterval (-3784145083 / 1000000000000) (-3784145016 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (2237809643379471 / 4000000000000) 1 (IntervalRat.scale (969 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (28990338264 / 1000000000000) (28990338265 / 1000000000000), orderedInterval (17222099243 / 1000000000000) (17222099244 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3834524966174283 / 4000000000000) 1 (IntervalRat.scale (969 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-24294379525 / 1000000000000) (-24294379397 / 1000000000000), orderedInterval (-8582415003 / 1000000000000) (-8582414875 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2824493734832097 / 4000000000000) 1 (IntervalRat.scale (969 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-1509912349 / 1000000000000) (-1509912348 / 1000000000000), orderedInterval (-29987103284 / 1000000000000) (-29987103283 / 1000000000000)))) (orderedInterval (-532473039 / 1000000000000) (-532472983 / 1000000000000))) = true
  rfl'

theorem compactCertificate613_chunkChecks1_1 :
    compactCertificate613.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (4333499740394031 / 4000000000000) 1 (IntervalRat.scale (969 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-7412295664 / 1000000000000) (-7412295663 / 1000000000000), orderedInterval (-23076535284 / 1000000000000) (-23076535283 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2501947241649399 / 4000000000000) 1 (IntervalRat.scale (969 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-28360470692 / 1000000000000) (-28360470690 / 1000000000000), orderedInterval (-14588365846 / 1000000000000) (-14588365845 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (4439749285286691 / 4000000000000) 1 (IntervalRat.scale (969 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-23605594743 / 1000000000000) (-23605522172 / 1000000000000), orderedInterval (4053025950 / 1000000000000) (4053098521 / 1000000000000)))) (orderedInterval (9093338116 / 1000000000000) (9093362148 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (4148189691444879 / 4000000000000) 1 (IntervalRat.scale (969 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (22160549670 / 1000000000000) (22160549709 / 1000000000000), orderedInterval (11070254067 / 1000000000000) (11070254105 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2960343898940607 / 4000000000000) 1 (IntervalRat.scale (969 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-15196270971 / 1000000000000) (-15196270796 / 1000000000000), orderedInterval (25095530910 / 1000000000000) (25095531085 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (3356714465067753 / 4000000000000) 1 (IntervalRat.scale (969 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-25236473838 / 1000000000000) (-25236473820 / 1000000000000), orderedInterval (-11018675050 / 1000000000000) (-11018675031 / 1000000000000)))) (orderedInterval (3293785330 / 1000000000000) (3293785451 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2798478565898457 / 4000000000000) 1 (IntervalRat.scale (969 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (5112394450 / 1000000000000) (5112394451 / 1000000000000), orderedInterval (-29732678221 / 1000000000000) (-29732678219 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2472540682311597 / 4000000000000) 1 (IntervalRat.scale (969 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-853990979 / 1000000000000) (-853990978 / 1000000000000), orderedInterval (-32080064419 / 1000000000000) (-32080064418 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (716638661636103 / 800000000000) 1 (IntervalRat.scale (969 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-25122433226 / 1000000000000) (-25122433145 / 1000000000000), orderedInterval (-8904293825 / 1000000000000) (-8904293745 / 1000000000000)))) (orderedInterval (1424883762 / 1000000000000) (1424883833 / 1000000000000))) = true
  rfl'

theorem compactCertificate613_chunkChecks1_2 :
    compactCertificate613.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1982260252711941 / 4000000000000) 1 (IntervalRat.scale (969 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-768036455 / 1000000000000) (-768036453 / 1000000000000), orderedInterval (35834346598 / 1000000000000) (35834346599 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1680383969155101 / 4000000000000) 1 (IntervalRat.scale (969 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-3588863262 / 1000000000000) (-3588863260 / 1000000000000), orderedInterval (38766832348 / 1000000000000) (38766832351 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (1051506265167903 / 4000000000000) 1 (IntervalRat.scale (969 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-11328927426 / 1000000000000) (-11328927361 / 1000000000000), orderedInterval (47911039596 / 1000000000000) (47911039661 / 1000000000000)))) (orderedInterval (-6916742084 / 1000000000000) (-6916741970 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (565503566559201 / 4000000000000) 1 (IntervalRat.scale (969 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-47608106632 / 1000000000000) (-47608106631 / 1000000000000), orderedInterval (-47123246866 / 1000000000000) (-47123246865 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1535452189320603 / 4000000000000) 1 (IntervalRat.scale (969 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (39936600356 / 1000000000000) (39936600370 / 1000000000000), orderedInterval (7918057722 / 1000000000000) (7918057736 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (2096528694671931 / 4000000000000) 1 (IntervalRat.scale (969 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-9341628044 / 1000000000000) (-9341628043 / 1000000000000), orderedInterval (-33567141171 / 1000000000000) (-33567141170 / 1000000000000)))) (orderedInterval (2894562960 / 1000000000000) (2894563013 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (886493734832097 / 4000000000000) 1 (IntervalRat.scale (969 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (32213658354 / 1000000000000) (32213669823 / 1000000000000), orderedInterval (-42907375678 / 1000000000000) (-42907364208 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3603547815431937 / 4000000000000) 1 (IntervalRat.scale (969 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-933449835 / 1000000000000) (-933449834 / 1000000000000), orderedInterval (-26566146514 / 1000000000000) (-26566146513 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2407002937659183 / 4000000000000) 1 (IntervalRat.scale (969 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-19680834591 / 1000000000000) (-19680833030 / 1000000000000), orderedInterval (25912507501 / 1000000000000) (25912509062 / 1000000000000)))) (orderedInterval (-2135737785 / 1000000000000) (-2135737200 / 1000000000000))) = true
  rfl'

theorem compactCertificate613_chunkChecks1 :
    compactCertificate613.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate613.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate613_chunkChecks1_0
    compactCertificate613_chunkChecks1_1 compactCertificate613_chunkChecks1_2

theorem compactCertificate613_chunkChecks2_0 :
    compactCertificate613.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (969 / 2) 2 (IntervalRat.scale (969 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (36099014767 / 1000000000000) (36099014912 / 1000000000000), orderedInterval (3254119310 / 1000000000000) (3254119455 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1427522028516069 / 4000000000000) 2 (IntervalRat.scale (969 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-19353784409 / 1000000000000) (-19353783540 / 1000000000000), orderedInterval (37567463690 / 1000000000000) (37567464559 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (461631293731077 / 800000000000) 2 (IntervalRat.scale (969 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-7531881458 / 1000000000000) (-7531881452 / 1000000000000), orderedInterval (32356541785 / 1000000000000) (32356541790 / 1000000000000)))) (orderedInterval (-13591461636 / 1000000000000) (-13591461530 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (416547367630383 / 4000000000000) 2 (IntervalRat.scale (969 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-74160893298 / 1000000000000) (-74160893297 / 1000000000000), orderedInterval (-24410963466 / 1000000000000) (-24410963465 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (1118904821689251 / 4000000000000) 2 (IntervalRat.scale (969 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-37646811849 / 1000000000000) (-37646811848 / 1000000000000), orderedInterval (-29234314380 / 1000000000000) (-29234314379 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (3038044248871767 / 4000000000000) 2 (IntervalRat.scale (969 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (893699894 / 1000000000000) (893699895 / 1000000000000), orderedInterval (28937247134 / 1000000000000) (28937247135 / 1000000000000)))) (orderedInterval (584950787 / 1000000000000) (584950879 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (2237809643379471 / 4000000000000) 2 (IntervalRat.scale (969 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (28990338264 / 1000000000000) (28990338265 / 1000000000000), orderedInterval (17222099243 / 1000000000000) (17222099244 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3834524966174283 / 4000000000000) 2 (IntervalRat.scale (969 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-24294379525 / 1000000000000) (-24294379397 / 1000000000000), orderedInterval (-8582415003 / 1000000000000) (-8582414875 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2824493734832097 / 4000000000000) 2 (IntervalRat.scale (969 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-1509912349 / 1000000000000) (-1509912348 / 1000000000000), orderedInterval (-29987103284 / 1000000000000) (-29987103283 / 1000000000000)))) (orderedInterval (-2854930116 / 1000000000000) (-2854930017 / 1000000000000))) = true
  rfl'

theorem compactCertificate613_chunkChecks2_1 :
    compactCertificate613.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (4333499740394031 / 4000000000000) 2 (IntervalRat.scale (969 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-7412295664 / 1000000000000) (-7412295663 / 1000000000000), orderedInterval (-23076535284 / 1000000000000) (-23076535283 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2501947241649399 / 4000000000000) 2 (IntervalRat.scale (969 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-28360470692 / 1000000000000) (-28360470690 / 1000000000000), orderedInterval (-14588365846 / 1000000000000) (-14588365845 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (4439749285286691 / 4000000000000) 2 (IntervalRat.scale (969 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-23605594743 / 1000000000000) (-23605522172 / 1000000000000), orderedInterval (4053025950 / 1000000000000) (4053098521 / 1000000000000)))) (orderedInterval (14509137314 / 1000000000000) (14509192359 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (4148189691444879 / 4000000000000) 2 (IntervalRat.scale (969 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (22160549670 / 1000000000000) (22160549709 / 1000000000000), orderedInterval (11070254067 / 1000000000000) (11070254105 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2960343898940607 / 4000000000000) 2 (IntervalRat.scale (969 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-15196270971 / 1000000000000) (-15196270796 / 1000000000000), orderedInterval (25095530910 / 1000000000000) (25095531085 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (3356714465067753 / 4000000000000) 2 (IntervalRat.scale (969 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-25236473838 / 1000000000000) (-25236473820 / 1000000000000), orderedInterval (-11018675050 / 1000000000000) (-11018675031 / 1000000000000)))) (orderedInterval (4795987282 / 1000000000000) (4795987480 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2798478565898457 / 4000000000000) 2 (IntervalRat.scale (969 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (5112394450 / 1000000000000) (5112394451 / 1000000000000), orderedInterval (-29732678221 / 1000000000000) (-29732678219 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2472540682311597 / 4000000000000) 2 (IntervalRat.scale (969 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-853990979 / 1000000000000) (-853990978 / 1000000000000), orderedInterval (-32080064419 / 1000000000000) (-32080064418 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (716638661636103 / 800000000000) 2 (IntervalRat.scale (969 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-25122433226 / 1000000000000) (-25122433145 / 1000000000000), orderedInterval (-8904293825 / 1000000000000) (-8904293745 / 1000000000000)))) (orderedInterval (1993291854 / 1000000000000) (1993291962 / 1000000000000))) = true
  rfl'

theorem compactCertificate613_chunkChecks2_2 :
    compactCertificate613.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1982260252711941 / 4000000000000) 2 (IntervalRat.scale (969 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-768036455 / 1000000000000) (-768036453 / 1000000000000), orderedInterval (35834346598 / 1000000000000) (35834346599 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1680383969155101 / 4000000000000) 2 (IntervalRat.scale (969 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-3588863262 / 1000000000000) (-3588863260 / 1000000000000), orderedInterval (38766832348 / 1000000000000) (38766832351 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (1051506265167903 / 4000000000000) 2 (IntervalRat.scale (969 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-11328927426 / 1000000000000) (-11328927361 / 1000000000000), orderedInterval (47911039596 / 1000000000000) (47911039661 / 1000000000000)))) (orderedInterval (-158341651 / 1000000000000) (-158341543 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (565503566559201 / 4000000000000) 2 (IntervalRat.scale (969 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-47608106632 / 1000000000000) (-47608106631 / 1000000000000), orderedInterval (-47123246866 / 1000000000000) (-47123246865 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1535452189320603 / 4000000000000) 2 (IntervalRat.scale (969 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (39936600356 / 1000000000000) (39936600370 / 1000000000000), orderedInterval (7918057722 / 1000000000000) (7918057736 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (2096528694671931 / 4000000000000) 2 (IntervalRat.scale (969 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-9341628044 / 1000000000000) (-9341628043 / 1000000000000), orderedInterval (-33567141171 / 1000000000000) (-33567141170 / 1000000000000)))) (orderedInterval (-349938263 / 1000000000000) (-349938211 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (886493734832097 / 4000000000000) 2 (IntervalRat.scale (969 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (32213658354 / 1000000000000) (32213669823 / 1000000000000), orderedInterval (-42907375678 / 1000000000000) (-42907364208 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3603547815431937 / 4000000000000) 2 (IntervalRat.scale (969 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-933449835 / 1000000000000) (-933449834 / 1000000000000), orderedInterval (-26566146514 / 1000000000000) (-26566146513 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2407002937659183 / 4000000000000) 2 (IntervalRat.scale (969 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-19680834591 / 1000000000000) (-19680833030 / 1000000000000), orderedInterval (25912507501 / 1000000000000) (25912509062 / 1000000000000)))) (orderedInterval (-5995112595 / 1000000000000) (-5995111849 / 1000000000000))) = true
  rfl'

theorem compactCertificate613_chunkChecks2 :
    compactCertificate613.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate613.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate613_chunkChecks2_0
    compactCertificate613_chunkChecks2_1 compactCertificate613_chunkChecks2_2

theorem compactCertificate613_chunkChecks3_0 :
    compactCertificate613.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (969 / 2) 3 (IntervalRat.scale (969 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (36099014767 / 1000000000000) (36099014912 / 1000000000000), orderedInterval (3254119310 / 1000000000000) (3254119455 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1427522028516069 / 4000000000000) 3 (IntervalRat.scale (969 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-19353784409 / 1000000000000) (-19353783540 / 1000000000000), orderedInterval (37567463690 / 1000000000000) (37567464559 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (461631293731077 / 800000000000) 3 (IntervalRat.scale (969 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-7531881458 / 1000000000000) (-7531881452 / 1000000000000), orderedInterval (32356541785 / 1000000000000) (32356541790 / 1000000000000)))) (orderedInterval (-4609362203 / 1000000000000) (-4609362091 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (416547367630383 / 4000000000000) 3 (IntervalRat.scale (969 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-74160893298 / 1000000000000) (-74160893297 / 1000000000000), orderedInterval (-24410963466 / 1000000000000) (-24410963465 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (1118904821689251 / 4000000000000) 3 (IntervalRat.scale (969 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-37646811849 / 1000000000000) (-37646811848 / 1000000000000), orderedInterval (-29234314380 / 1000000000000) (-29234314379 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (3038044248871767 / 4000000000000) 3 (IntervalRat.scale (969 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (893699894 / 1000000000000) (893699895 / 1000000000000), orderedInterval (28937247134 / 1000000000000) (28937247135 / 1000000000000)))) (orderedInterval (8126297629 / 1000000000000) (8126297767 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (2237809643379471 / 4000000000000) 3 (IntervalRat.scale (969 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (28990338264 / 1000000000000) (28990338265 / 1000000000000), orderedInterval (17222099243 / 1000000000000) (17222099244 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3834524966174283 / 4000000000000) 3 (IntervalRat.scale (969 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-24294379525 / 1000000000000) (-24294379397 / 1000000000000), orderedInterval (-8582415003 / 1000000000000) (-8582414875 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2824493734832097 / 4000000000000) 3 (IntervalRat.scale (969 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-1509912349 / 1000000000000) (-1509912348 / 1000000000000), orderedInterval (-29987103284 / 1000000000000) (-29987103283 / 1000000000000)))) (orderedInterval (198971809 / 1000000000000) (198971993 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate613_chunkChecks3_1 :
    compactCertificate613.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (4333499740394031 / 4000000000000) 3 (IntervalRat.scale (969 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-7412295664 / 1000000000000) (-7412295663 / 1000000000000), orderedInterval (-23076535284 / 1000000000000) (-23076535283 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2501947241649399 / 4000000000000) 3 (IntervalRat.scale (969 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-28360470692 / 1000000000000) (-28360470690 / 1000000000000), orderedInterval (-14588365846 / 1000000000000) (-14588365845 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (4439749285286691 / 4000000000000) 3 (IntervalRat.scale (969 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-23605594743 / 1000000000000) (-23605522172 / 1000000000000), orderedInterval (4053025950 / 1000000000000) (4053098521 / 1000000000000)))) (orderedInterval (-50475670969 / 1000000000000) (-50475544952 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (4148189691444879 / 4000000000000) 3 (IntervalRat.scale (969 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (22160549670 / 1000000000000) (22160549709 / 1000000000000), orderedInterval (11070254067 / 1000000000000) (11070254105 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2960343898940607 / 4000000000000) 3 (IntervalRat.scale (969 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-15196270971 / 1000000000000) (-15196270796 / 1000000000000), orderedInterval (25095530910 / 1000000000000) (25095531085 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (3356714465067753 / 4000000000000) 3 (IntervalRat.scale (969 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-25236473838 / 1000000000000) (-25236473820 / 1000000000000), orderedInterval (-11018675050 / 1000000000000) (-11018675031 / 1000000000000)))) (orderedInterval (-6798056239 / 1000000000000) (-6798055910 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2798478565898457 / 4000000000000) 3 (IntervalRat.scale (969 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (5112394450 / 1000000000000) (5112394451 / 1000000000000), orderedInterval (-29732678221 / 1000000000000) (-29732678219 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2472540682311597 / 4000000000000) 3 (IntervalRat.scale (969 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-853990979 / 1000000000000) (-853990978 / 1000000000000), orderedInterval (-32080064419 / 1000000000000) (-32080064418 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (716638661636103 / 800000000000) 3 (IntervalRat.scale (969 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-25122433226 / 1000000000000) (-25122433145 / 1000000000000), orderedInterval (-8904293825 / 1000000000000) (-8904293745 / 1000000000000)))) (orderedInterval (-1341781357 / 1000000000000) (-1341781190 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate613_chunkChecks3_2 :
    compactCertificate613.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1982260252711941 / 4000000000000) 3 (IntervalRat.scale (969 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-768036455 / 1000000000000) (-768036453 / 1000000000000), orderedInterval (35834346598 / 1000000000000) (35834346599 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1680383969155101 / 4000000000000) 3 (IntervalRat.scale (969 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-3588863262 / 1000000000000) (-3588863260 / 1000000000000), orderedInterval (38766832348 / 1000000000000) (38766832351 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (1051506265167903 / 4000000000000) 3 (IntervalRat.scale (969 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-11328927426 / 1000000000000) (-11328927361 / 1000000000000), orderedInterval (47911039596 / 1000000000000) (47911039661 / 1000000000000)))) (orderedInterval (7312746245 / 1000000000000) (7312746350 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (565503566559201 / 4000000000000) 3 (IntervalRat.scale (969 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-47608106632 / 1000000000000) (-47608106631 / 1000000000000), orderedInterval (-47123246866 / 1000000000000) (-47123246865 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1535452189320603 / 4000000000000) 3 (IntervalRat.scale (969 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (39936600356 / 1000000000000) (39936600370 / 1000000000000), orderedInterval (7918057722 / 1000000000000) (7918057736 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (2096528694671931 / 4000000000000) 3 (IntervalRat.scale (969 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-9341628044 / 1000000000000) (-9341628043 / 1000000000000), orderedInterval (-33567141171 / 1000000000000) (-33567141170 / 1000000000000)))) (orderedInterval (-3188446371 / 1000000000000) (-3188446317 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (886493734832097 / 4000000000000) 3 (IntervalRat.scale (969 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (32213658354 / 1000000000000) (32213669823 / 1000000000000), orderedInterval (-42907375678 / 1000000000000) (-42907364208 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3603547815431937 / 4000000000000) 3 (IntervalRat.scale (969 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-933449835 / 1000000000000) (-933449834 / 1000000000000), orderedInterval (-26566146514 / 1000000000000) (-26566146513 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2407002937659183 / 4000000000000) 3 (IntervalRat.scale (969 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-19680834591 / 1000000000000) (-19680833030 / 1000000000000), orderedInterval (25912507501 / 1000000000000) (25912509062 / 1000000000000)))) (orderedInterval (-4550577840 / 1000000000000) (-4550576841 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate613_chunkChecks3 :
    compactCertificate613.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate613.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate613_chunkChecks3_0
    compactCertificate613_chunkChecks3_1 compactCertificate613_chunkChecks3_2

theorem compactCertificate613_chunkChecks4_0 :
    compactCertificate613.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (969 / 2) 4 (IntervalRat.scale (969 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (36099014767 / 1000000000000) (36099014912 / 1000000000000), orderedInterval (3254119310 / 1000000000000) (3254119455 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1427522028516069 / 4000000000000) 4 (IntervalRat.scale (969 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-19353784409 / 1000000000000) (-19353783540 / 1000000000000), orderedInterval (37567463690 / 1000000000000) (37567464559 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (461631293731077 / 800000000000) 4 (IntervalRat.scale (969 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-7531881458 / 1000000000000) (-7531881452 / 1000000000000), orderedInterval (32356541785 / 1000000000000) (32356541790 / 1000000000000)))) (orderedInterval (13384966474 / 1000000000000) (13384966594 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (416547367630383 / 4000000000000) 4 (IntervalRat.scale (969 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-74160893298 / 1000000000000) (-74160893297 / 1000000000000), orderedInterval (-24410963466 / 1000000000000) (-24410963465 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (1118904821689251 / 4000000000000) 4 (IntervalRat.scale (969 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-37646811849 / 1000000000000) (-37646811848 / 1000000000000), orderedInterval (-29234314380 / 1000000000000) (-29234314379 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (3038044248871767 / 4000000000000) 4 (IntervalRat.scale (969 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (893699894 / 1000000000000) (893699895 / 1000000000000), orderedInterval (28937247134 / 1000000000000) (28937247135 / 1000000000000)))) (orderedInterval (-568224651 / 1000000000000) (-568224439 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (2237809643379471 / 4000000000000) 4 (IntervalRat.scale (969 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (28990338264 / 1000000000000) (28990338265 / 1000000000000), orderedInterval (17222099243 / 1000000000000) (17222099244 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3834524966174283 / 4000000000000) 4 (IntervalRat.scale (969 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-24294379525 / 1000000000000) (-24294379397 / 1000000000000), orderedInterval (-8582415003 / 1000000000000) (-8582414875 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2824493734832097 / 4000000000000) 4 (IntervalRat.scale (969 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-1509912349 / 1000000000000) (-1509912348 / 1000000000000), orderedInterval (-29987103284 / 1000000000000) (-29987103283 / 1000000000000)))) (orderedInterval (11318908494 / 1000000000000) (11318908837 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate613_chunkChecks4_1 :
    compactCertificate613.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (4333499740394031 / 4000000000000) 4 (IntervalRat.scale (969 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-7412295664 / 1000000000000) (-7412295663 / 1000000000000), orderedInterval (-23076535284 / 1000000000000) (-23076535283 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2501947241649399 / 4000000000000) 4 (IntervalRat.scale (969 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-28360470692 / 1000000000000) (-28360470690 / 1000000000000), orderedInterval (-14588365846 / 1000000000000) (-14588365845 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (4439749285286691 / 4000000000000) 4 (IntervalRat.scale (969 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-23605594743 / 1000000000000) (-23605522172 / 1000000000000), orderedInterval (4053025950 / 1000000000000) (4053098521 / 1000000000000)))) (orderedInterval (-65128499901 / 1000000000000) (-65128211085 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (4148189691444879 / 4000000000000) 4 (IntervalRat.scale (969 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (22160549670 / 1000000000000) (22160549709 / 1000000000000), orderedInterval (11070254067 / 1000000000000) (11070254105 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2960343898940607 / 4000000000000) 4 (IntervalRat.scale (969 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-15196270971 / 1000000000000) (-15196270796 / 1000000000000), orderedInterval (25095530910 / 1000000000000) (25095531085 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (3356714465067753 / 4000000000000) 4 (IntervalRat.scale (969 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-25236473838 / 1000000000000) (-25236473820 / 1000000000000), orderedInterval (-11018675050 / 1000000000000) (-11018675031 / 1000000000000)))) (orderedInterval (-15043725781 / 1000000000000) (-15043725219 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2798478565898457 / 4000000000000) 4 (IntervalRat.scale (969 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (5112394450 / 1000000000000) (5112394451 / 1000000000000), orderedInterval (-29732678221 / 1000000000000) (-29732678219 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2472540682311597 / 4000000000000) 4 (IntervalRat.scale (969 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-853990979 / 1000000000000) (-853990978 / 1000000000000), orderedInterval (-32080064419 / 1000000000000) (-32080064418 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (716638661636103 / 800000000000) 4 (IntervalRat.scale (969 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-25122433226 / 1000000000000) (-25122433145 / 1000000000000), orderedInterval (-8904293825 / 1000000000000) (-8904293745 / 1000000000000)))) (orderedInterval (-7125117387 / 1000000000000) (-7125117118 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate613_chunkChecks4_2 :
    compactCertificate613.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1982260252711941 / 4000000000000) 4 (IntervalRat.scale (969 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-768036455 / 1000000000000) (-768036453 / 1000000000000), orderedInterval (35834346598 / 1000000000000) (35834346599 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1680383969155101 / 4000000000000) 4 (IntervalRat.scale (969 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-3588863262 / 1000000000000) (-3588863260 / 1000000000000), orderedInterval (38766832348 / 1000000000000) (38766832351 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (1051506265167903 / 4000000000000) 4 (IntervalRat.scale (969 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-11328927426 / 1000000000000) (-11328927361 / 1000000000000), orderedInterval (47911039596 / 1000000000000) (47911039661 / 1000000000000)))) (orderedInterval (187074979 / 1000000000000) (187075082 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (565503566559201 / 4000000000000) 4 (IntervalRat.scale (969 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-47608106632 / 1000000000000) (-47608106631 / 1000000000000), orderedInterval (-47123246866 / 1000000000000) (-47123246865 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1535452189320603 / 4000000000000) 4 (IntervalRat.scale (969 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (39936600356 / 1000000000000) (39936600370 / 1000000000000), orderedInterval (7918057722 / 1000000000000) (7918057736 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (2096528694671931 / 4000000000000) 4 (IntervalRat.scale (969 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-9341628044 / 1000000000000) (-9341628043 / 1000000000000), orderedInterval (-33567141171 / 1000000000000) (-33567141170 / 1000000000000)))) (orderedInterval (643054979 / 1000000000000) (643055035 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (886493734832097 / 4000000000000) 4 (IntervalRat.scale (969 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (32213658354 / 1000000000000) (32213669823 / 1000000000000), orderedInterval (-42907375678 / 1000000000000) (-42907364208 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3603547815431937 / 4000000000000) 4 (IntervalRat.scale (969 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-933449835 / 1000000000000) (-933449834 / 1000000000000), orderedInterval (-26566146514 / 1000000000000) (-26566146513 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2407002937659183 / 4000000000000) 4 (IntervalRat.scale (969 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-19680834591 / 1000000000000) (-19680833030 / 1000000000000), orderedInterval (25912507501 / 1000000000000) (25912509062 / 1000000000000)))) (orderedInterval (9722331155 / 1000000000000) (9722332547 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate613_chunkChecks4 :
    compactCertificate613.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate613.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate613_chunkChecks4_0
    compactCertificate613_chunkChecks4_1 compactCertificate613_chunkChecks4_2

theorem compactCertificate613_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate613.chunkCheck r b = true :=
  compactCertificate613.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate613_chunkChecks0
    · exact compactCertificate613_chunkChecks1
    · exact compactCertificate613_chunkChecks2
    · exact compactCertificate613_chunkChecks3
    · exact compactCertificate613_chunkChecks4)

theorem compactCertificate613_coefficient0 :
    compactCertificate613.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate613_coefficient1 :
    compactCertificate613.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate613_coefficient2 :
    compactCertificate613.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate613_coefficient3 :
    compactCertificate613.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate613_coefficient4 :
    compactCertificate613.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate613_coefficients : ∀ r : Fin 5,
    compactCertificate613.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate613_coefficient0
  · exact compactCertificate613_coefficient1
  · exact compactCertificate613_coefficient2
  · exact compactCertificate613_coefficient3
  · exact compactCertificate613_coefficient4

theorem compactCertificate613_lower : (1 : ℚ) ≤ compactCertificate613.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate613, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate613_proves {t : ℝ} (ht : t ∈ compactCertificate613.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate613.proves compactCertificate613_states compactCertificate613_chunks
    compactCertificate613_coefficients compactCertificate613_lower ht

end Erdos232
