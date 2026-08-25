/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate579 : CompactCertificate where
  left := 450
  right := 451
  center := 901 / 2
  grid := fun i =>
    match i.val with
    | 0 => 143
    | 1 => 106
    | 2 => 171
    | 3 => 31
    | 4 => 83
    | 5 => 225
    | 6 => 166
    | 7 => 284
    | 8 => 209
    | 9 => 321
    | 10 => 185
    | 11 => 329
    | 12 => 307
    | 13 => 219
    | 14 => 248
    | 15 => 207
    | 16 => 183
    | 17 => 265
    | 18 => 147
    | 19 => 124
    | 20 => 78
    | 21 => 42
    | 22 => 114
    | 23 => 155
    | 24 => 66
    | 25 => 267
    | _ => 178
  point := fun i =>
    match i.val with
    | 0 => 901 / 2
    | 1 => 1327345044058801 / 4000000000000
    | 2 => 429236115223633 / 800000000000
    | 3 => 387315973410707 / 4000000000000
    | 4 => 1040385185079479 / 4000000000000
    | 5 => 2824848161231643 / 4000000000000
    | 6 => 2080770370159859 / 4000000000000
    | 7 => 3565435494863807 / 4000000000000
    | 8 => 2626283648177213 / 4000000000000
    | 9 => 4029394495454099 / 4000000000000
    | 10 => 2326371996621371 / 4000000000000
    | 11 => 4128187931933239 / 4000000000000
    | 12 => 3857088660466291 / 4000000000000
    | 13 => 2752600467436003 / 4000000000000
    | 14 => 3121155555238437 / 4000000000000
    | 15 => 2602094105133653 / 4000000000000
    | 16 => 2299029055482713 / 4000000000000
    | 17 => 666348229240587 / 800000000000
    | 18 => 1843154270065489 / 4000000000000
    | 19 => 1562462287109129 / 4000000000000
    | 20 => 977716351822787 / 4000000000000
    | 21 => 525819105748029 / 4000000000000
    | 22 => 1427701158491087 / 4000000000000
    | 23 => 1949403873993199 / 4000000000000
    | 24 => 824283648177213 / 4000000000000
    | 25 => 3350667266980573 / 4000000000000
    | _ => 2238090450805907 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-33573751442 / 1000000000000) (-33573698942 / 1000000000000), orderedInterval (16947139914 / 1000000000000) (16947192414 / 1000000000000))
    | 1 => (orderedInterval (-16552640605 / 1000000000000) (-16552640267 / 1000000000000), orderedInterval (40577218825 / 1000000000000) (40577219163 / 1000000000000))
    | 2 => (orderedInterval (-4054002002 / 1000000000000) (-4054002001 / 1000000000000), orderedInterval (-34202687397 / 1000000000000) (-34202687396 / 1000000000000))
    | 3 => (orderedInterval (-17989804154 / 1000000000000) (-17989804153 / 1000000000000), orderedInterval (-78971178379 / 1000000000000) (-78971178378 / 1000000000000))
    | 4 => (orderedInterval (-6365552413 / 1000000000000) (-6365552412 / 1000000000000), orderedInterval (-49050123159 / 1000000000000) (-49050123158 / 1000000000000))
    | 5 => (orderedInterval (-4157402552 / 1000000000000) (-4157402551 / 1000000000000), orderedInterval (-29732106580 / 1000000000000) (-29732106579 / 1000000000000))
    | 6 => (orderedInterval (-17583290493 / 1000000000000) (-17583289906 / 1000000000000), orderedInterval (30259977549 / 1000000000000) (30259978137 / 1000000000000))
    | 7 => (orderedInterval (-1820735117 / 1000000000000) (-1820735116 / 1000000000000), orderedInterval (26663685721 / 1000000000000) (26663685722 / 1000000000000))
    | 8 => (orderedInterval (-21525411966 / 1000000000000) (-21525411965 / 1000000000000), orderedInterval (-22484047151 / 1000000000000) (-22484047150 / 1000000000000))
    | 9 => (orderedInterval (7844516632 / 1000000000000) (7844516633 / 1000000000000), orderedInterval (-23887763573 / 1000000000000) (-23887763572 / 1000000000000))
    | 10 => (orderedInterval (-30634978483 / 1000000000000) (-30634978480 / 1000000000000), orderedInterval (-12468129246 / 1000000000000) (-12468129242 / 1000000000000))
    | 11 => (orderedInterval (16960803530 / 1000000000000) (16960803911 / 1000000000000), orderedInterval (-18151609536 / 1000000000000) (-18151609155 / 1000000000000))
    | 12 => (orderedInterval (-14263142671 / 1000000000000) (-14263142670 / 1000000000000), orderedInterval (-21364790659 / 1000000000000) (-21364790658 / 1000000000000))
    | 13 => (orderedInterval (-24318844967 / 1000000000000) (-24318844966 / 1000000000000), orderedInterval (-18250096810 / 1000000000000) (-18250096809 / 1000000000000))
    | 14 => (orderedInterval (26436492992 / 1000000000000) (26436605053 / 1000000000000), orderedInterval (-10832988338 / 1000000000000) (-10832876277 / 1000000000000))
    | 15 => (orderedInterval (-26307724570 / 1000000000000) (-26307724569 / 1000000000000), orderedInterval (-16906986446 / 1000000000000) (-16906986445 / 1000000000000))
    | 16 => (orderedInterval (-19633974044 / 1000000000000) (-19633974043 / 1000000000000), orderedInterval (-26855575009 / 1000000000000) (-26855575008 / 1000000000000))
    | 17 => (orderedInterval (-25752034174 / 1000000000000) (-25752034142 / 1000000000000), orderedInterval (-10041451434 / 1000000000000) (-10041451403 / 1000000000000))
    | 18 => (orderedInterval (8850703701 / 1000000000000) (8850703717 / 1000000000000), orderedInterval (-36110204519 / 1000000000000) (-36110204503 / 1000000000000))
    | 19 => (orderedInterval (38882426898 / 1000000000000) (38882433089 / 1000000000000), orderedInterval (-10909858480 / 1000000000000) (-10909852289 / 1000000000000))
    | 20 => (orderedInterval (8621434419 / 1000000000000) (8621434420 / 1000000000000), orderedInterval (50283390463 / 1000000000000) (50283390464 / 1000000000000))
    | 21 => (orderedInterval (20055047538 / 1000000000000) (20055047539 / 1000000000000), orderedInterval (66562333144 / 1000000000000) (66562333145 / 1000000000000))
    | 22 => (orderedInterval (-17652684601 / 1000000000000) (-17652684100 / 1000000000000), orderedInterval (38391456278 / 1000000000000) (38391456780 / 1000000000000))
    | 23 => (orderedInterval (-33543541120 / 1000000000000) (-33543541118 / 1000000000000), orderedInterval (-13423535355 / 1000000000000) (-13423535353 / 1000000000000))
    | 24 => (orderedInterval (-26129277928 / 1000000000000) (-26129275480 / 1000000000000), orderedInterval (49120402391 / 1000000000000) (49120404839 / 1000000000000))
    | 25 => (orderedInterval (9535104861 / 1000000000000) (9535104866 / 1000000000000), orderedInterval (-25872146804 / 1000000000000) (-25872146799 / 1000000000000))
    | _ => (orderedInterval (30126888759 / 1000000000000) (30126888760 / 1000000000000), orderedInterval (15144144810 / 1000000000000) (15144144812 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-13699591728 / 1000000000000) (-13699570884 / 1000000000000)
      | 1 => orderedInterval (258307415 / 1000000000000) (258307470 / 1000000000000)
      | 2 => orderedInterval (-464067995 / 1000000000000) (-464067969 / 1000000000000)
      | 3 => orderedInterval (-1252597636 / 1000000000000) (-1252597403 / 1000000000000)
      | 4 => orderedInterval (-2175950413 / 1000000000000) (-2175949791 / 1000000000000)
      | 5 => orderedInterval (160440352 / 1000000000000) (160440396 / 1000000000000)
      | 6 => orderedInterval (-3335231555 / 1000000000000) (-3335231089 / 1000000000000)
      | 7 => orderedInterval (2600904269 / 1000000000000) (2600904335 / 1000000000000)
      | _ => orderedInterval (-6586293908 / 1000000000000) (-6586293767 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (4605362266 / 1000000000000) (4605383113 / 1000000000000)
      | 1 => orderedInterval (2463562103 / 1000000000000) (2463562165 / 1000000000000)
      | 2 => orderedInterval (-2419187755 / 1000000000000) (-2419187711 / 1000000000000)
      | 3 => orderedInterval (2387215378 / 1000000000000) (2387215873 / 1000000000000)
      | 4 => orderedInterval (-1715650765 / 1000000000000) (-1715649695 / 1000000000000)
      | 5 => orderedInterval (1203473009 / 1000000000000) (1203473073 / 1000000000000)
      | 6 => orderedInterval (7329210296 / 1000000000000) (7329210707 / 1000000000000)
      | 7 => orderedInterval (64207350 / 1000000000000) (64207408 / 1000000000000)
      | _ => orderedInterval (522369365 / 1000000000000) (522369548 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (13718348630 / 1000000000000) (13718369528 / 1000000000000)
      | 1 => orderedInterval (-663301094 / 1000000000000) (-663301009 / 1000000000000)
      | 2 => orderedInterval (890527000 / 1000000000000) (890527078 / 1000000000000)
      | 3 => orderedInterval (-1906710931 / 1000000000000) (-1906709852 / 1000000000000)
      | 4 => orderedInterval (4591319526 / 1000000000000) (4591321374 / 1000000000000)
      | 5 => orderedInterval (1055884553 / 1000000000000) (1055884649 / 1000000000000)
      | 6 => orderedInterval (3036189242 / 1000000000000) (3036189609 / 1000000000000)
      | 7 => orderedInterval (-3228517043 / 1000000000000) (-3228516987 / 1000000000000)
      | _ => orderedInterval (11434918510 / 1000000000000) (11434918774 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-3508083281 / 1000000000000) (-3508062378 / 1000000000000)
      | 1 => orderedInterval (-7804773144 / 1000000000000) (-7804773017 / 1000000000000)
      | 2 => orderedInterval (8050570260 / 1000000000000) (8050570402 / 1000000000000)
      | 3 => orderedInterval (-14440059451 / 1000000000000) (-14440057059 / 1000000000000)
      | 4 => orderedInterval (2073639936 / 1000000000000) (2073643132 / 1000000000000)
      | 5 => orderedInterval (-981044209 / 1000000000000) (-981044061 / 1000000000000)
      | 6 => orderedInterval (-6849140084 / 1000000000000) (-6849139756 / 1000000000000)
      | 7 => orderedInterval (-831566216 / 1000000000000) (-831566160 / 1000000000000)
      | _ => orderedInterval (-8149144930 / 1000000000000) (-8149144526 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-13815885094 / 1000000000000) (-13815864137 / 1000000000000)
      | 1 => orderedInterval (1794038921 / 1000000000000) (1794039118 / 1000000000000)
      | 2 => orderedInterval (-1522188194 / 1000000000000) (-1522187930 / 1000000000000)
      | 3 => orderedInterval (25321663676 / 1000000000000) (25321669034 / 1000000000000)
      | 4 => orderedInterval (-8328733404 / 1000000000000) (-8328727862 / 1000000000000)
      | 5 => orderedInterval (-6044780405 / 1000000000000) (-6044780169 / 1000000000000)
      | 6 => orderedInterval (-2738098792 / 1000000000000) (-2738098494 / 1000000000000)
      | 7 => orderedInterval (3679632980 / 1000000000000) (3679633037 / 1000000000000)
      | _ => orderedInterval (-22699444202 / 1000000000000) (-22699443555 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-24494081199 / 1000000000000) (-24494058702 / 1000000000000)
    | 1 => orderedInterval (14440561247 / 1000000000000) (14440584481 / 1000000000000)
    | 2 => orderedInterval (28928658393 / 1000000000000) (28928683164 / 1000000000000)
    | 3 => orderedInterval (-32439601119 / 1000000000000) (-32439573423 / 1000000000000)
    | _ => orderedInterval (-24353794514 / 1000000000000) (-24353760958 / 1000000000000)

theorem compactCertificate579_stateChecks0 :
    compactCertificate579.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 143 12 (901 / 2)) (orderedInterval (-33573751442 / 1000000000000) (-33573698942 / 1000000000000), orderedInterval (16947139914 / 1000000000000) (16947192414 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 106 12 (1327345044058801 / 4000000000000)) (orderedInterval (-16552640605 / 1000000000000) (-16552640267 / 1000000000000), orderedInterval (40577218825 / 1000000000000) (40577219163 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 171 12 (429236115223633 / 800000000000)) (orderedInterval (-4054002002 / 1000000000000) (-4054002001 / 1000000000000), orderedInterval (-34202687397 / 1000000000000) (-34202687396 / 1000000000000))) = true
  rfl'

theorem compactCertificate579_stateChecks1 :
    compactCertificate579.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 31 12 (387315973410707 / 4000000000000)) (orderedInterval (-17989804154 / 1000000000000) (-17989804153 / 1000000000000), orderedInterval (-78971178379 / 1000000000000) (-78971178378 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 83 12 (1040385185079479 / 4000000000000)) (orderedInterval (-6365552413 / 1000000000000) (-6365552412 / 1000000000000), orderedInterval (-49050123159 / 1000000000000) (-49050123158 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 225 12 (2824848161231643 / 4000000000000)) (orderedInterval (-4157402552 / 1000000000000) (-4157402551 / 1000000000000), orderedInterval (-29732106580 / 1000000000000) (-29732106579 / 1000000000000))) = true
  rfl'

theorem compactCertificate579_stateChecks2 :
    compactCertificate579.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 166 12 (2080770370159859 / 4000000000000)) (orderedInterval (-17583290493 / 1000000000000) (-17583289906 / 1000000000000), orderedInterval (30259977549 / 1000000000000) (30259978137 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 284 12 (3565435494863807 / 4000000000000)) (orderedInterval (-1820735117 / 1000000000000) (-1820735116 / 1000000000000), orderedInterval (26663685721 / 1000000000000) (26663685722 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 209 12 (2626283648177213 / 4000000000000)) (orderedInterval (-21525411966 / 1000000000000) (-21525411965 / 1000000000000), orderedInterval (-22484047151 / 1000000000000) (-22484047150 / 1000000000000))) = true
  rfl'

theorem compactCertificate579_stateChecks3 :
    compactCertificate579.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 321 12 (4029394495454099 / 4000000000000)) (orderedInterval (7844516632 / 1000000000000) (7844516633 / 1000000000000), orderedInterval (-23887763573 / 1000000000000) (-23887763572 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 185 12 (2326371996621371 / 4000000000000)) (orderedInterval (-30634978483 / 1000000000000) (-30634978480 / 1000000000000), orderedInterval (-12468129246 / 1000000000000) (-12468129242 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 329 12 (4128187931933239 / 4000000000000)) (orderedInterval (16960803530 / 1000000000000) (16960803911 / 1000000000000), orderedInterval (-18151609536 / 1000000000000) (-18151609155 / 1000000000000))) = true
  rfl'

theorem compactCertificate579_stateChecks4 :
    compactCertificate579.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 307 12 (3857088660466291 / 4000000000000)) (orderedInterval (-14263142671 / 1000000000000) (-14263142670 / 1000000000000), orderedInterval (-21364790659 / 1000000000000) (-21364790658 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 219 12 (2752600467436003 / 4000000000000)) (orderedInterval (-24318844967 / 1000000000000) (-24318844966 / 1000000000000), orderedInterval (-18250096810 / 1000000000000) (-18250096809 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 248 12 (3121155555238437 / 4000000000000)) (orderedInterval (26436492992 / 1000000000000) (26436605053 / 1000000000000), orderedInterval (-10832988338 / 1000000000000) (-10832876277 / 1000000000000))) = true
  rfl'

theorem compactCertificate579_stateChecks5 :
    compactCertificate579.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 207 12 (2602094105133653 / 4000000000000)) (orderedInterval (-26307724570 / 1000000000000) (-26307724569 / 1000000000000), orderedInterval (-16906986446 / 1000000000000) (-16906986445 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 183 12 (2299029055482713 / 4000000000000)) (orderedInterval (-19633974044 / 1000000000000) (-19633974043 / 1000000000000), orderedInterval (-26855575009 / 1000000000000) (-26855575008 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 265 12 (666348229240587 / 800000000000)) (orderedInterval (-25752034174 / 1000000000000) (-25752034142 / 1000000000000), orderedInterval (-10041451434 / 1000000000000) (-10041451403 / 1000000000000))) = true
  rfl'

theorem compactCertificate579_stateChecks6 :
    compactCertificate579.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 147 12 (1843154270065489 / 4000000000000)) (orderedInterval (8850703701 / 1000000000000) (8850703717 / 1000000000000), orderedInterval (-36110204519 / 1000000000000) (-36110204503 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 124 12 (1562462287109129 / 4000000000000)) (orderedInterval (38882426898 / 1000000000000) (38882433089 / 1000000000000), orderedInterval (-10909858480 / 1000000000000) (-10909852289 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 78 12 (977716351822787 / 4000000000000)) (orderedInterval (8621434419 / 1000000000000) (8621434420 / 1000000000000), orderedInterval (50283390463 / 1000000000000) (50283390464 / 1000000000000))) = true
  rfl'

theorem compactCertificate579_stateChecks7 :
    compactCertificate579.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 42 12 (525819105748029 / 4000000000000)) (orderedInterval (20055047538 / 1000000000000) (20055047539 / 1000000000000), orderedInterval (66562333144 / 1000000000000) (66562333145 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 114 12 (1427701158491087 / 4000000000000)) (orderedInterval (-17652684601 / 1000000000000) (-17652684100 / 1000000000000), orderedInterval (38391456278 / 1000000000000) (38391456780 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 155 12 (1949403873993199 / 4000000000000)) (orderedInterval (-33543541120 / 1000000000000) (-33543541118 / 1000000000000), orderedInterval (-13423535355 / 1000000000000) (-13423535353 / 1000000000000))) = true
  rfl'

theorem compactCertificate579_stateChecks8 :
    compactCertificate579.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (824283648177213 / 4000000000000)) (orderedInterval (-26129277928 / 1000000000000) (-26129275480 / 1000000000000), orderedInterval (49120402391 / 1000000000000) (49120404839 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 267 12 (3350667266980573 / 4000000000000)) (orderedInterval (9535104861 / 1000000000000) (9535104866 / 1000000000000), orderedInterval (-25872146804 / 1000000000000) (-25872146799 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 178 12 (2238090450805907 / 4000000000000)) (orderedInterval (30126888759 / 1000000000000) (30126888760 / 1000000000000), orderedInterval (15144144810 / 1000000000000) (15144144812 / 1000000000000))) = true
  rfl'

theorem compactCertificate579_states : ∀ j,
    BesselStateValid (compactCertificate579.point j) (compactCertificate579.state j) :=
  compactCertificate579.statesValid_of_checks3 compactCertificate579_stateChecks0
    compactCertificate579_stateChecks1 compactCertificate579_stateChecks2
    compactCertificate579_stateChecks3 compactCertificate579_stateChecks4
    compactCertificate579_stateChecks5 compactCertificate579_stateChecks6
    compactCertificate579_stateChecks7 compactCertificate579_stateChecks8

theorem compactCertificate579_chunkChecks0_0 :
    compactCertificate579.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (901 / 2) 0 (IntervalRat.scale (901 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-33573751442 / 1000000000000) (-33573698942 / 1000000000000), orderedInterval (16947139914 / 1000000000000) (16947192414 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1327345044058801 / 4000000000000) 0 (IntervalRat.scale (901 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-16552640605 / 1000000000000) (-16552640267 / 1000000000000), orderedInterval (40577218825 / 1000000000000) (40577219163 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (429236115223633 / 800000000000) 0 (IntervalRat.scale (901 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-4054002002 / 1000000000000) (-4054002001 / 1000000000000), orderedInterval (-34202687397 / 1000000000000) (-34202687396 / 1000000000000)))) (orderedInterval (-13699591728 / 1000000000000) (-13699570884 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (387315973410707 / 4000000000000) 0 (IntervalRat.scale (901 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-17989804154 / 1000000000000) (-17989804153 / 1000000000000), orderedInterval (-78971178379 / 1000000000000) (-78971178378 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (1040385185079479 / 4000000000000) 0 (IntervalRat.scale (901 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-6365552413 / 1000000000000) (-6365552412 / 1000000000000), orderedInterval (-49050123159 / 1000000000000) (-49050123158 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2824848161231643 / 4000000000000) 0 (IntervalRat.scale (901 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-4157402552 / 1000000000000) (-4157402551 / 1000000000000), orderedInterval (-29732106580 / 1000000000000) (-29732106579 / 1000000000000)))) (orderedInterval (258307415 / 1000000000000) (258307470 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (2080770370159859 / 4000000000000) 0 (IntervalRat.scale (901 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-17583290493 / 1000000000000) (-17583289906 / 1000000000000), orderedInterval (30259977549 / 1000000000000) (30259978137 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3565435494863807 / 4000000000000) 0 (IntervalRat.scale (901 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-1820735117 / 1000000000000) (-1820735116 / 1000000000000), orderedInterval (26663685721 / 1000000000000) (26663685722 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2626283648177213 / 4000000000000) 0 (IntervalRat.scale (901 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-21525411966 / 1000000000000) (-21525411965 / 1000000000000), orderedInterval (-22484047151 / 1000000000000) (-22484047150 / 1000000000000)))) (orderedInterval (-464067995 / 1000000000000) (-464067969 / 1000000000000))) = true
  rfl'

theorem compactCertificate579_chunkChecks0_1 :
    compactCertificate579.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (4029394495454099 / 4000000000000) 0 (IntervalRat.scale (901 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (7844516632 / 1000000000000) (7844516633 / 1000000000000), orderedInterval (-23887763573 / 1000000000000) (-23887763572 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2326371996621371 / 4000000000000) 0 (IntervalRat.scale (901 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-30634978483 / 1000000000000) (-30634978480 / 1000000000000), orderedInterval (-12468129246 / 1000000000000) (-12468129242 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (4128187931933239 / 4000000000000) 0 (IntervalRat.scale (901 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (16960803530 / 1000000000000) (16960803911 / 1000000000000), orderedInterval (-18151609536 / 1000000000000) (-18151609155 / 1000000000000)))) (orderedInterval (-1252597636 / 1000000000000) (-1252597403 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3857088660466291 / 4000000000000) 0 (IntervalRat.scale (901 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-14263142671 / 1000000000000) (-14263142670 / 1000000000000), orderedInterval (-21364790659 / 1000000000000) (-21364790658 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2752600467436003 / 4000000000000) 0 (IntervalRat.scale (901 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-24318844967 / 1000000000000) (-24318844966 / 1000000000000), orderedInterval (-18250096810 / 1000000000000) (-18250096809 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (3121155555238437 / 4000000000000) 0 (IntervalRat.scale (901 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (26436492992 / 1000000000000) (26436605053 / 1000000000000), orderedInterval (-10832988338 / 1000000000000) (-10832876277 / 1000000000000)))) (orderedInterval (-2175950413 / 1000000000000) (-2175949791 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2602094105133653 / 4000000000000) 0 (IntervalRat.scale (901 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-26307724570 / 1000000000000) (-26307724569 / 1000000000000), orderedInterval (-16906986446 / 1000000000000) (-16906986445 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2299029055482713 / 4000000000000) 0 (IntervalRat.scale (901 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-19633974044 / 1000000000000) (-19633974043 / 1000000000000), orderedInterval (-26855575009 / 1000000000000) (-26855575008 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (666348229240587 / 800000000000) 0 (IntervalRat.scale (901 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-25752034174 / 1000000000000) (-25752034142 / 1000000000000), orderedInterval (-10041451434 / 1000000000000) (-10041451403 / 1000000000000)))) (orderedInterval (160440352 / 1000000000000) (160440396 / 1000000000000))) = true
  rfl'

theorem compactCertificate579_chunkChecks0_2 :
    compactCertificate579.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1843154270065489 / 4000000000000) 0 (IntervalRat.scale (901 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (8850703701 / 1000000000000) (8850703717 / 1000000000000), orderedInterval (-36110204519 / 1000000000000) (-36110204503 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1562462287109129 / 4000000000000) 0 (IntervalRat.scale (901 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (38882426898 / 1000000000000) (38882433089 / 1000000000000), orderedInterval (-10909858480 / 1000000000000) (-10909852289 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (977716351822787 / 4000000000000) 0 (IntervalRat.scale (901 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (8621434419 / 1000000000000) (8621434420 / 1000000000000), orderedInterval (50283390463 / 1000000000000) (50283390464 / 1000000000000)))) (orderedInterval (-3335231555 / 1000000000000) (-3335231089 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (525819105748029 / 4000000000000) 0 (IntervalRat.scale (901 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (20055047538 / 1000000000000) (20055047539 / 1000000000000), orderedInterval (66562333144 / 1000000000000) (66562333145 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1427701158491087 / 4000000000000) 0 (IntervalRat.scale (901 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-17652684601 / 1000000000000) (-17652684100 / 1000000000000), orderedInterval (38391456278 / 1000000000000) (38391456780 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1949403873993199 / 4000000000000) 0 (IntervalRat.scale (901 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-33543541120 / 1000000000000) (-33543541118 / 1000000000000), orderedInterval (-13423535355 / 1000000000000) (-13423535353 / 1000000000000)))) (orderedInterval (2600904269 / 1000000000000) (2600904335 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (824283648177213 / 4000000000000) 0 (IntervalRat.scale (901 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-26129277928 / 1000000000000) (-26129275480 / 1000000000000), orderedInterval (49120402391 / 1000000000000) (49120404839 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3350667266980573 / 4000000000000) 0 (IntervalRat.scale (901 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (9535104861 / 1000000000000) (9535104866 / 1000000000000), orderedInterval (-25872146804 / 1000000000000) (-25872146799 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2238090450805907 / 4000000000000) 0 (IntervalRat.scale (901 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (30126888759 / 1000000000000) (30126888760 / 1000000000000), orderedInterval (15144144810 / 1000000000000) (15144144812 / 1000000000000)))) (orderedInterval (-6586293908 / 1000000000000) (-6586293767 / 1000000000000))) = true
  rfl'

theorem compactCertificate579_chunkChecks0 :
    compactCertificate579.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate579.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate579_chunkChecks0_0
    compactCertificate579_chunkChecks0_1 compactCertificate579_chunkChecks0_2

theorem compactCertificate579_chunkChecks1_0 :
    compactCertificate579.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (901 / 2) 1 (IntervalRat.scale (901 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-33573751442 / 1000000000000) (-33573698942 / 1000000000000), orderedInterval (16947139914 / 1000000000000) (16947192414 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1327345044058801 / 4000000000000) 1 (IntervalRat.scale (901 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-16552640605 / 1000000000000) (-16552640267 / 1000000000000), orderedInterval (40577218825 / 1000000000000) (40577219163 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (429236115223633 / 800000000000) 1 (IntervalRat.scale (901 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-4054002002 / 1000000000000) (-4054002001 / 1000000000000), orderedInterval (-34202687397 / 1000000000000) (-34202687396 / 1000000000000)))) (orderedInterval (4605362266 / 1000000000000) (4605383113 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (387315973410707 / 4000000000000) 1 (IntervalRat.scale (901 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-17989804154 / 1000000000000) (-17989804153 / 1000000000000), orderedInterval (-78971178379 / 1000000000000) (-78971178378 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (1040385185079479 / 4000000000000) 1 (IntervalRat.scale (901 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-6365552413 / 1000000000000) (-6365552412 / 1000000000000), orderedInterval (-49050123159 / 1000000000000) (-49050123158 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2824848161231643 / 4000000000000) 1 (IntervalRat.scale (901 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-4157402552 / 1000000000000) (-4157402551 / 1000000000000), orderedInterval (-29732106580 / 1000000000000) (-29732106579 / 1000000000000)))) (orderedInterval (2463562103 / 1000000000000) (2463562165 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (2080770370159859 / 4000000000000) 1 (IntervalRat.scale (901 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-17583290493 / 1000000000000) (-17583289906 / 1000000000000), orderedInterval (30259977549 / 1000000000000) (30259978137 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3565435494863807 / 4000000000000) 1 (IntervalRat.scale (901 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-1820735117 / 1000000000000) (-1820735116 / 1000000000000), orderedInterval (26663685721 / 1000000000000) (26663685722 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2626283648177213 / 4000000000000) 1 (IntervalRat.scale (901 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-21525411966 / 1000000000000) (-21525411965 / 1000000000000), orderedInterval (-22484047151 / 1000000000000) (-22484047150 / 1000000000000)))) (orderedInterval (-2419187755 / 1000000000000) (-2419187711 / 1000000000000))) = true
  rfl'

theorem compactCertificate579_chunkChecks1_1 :
    compactCertificate579.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (4029394495454099 / 4000000000000) 1 (IntervalRat.scale (901 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (7844516632 / 1000000000000) (7844516633 / 1000000000000), orderedInterval (-23887763573 / 1000000000000) (-23887763572 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2326371996621371 / 4000000000000) 1 (IntervalRat.scale (901 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-30634978483 / 1000000000000) (-30634978480 / 1000000000000), orderedInterval (-12468129246 / 1000000000000) (-12468129242 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (4128187931933239 / 4000000000000) 1 (IntervalRat.scale (901 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (16960803530 / 1000000000000) (16960803911 / 1000000000000), orderedInterval (-18151609536 / 1000000000000) (-18151609155 / 1000000000000)))) (orderedInterval (2387215378 / 1000000000000) (2387215873 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3857088660466291 / 4000000000000) 1 (IntervalRat.scale (901 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-14263142671 / 1000000000000) (-14263142670 / 1000000000000), orderedInterval (-21364790659 / 1000000000000) (-21364790658 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2752600467436003 / 4000000000000) 1 (IntervalRat.scale (901 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-24318844967 / 1000000000000) (-24318844966 / 1000000000000), orderedInterval (-18250096810 / 1000000000000) (-18250096809 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (3121155555238437 / 4000000000000) 1 (IntervalRat.scale (901 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (26436492992 / 1000000000000) (26436605053 / 1000000000000), orderedInterval (-10832988338 / 1000000000000) (-10832876277 / 1000000000000)))) (orderedInterval (-1715650765 / 1000000000000) (-1715649695 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2602094105133653 / 4000000000000) 1 (IntervalRat.scale (901 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-26307724570 / 1000000000000) (-26307724569 / 1000000000000), orderedInterval (-16906986446 / 1000000000000) (-16906986445 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2299029055482713 / 4000000000000) 1 (IntervalRat.scale (901 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-19633974044 / 1000000000000) (-19633974043 / 1000000000000), orderedInterval (-26855575009 / 1000000000000) (-26855575008 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (666348229240587 / 800000000000) 1 (IntervalRat.scale (901 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-25752034174 / 1000000000000) (-25752034142 / 1000000000000), orderedInterval (-10041451434 / 1000000000000) (-10041451403 / 1000000000000)))) (orderedInterval (1203473009 / 1000000000000) (1203473073 / 1000000000000))) = true
  rfl'

theorem compactCertificate579_chunkChecks1_2 :
    compactCertificate579.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1843154270065489 / 4000000000000) 1 (IntervalRat.scale (901 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (8850703701 / 1000000000000) (8850703717 / 1000000000000), orderedInterval (-36110204519 / 1000000000000) (-36110204503 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1562462287109129 / 4000000000000) 1 (IntervalRat.scale (901 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (38882426898 / 1000000000000) (38882433089 / 1000000000000), orderedInterval (-10909858480 / 1000000000000) (-10909852289 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (977716351822787 / 4000000000000) 1 (IntervalRat.scale (901 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (8621434419 / 1000000000000) (8621434420 / 1000000000000), orderedInterval (50283390463 / 1000000000000) (50283390464 / 1000000000000)))) (orderedInterval (7329210296 / 1000000000000) (7329210707 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (525819105748029 / 4000000000000) 1 (IntervalRat.scale (901 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (20055047538 / 1000000000000) (20055047539 / 1000000000000), orderedInterval (66562333144 / 1000000000000) (66562333145 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1427701158491087 / 4000000000000) 1 (IntervalRat.scale (901 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-17652684601 / 1000000000000) (-17652684100 / 1000000000000), orderedInterval (38391456278 / 1000000000000) (38391456780 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1949403873993199 / 4000000000000) 1 (IntervalRat.scale (901 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-33543541120 / 1000000000000) (-33543541118 / 1000000000000), orderedInterval (-13423535355 / 1000000000000) (-13423535353 / 1000000000000)))) (orderedInterval (64207350 / 1000000000000) (64207408 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (824283648177213 / 4000000000000) 1 (IntervalRat.scale (901 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-26129277928 / 1000000000000) (-26129275480 / 1000000000000), orderedInterval (49120402391 / 1000000000000) (49120404839 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3350667266980573 / 4000000000000) 1 (IntervalRat.scale (901 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (9535104861 / 1000000000000) (9535104866 / 1000000000000), orderedInterval (-25872146804 / 1000000000000) (-25872146799 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2238090450805907 / 4000000000000) 1 (IntervalRat.scale (901 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (30126888759 / 1000000000000) (30126888760 / 1000000000000), orderedInterval (15144144810 / 1000000000000) (15144144812 / 1000000000000)))) (orderedInterval (522369365 / 1000000000000) (522369548 / 1000000000000))) = true
  rfl'

theorem compactCertificate579_chunkChecks1 :
    compactCertificate579.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate579.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate579_chunkChecks1_0
    compactCertificate579_chunkChecks1_1 compactCertificate579_chunkChecks1_2

theorem compactCertificate579_chunkChecks2_0 :
    compactCertificate579.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (901 / 2) 2 (IntervalRat.scale (901 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-33573751442 / 1000000000000) (-33573698942 / 1000000000000), orderedInterval (16947139914 / 1000000000000) (16947192414 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1327345044058801 / 4000000000000) 2 (IntervalRat.scale (901 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-16552640605 / 1000000000000) (-16552640267 / 1000000000000), orderedInterval (40577218825 / 1000000000000) (40577219163 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (429236115223633 / 800000000000) 2 (IntervalRat.scale (901 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-4054002002 / 1000000000000) (-4054002001 / 1000000000000), orderedInterval (-34202687397 / 1000000000000) (-34202687396 / 1000000000000)))) (orderedInterval (13718348630 / 1000000000000) (13718369528 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (387315973410707 / 4000000000000) 2 (IntervalRat.scale (901 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-17989804154 / 1000000000000) (-17989804153 / 1000000000000), orderedInterval (-78971178379 / 1000000000000) (-78971178378 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (1040385185079479 / 4000000000000) 2 (IntervalRat.scale (901 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-6365552413 / 1000000000000) (-6365552412 / 1000000000000), orderedInterval (-49050123159 / 1000000000000) (-49050123158 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2824848161231643 / 4000000000000) 2 (IntervalRat.scale (901 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-4157402552 / 1000000000000) (-4157402551 / 1000000000000), orderedInterval (-29732106580 / 1000000000000) (-29732106579 / 1000000000000)))) (orderedInterval (-663301094 / 1000000000000) (-663301009 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (2080770370159859 / 4000000000000) 2 (IntervalRat.scale (901 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-17583290493 / 1000000000000) (-17583289906 / 1000000000000), orderedInterval (30259977549 / 1000000000000) (30259978137 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3565435494863807 / 4000000000000) 2 (IntervalRat.scale (901 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-1820735117 / 1000000000000) (-1820735116 / 1000000000000), orderedInterval (26663685721 / 1000000000000) (26663685722 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2626283648177213 / 4000000000000) 2 (IntervalRat.scale (901 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-21525411966 / 1000000000000) (-21525411965 / 1000000000000), orderedInterval (-22484047151 / 1000000000000) (-22484047150 / 1000000000000)))) (orderedInterval (890527000 / 1000000000000) (890527078 / 1000000000000))) = true
  rfl'

theorem compactCertificate579_chunkChecks2_1 :
    compactCertificate579.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (4029394495454099 / 4000000000000) 2 (IntervalRat.scale (901 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (7844516632 / 1000000000000) (7844516633 / 1000000000000), orderedInterval (-23887763573 / 1000000000000) (-23887763572 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2326371996621371 / 4000000000000) 2 (IntervalRat.scale (901 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-30634978483 / 1000000000000) (-30634978480 / 1000000000000), orderedInterval (-12468129246 / 1000000000000) (-12468129242 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (4128187931933239 / 4000000000000) 2 (IntervalRat.scale (901 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (16960803530 / 1000000000000) (16960803911 / 1000000000000), orderedInterval (-18151609536 / 1000000000000) (-18151609155 / 1000000000000)))) (orderedInterval (-1906710931 / 1000000000000) (-1906709852 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3857088660466291 / 4000000000000) 2 (IntervalRat.scale (901 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-14263142671 / 1000000000000) (-14263142670 / 1000000000000), orderedInterval (-21364790659 / 1000000000000) (-21364790658 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2752600467436003 / 4000000000000) 2 (IntervalRat.scale (901 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-24318844967 / 1000000000000) (-24318844966 / 1000000000000), orderedInterval (-18250096810 / 1000000000000) (-18250096809 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (3121155555238437 / 4000000000000) 2 (IntervalRat.scale (901 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (26436492992 / 1000000000000) (26436605053 / 1000000000000), orderedInterval (-10832988338 / 1000000000000) (-10832876277 / 1000000000000)))) (orderedInterval (4591319526 / 1000000000000) (4591321374 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2602094105133653 / 4000000000000) 2 (IntervalRat.scale (901 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-26307724570 / 1000000000000) (-26307724569 / 1000000000000), orderedInterval (-16906986446 / 1000000000000) (-16906986445 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2299029055482713 / 4000000000000) 2 (IntervalRat.scale (901 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-19633974044 / 1000000000000) (-19633974043 / 1000000000000), orderedInterval (-26855575009 / 1000000000000) (-26855575008 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (666348229240587 / 800000000000) 2 (IntervalRat.scale (901 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-25752034174 / 1000000000000) (-25752034142 / 1000000000000), orderedInterval (-10041451434 / 1000000000000) (-10041451403 / 1000000000000)))) (orderedInterval (1055884553 / 1000000000000) (1055884649 / 1000000000000))) = true
  rfl'

theorem compactCertificate579_chunkChecks2_2 :
    compactCertificate579.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1843154270065489 / 4000000000000) 2 (IntervalRat.scale (901 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (8850703701 / 1000000000000) (8850703717 / 1000000000000), orderedInterval (-36110204519 / 1000000000000) (-36110204503 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1562462287109129 / 4000000000000) 2 (IntervalRat.scale (901 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (38882426898 / 1000000000000) (38882433089 / 1000000000000), orderedInterval (-10909858480 / 1000000000000) (-10909852289 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (977716351822787 / 4000000000000) 2 (IntervalRat.scale (901 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (8621434419 / 1000000000000) (8621434420 / 1000000000000), orderedInterval (50283390463 / 1000000000000) (50283390464 / 1000000000000)))) (orderedInterval (3036189242 / 1000000000000) (3036189609 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (525819105748029 / 4000000000000) 2 (IntervalRat.scale (901 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (20055047538 / 1000000000000) (20055047539 / 1000000000000), orderedInterval (66562333144 / 1000000000000) (66562333145 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1427701158491087 / 4000000000000) 2 (IntervalRat.scale (901 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-17652684601 / 1000000000000) (-17652684100 / 1000000000000), orderedInterval (38391456278 / 1000000000000) (38391456780 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1949403873993199 / 4000000000000) 2 (IntervalRat.scale (901 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-33543541120 / 1000000000000) (-33543541118 / 1000000000000), orderedInterval (-13423535355 / 1000000000000) (-13423535353 / 1000000000000)))) (orderedInterval (-3228517043 / 1000000000000) (-3228516987 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (824283648177213 / 4000000000000) 2 (IntervalRat.scale (901 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-26129277928 / 1000000000000) (-26129275480 / 1000000000000), orderedInterval (49120402391 / 1000000000000) (49120404839 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3350667266980573 / 4000000000000) 2 (IntervalRat.scale (901 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (9535104861 / 1000000000000) (9535104866 / 1000000000000), orderedInterval (-25872146804 / 1000000000000) (-25872146799 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2238090450805907 / 4000000000000) 2 (IntervalRat.scale (901 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (30126888759 / 1000000000000) (30126888760 / 1000000000000), orderedInterval (15144144810 / 1000000000000) (15144144812 / 1000000000000)))) (orderedInterval (11434918510 / 1000000000000) (11434918774 / 1000000000000))) = true
  rfl'

theorem compactCertificate579_chunkChecks2 :
    compactCertificate579.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate579.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate579_chunkChecks2_0
    compactCertificate579_chunkChecks2_1 compactCertificate579_chunkChecks2_2

theorem compactCertificate579_chunkChecks3_0 :
    compactCertificate579.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (901 / 2) 3 (IntervalRat.scale (901 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-33573751442 / 1000000000000) (-33573698942 / 1000000000000), orderedInterval (16947139914 / 1000000000000) (16947192414 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1327345044058801 / 4000000000000) 3 (IntervalRat.scale (901 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-16552640605 / 1000000000000) (-16552640267 / 1000000000000), orderedInterval (40577218825 / 1000000000000) (40577219163 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (429236115223633 / 800000000000) 3 (IntervalRat.scale (901 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-4054002002 / 1000000000000) (-4054002001 / 1000000000000), orderedInterval (-34202687397 / 1000000000000) (-34202687396 / 1000000000000)))) (orderedInterval (-3508083281 / 1000000000000) (-3508062378 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (387315973410707 / 4000000000000) 3 (IntervalRat.scale (901 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-17989804154 / 1000000000000) (-17989804153 / 1000000000000), orderedInterval (-78971178379 / 1000000000000) (-78971178378 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (1040385185079479 / 4000000000000) 3 (IntervalRat.scale (901 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-6365552413 / 1000000000000) (-6365552412 / 1000000000000), orderedInterval (-49050123159 / 1000000000000) (-49050123158 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2824848161231643 / 4000000000000) 3 (IntervalRat.scale (901 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-4157402552 / 1000000000000) (-4157402551 / 1000000000000), orderedInterval (-29732106580 / 1000000000000) (-29732106579 / 1000000000000)))) (orderedInterval (-7804773144 / 1000000000000) (-7804773017 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (2080770370159859 / 4000000000000) 3 (IntervalRat.scale (901 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-17583290493 / 1000000000000) (-17583289906 / 1000000000000), orderedInterval (30259977549 / 1000000000000) (30259978137 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3565435494863807 / 4000000000000) 3 (IntervalRat.scale (901 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-1820735117 / 1000000000000) (-1820735116 / 1000000000000), orderedInterval (26663685721 / 1000000000000) (26663685722 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2626283648177213 / 4000000000000) 3 (IntervalRat.scale (901 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-21525411966 / 1000000000000) (-21525411965 / 1000000000000), orderedInterval (-22484047151 / 1000000000000) (-22484047150 / 1000000000000)))) (orderedInterval (8050570260 / 1000000000000) (8050570402 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate579_chunkChecks3_1 :
    compactCertificate579.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (4029394495454099 / 4000000000000) 3 (IntervalRat.scale (901 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (7844516632 / 1000000000000) (7844516633 / 1000000000000), orderedInterval (-23887763573 / 1000000000000) (-23887763572 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2326371996621371 / 4000000000000) 3 (IntervalRat.scale (901 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-30634978483 / 1000000000000) (-30634978480 / 1000000000000), orderedInterval (-12468129246 / 1000000000000) (-12468129242 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (4128187931933239 / 4000000000000) 3 (IntervalRat.scale (901 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (16960803530 / 1000000000000) (16960803911 / 1000000000000), orderedInterval (-18151609536 / 1000000000000) (-18151609155 / 1000000000000)))) (orderedInterval (-14440059451 / 1000000000000) (-14440057059 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3857088660466291 / 4000000000000) 3 (IntervalRat.scale (901 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-14263142671 / 1000000000000) (-14263142670 / 1000000000000), orderedInterval (-21364790659 / 1000000000000) (-21364790658 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2752600467436003 / 4000000000000) 3 (IntervalRat.scale (901 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-24318844967 / 1000000000000) (-24318844966 / 1000000000000), orderedInterval (-18250096810 / 1000000000000) (-18250096809 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (3121155555238437 / 4000000000000) 3 (IntervalRat.scale (901 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (26436492992 / 1000000000000) (26436605053 / 1000000000000), orderedInterval (-10832988338 / 1000000000000) (-10832876277 / 1000000000000)))) (orderedInterval (2073639936 / 1000000000000) (2073643132 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2602094105133653 / 4000000000000) 3 (IntervalRat.scale (901 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-26307724570 / 1000000000000) (-26307724569 / 1000000000000), orderedInterval (-16906986446 / 1000000000000) (-16906986445 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2299029055482713 / 4000000000000) 3 (IntervalRat.scale (901 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-19633974044 / 1000000000000) (-19633974043 / 1000000000000), orderedInterval (-26855575009 / 1000000000000) (-26855575008 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (666348229240587 / 800000000000) 3 (IntervalRat.scale (901 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-25752034174 / 1000000000000) (-25752034142 / 1000000000000), orderedInterval (-10041451434 / 1000000000000) (-10041451403 / 1000000000000)))) (orderedInterval (-981044209 / 1000000000000) (-981044061 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate579_chunkChecks3_2 :
    compactCertificate579.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1843154270065489 / 4000000000000) 3 (IntervalRat.scale (901 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (8850703701 / 1000000000000) (8850703717 / 1000000000000), orderedInterval (-36110204519 / 1000000000000) (-36110204503 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1562462287109129 / 4000000000000) 3 (IntervalRat.scale (901 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (38882426898 / 1000000000000) (38882433089 / 1000000000000), orderedInterval (-10909858480 / 1000000000000) (-10909852289 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (977716351822787 / 4000000000000) 3 (IntervalRat.scale (901 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (8621434419 / 1000000000000) (8621434420 / 1000000000000), orderedInterval (50283390463 / 1000000000000) (50283390464 / 1000000000000)))) (orderedInterval (-6849140084 / 1000000000000) (-6849139756 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (525819105748029 / 4000000000000) 3 (IntervalRat.scale (901 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (20055047538 / 1000000000000) (20055047539 / 1000000000000), orderedInterval (66562333144 / 1000000000000) (66562333145 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1427701158491087 / 4000000000000) 3 (IntervalRat.scale (901 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-17652684601 / 1000000000000) (-17652684100 / 1000000000000), orderedInterval (38391456278 / 1000000000000) (38391456780 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1949403873993199 / 4000000000000) 3 (IntervalRat.scale (901 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-33543541120 / 1000000000000) (-33543541118 / 1000000000000), orderedInterval (-13423535355 / 1000000000000) (-13423535353 / 1000000000000)))) (orderedInterval (-831566216 / 1000000000000) (-831566160 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (824283648177213 / 4000000000000) 3 (IntervalRat.scale (901 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-26129277928 / 1000000000000) (-26129275480 / 1000000000000), orderedInterval (49120402391 / 1000000000000) (49120404839 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3350667266980573 / 4000000000000) 3 (IntervalRat.scale (901 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (9535104861 / 1000000000000) (9535104866 / 1000000000000), orderedInterval (-25872146804 / 1000000000000) (-25872146799 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2238090450805907 / 4000000000000) 3 (IntervalRat.scale (901 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (30126888759 / 1000000000000) (30126888760 / 1000000000000), orderedInterval (15144144810 / 1000000000000) (15144144812 / 1000000000000)))) (orderedInterval (-8149144930 / 1000000000000) (-8149144526 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate579_chunkChecks3 :
    compactCertificate579.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate579.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate579_chunkChecks3_0
    compactCertificate579_chunkChecks3_1 compactCertificate579_chunkChecks3_2

theorem compactCertificate579_chunkChecks4_0 :
    compactCertificate579.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (901 / 2) 4 (IntervalRat.scale (901 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-33573751442 / 1000000000000) (-33573698942 / 1000000000000), orderedInterval (16947139914 / 1000000000000) (16947192414 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1327345044058801 / 4000000000000) 4 (IntervalRat.scale (901 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-16552640605 / 1000000000000) (-16552640267 / 1000000000000), orderedInterval (40577218825 / 1000000000000) (40577219163 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (429236115223633 / 800000000000) 4 (IntervalRat.scale (901 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-4054002002 / 1000000000000) (-4054002001 / 1000000000000), orderedInterval (-34202687397 / 1000000000000) (-34202687396 / 1000000000000)))) (orderedInterval (-13815885094 / 1000000000000) (-13815864137 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (387315973410707 / 4000000000000) 4 (IntervalRat.scale (901 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-17989804154 / 1000000000000) (-17989804153 / 1000000000000), orderedInterval (-78971178379 / 1000000000000) (-78971178378 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (1040385185079479 / 4000000000000) 4 (IntervalRat.scale (901 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-6365552413 / 1000000000000) (-6365552412 / 1000000000000), orderedInterval (-49050123159 / 1000000000000) (-49050123158 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2824848161231643 / 4000000000000) 4 (IntervalRat.scale (901 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-4157402552 / 1000000000000) (-4157402551 / 1000000000000), orderedInterval (-29732106580 / 1000000000000) (-29732106579 / 1000000000000)))) (orderedInterval (1794038921 / 1000000000000) (1794039118 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (2080770370159859 / 4000000000000) 4 (IntervalRat.scale (901 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-17583290493 / 1000000000000) (-17583289906 / 1000000000000), orderedInterval (30259977549 / 1000000000000) (30259978137 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3565435494863807 / 4000000000000) 4 (IntervalRat.scale (901 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-1820735117 / 1000000000000) (-1820735116 / 1000000000000), orderedInterval (26663685721 / 1000000000000) (26663685722 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2626283648177213 / 4000000000000) 4 (IntervalRat.scale (901 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-21525411966 / 1000000000000) (-21525411965 / 1000000000000), orderedInterval (-22484047151 / 1000000000000) (-22484047150 / 1000000000000)))) (orderedInterval (-1522188194 / 1000000000000) (-1522187930 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate579_chunkChecks4_1 :
    compactCertificate579.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (4029394495454099 / 4000000000000) 4 (IntervalRat.scale (901 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (7844516632 / 1000000000000) (7844516633 / 1000000000000), orderedInterval (-23887763573 / 1000000000000) (-23887763572 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2326371996621371 / 4000000000000) 4 (IntervalRat.scale (901 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-30634978483 / 1000000000000) (-30634978480 / 1000000000000), orderedInterval (-12468129246 / 1000000000000) (-12468129242 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (4128187931933239 / 4000000000000) 4 (IntervalRat.scale (901 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (16960803530 / 1000000000000) (16960803911 / 1000000000000), orderedInterval (-18151609536 / 1000000000000) (-18151609155 / 1000000000000)))) (orderedInterval (25321663676 / 1000000000000) (25321669034 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3857088660466291 / 4000000000000) 4 (IntervalRat.scale (901 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-14263142671 / 1000000000000) (-14263142670 / 1000000000000), orderedInterval (-21364790659 / 1000000000000) (-21364790658 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2752600467436003 / 4000000000000) 4 (IntervalRat.scale (901 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-24318844967 / 1000000000000) (-24318844966 / 1000000000000), orderedInterval (-18250096810 / 1000000000000) (-18250096809 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (3121155555238437 / 4000000000000) 4 (IntervalRat.scale (901 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (26436492992 / 1000000000000) (26436605053 / 1000000000000), orderedInterval (-10832988338 / 1000000000000) (-10832876277 / 1000000000000)))) (orderedInterval (-8328733404 / 1000000000000) (-8328727862 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2602094105133653 / 4000000000000) 4 (IntervalRat.scale (901 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-26307724570 / 1000000000000) (-26307724569 / 1000000000000), orderedInterval (-16906986446 / 1000000000000) (-16906986445 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2299029055482713 / 4000000000000) 4 (IntervalRat.scale (901 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-19633974044 / 1000000000000) (-19633974043 / 1000000000000), orderedInterval (-26855575009 / 1000000000000) (-26855575008 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (666348229240587 / 800000000000) 4 (IntervalRat.scale (901 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-25752034174 / 1000000000000) (-25752034142 / 1000000000000), orderedInterval (-10041451434 / 1000000000000) (-10041451403 / 1000000000000)))) (orderedInterval (-6044780405 / 1000000000000) (-6044780169 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate579_chunkChecks4_2 :
    compactCertificate579.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1843154270065489 / 4000000000000) 4 (IntervalRat.scale (901 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (8850703701 / 1000000000000) (8850703717 / 1000000000000), orderedInterval (-36110204519 / 1000000000000) (-36110204503 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1562462287109129 / 4000000000000) 4 (IntervalRat.scale (901 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (38882426898 / 1000000000000) (38882433089 / 1000000000000), orderedInterval (-10909858480 / 1000000000000) (-10909852289 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (977716351822787 / 4000000000000) 4 (IntervalRat.scale (901 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (8621434419 / 1000000000000) (8621434420 / 1000000000000), orderedInterval (50283390463 / 1000000000000) (50283390464 / 1000000000000)))) (orderedInterval (-2738098792 / 1000000000000) (-2738098494 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (525819105748029 / 4000000000000) 4 (IntervalRat.scale (901 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (20055047538 / 1000000000000) (20055047539 / 1000000000000), orderedInterval (66562333144 / 1000000000000) (66562333145 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1427701158491087 / 4000000000000) 4 (IntervalRat.scale (901 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-17652684601 / 1000000000000) (-17652684100 / 1000000000000), orderedInterval (38391456278 / 1000000000000) (38391456780 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1949403873993199 / 4000000000000) 4 (IntervalRat.scale (901 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-33543541120 / 1000000000000) (-33543541118 / 1000000000000), orderedInterval (-13423535355 / 1000000000000) (-13423535353 / 1000000000000)))) (orderedInterval (3679632980 / 1000000000000) (3679633037 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (824283648177213 / 4000000000000) 4 (IntervalRat.scale (901 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-26129277928 / 1000000000000) (-26129275480 / 1000000000000), orderedInterval (49120402391 / 1000000000000) (49120404839 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3350667266980573 / 4000000000000) 4 (IntervalRat.scale (901 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (9535104861 / 1000000000000) (9535104866 / 1000000000000), orderedInterval (-25872146804 / 1000000000000) (-25872146799 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2238090450805907 / 4000000000000) 4 (IntervalRat.scale (901 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (30126888759 / 1000000000000) (30126888760 / 1000000000000), orderedInterval (15144144810 / 1000000000000) (15144144812 / 1000000000000)))) (orderedInterval (-22699444202 / 1000000000000) (-22699443555 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate579_chunkChecks4 :
    compactCertificate579.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate579.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate579_chunkChecks4_0
    compactCertificate579_chunkChecks4_1 compactCertificate579_chunkChecks4_2

theorem compactCertificate579_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate579.chunkCheck r b = true :=
  compactCertificate579.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate579_chunkChecks0
    · exact compactCertificate579_chunkChecks1
    · exact compactCertificate579_chunkChecks2
    · exact compactCertificate579_chunkChecks3
    · exact compactCertificate579_chunkChecks4)

theorem compactCertificate579_coefficient0 :
    compactCertificate579.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate579_coefficient1 :
    compactCertificate579.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate579_coefficient2 :
    compactCertificate579.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate579_coefficient3 :
    compactCertificate579.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate579_coefficient4 :
    compactCertificate579.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate579_coefficients : ∀ r : Fin 5,
    compactCertificate579.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate579_coefficient0
  · exact compactCertificate579_coefficient1
  · exact compactCertificate579_coefficient2
  · exact compactCertificate579_coefficient3
  · exact compactCertificate579_coefficient4

theorem compactCertificate579_lower : (1 : ℚ) ≤ compactCertificate579.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate579, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate579_proves {t : ℝ} (ht : t ∈ compactCertificate579.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate579.proves compactCertificate579_states compactCertificate579_chunks
    compactCertificate579_coefficients compactCertificate579_lower ht

end Erdos232
