/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate331 : CompactCertificate where
  left := 203
  right := 204
  center := 407 / 2
  grid := fun i =>
    match i.val with
    | 0 => 65
    | 1 => 48
    | 2 => 77
    | 3 => 14
    | 4 => 37
    | 5 => 102
    | 6 => 75
    | 7 => 128
    | 8 => 94
    | 9 => 145
    | 10 => 84
    | 11 => 148
    | 12 => 139
    | 13 => 99
    | 14 => 112
    | 15 => 94
    | 16 => 83
    | 17 => 120
    | 18 => 66
    | 19 => 56
    | 20 => 35
    | 21 => 19
    | 22 => 51
    | 23 => 70
    | 24 => 30
    | 25 => 121
    | _ => 80
  point := fun i =>
    match i.val with
    | 0 => 407 / 2
    | 1 => 599588715795707 / 4000000000000
    | 2 => 193894671360731 / 800000000000
    | 3 => 174958491873649 / 4000000000000
    | 4 => 469963119120253 / 4000000000000
    | 5 => 1276041289257801 / 4000000000000
    | 6 => 939926238240913 / 4000000000000
    | 7 => 1610579629755349 / 4000000000000
    | 8 => 1186345665713791 / 4000000000000
    | 9 => 1820159333684593 / 4000000000000
    | 10 => 1050869481270697 / 4000000000000
    | 11 => 1864786335512573 / 4000000000000
    | 12 => 1742325288357137 / 4000000000000
    | 13 => 1243405538564321 / 4000000000000
    | 14 => 1409889357360759 / 4000000000000
    | 15 => 1175418757812871 / 4000000000000
    | 16 => 1038518119402291 / 4000000000000
    | 17 => 301003029190809 / 800000000000
    | 18 => 832590219663323 / 4000000000000
    | 19 => 705795949892803 / 4000000000000
    | 20 => 441654334286209 / 4000000000000
    | 21 => 237523169855103 / 4000000000000
    | 22 => 644921610994309 / 4000000000000
    | 23 => 880585323768293 / 4000000000000
    | 24 => 372345665713791 / 4000000000000
    | 25 => 1513564459113311 / 4000000000000
    | _ => 1010990913960049 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-4540081211 / 1000000000000) (-4540081210 / 1000000000000), orderedInterval (-55736039359 / 1000000000000) (-55736039358 / 1000000000000))
    | 1 => (orderedInterval (-7458791762 / 1000000000000) (-7458791735 / 1000000000000), orderedInterval (64766152823 / 1000000000000) (64766152850 / 1000000000000))
    | 2 => (orderedInterval (-48645816396 / 1000000000000) (-48645816394 / 1000000000000), orderedInterval (-16031673588 / 1000000000000) (-16031673586 / 1000000000000))
    | 3 => (orderedInterval (62011174283 / 1000000000000) (62011174284 / 1000000000000), orderedInterval (102779503147 / 1000000000000) (102779503148 / 1000000000000))
    | 4 => (orderedInterval (-65781253616 / 1000000000000) (-65781242785 / 1000000000000), orderedInterval (33314214414 / 1000000000000) (33314225245 / 1000000000000))
    | 5 => (orderedInterval (-26932556145 / 1000000000000) (-26932548986 / 1000000000000), orderedInterval (35682733128 / 1000000000000) (35682740287 / 1000000000000))
    | 6 => (orderedInterval (-7622660592 / 1000000000000) (-7622660591 / 1000000000000), orderedInterval (-51472942504 / 1000000000000) (-51472942503 / 1000000000000))
    | 7 => (orderedInterval (38378471796 / 1000000000000) (38378471802 / 1000000000000), orderedInterval (10353623642 / 1000000000000) (10353623647 / 1000000000000))
    | 8 => (orderedInterval (40859271841 / 1000000000000) (40859304347 / 1000000000000), orderedInterval (-21909383984 / 1000000000000) (-21909351478 / 1000000000000))
    | 9 => (orderedInterval (-10839760805 / 1000000000000) (-10839760804 / 1000000000000), orderedInterval (-35786722486 / 1000000000000) (-35786722485 / 1000000000000))
    | 10 => (orderedInterval (-18783014590 / 1000000000000) (-18783014036 / 1000000000000), orderedInterval (45537538957 / 1000000000000) (45537539510 / 1000000000000))
    | 11 => (orderedInterval (33190521044 / 1000000000000) (33190571991 / 1000000000000), orderedInterval (-16282094696 / 1000000000000) (-16282043750 / 1000000000000))
    | 12 => (orderedInterval (11842332272 / 1000000000000) (11842332333 / 1000000000000), orderedInterval (-36363291252 / 1000000000000) (-36363291191 / 1000000000000))
    | 13 => (orderedInterval (-26246943583 / 1000000000000) (-26246943582 / 1000000000000), orderedInterval (-36823571176 / 1000000000000) (-36823571175 / 1000000000000))
    | 14 => (orderedInterval (41873290959 / 1000000000000) (41873290976 / 1000000000000), orderedInterval (7205658182 / 1000000000000) (7205658199 / 1000000000000))
    | 15 => (orderedInterval (-28905546206 / 1000000000000) (-28905535948 / 1000000000000), orderedInterval (36530879554 / 1000000000000) (36530889812 / 1000000000000))
    | 16 => (orderedInterval (16408221331 / 1000000000000) (16408221616 / 1000000000000), orderedInterval (-46752100875 / 1000000000000) (-46752100590 / 1000000000000))
    | 17 => (orderedInterval (1962737944 / 1000000000000) (1962737945 / 1000000000000), orderedInterval (41084431098 / 1000000000000) (41084431099 / 1000000000000))
    | 18 => (orderedInterval (55296173386 / 1000000000000) (55296173478 / 1000000000000), orderedInterval (-1042042300 / 1000000000000) (-1042042208 / 1000000000000))
    | 19 => (orderedInterval (57948743187 / 1000000000000) (57948743188 / 1000000000000), orderedInterval (15643524044 / 1000000000000) (15643524046 / 1000000000000))
    | 20 => (orderedInterval (-71867358564 / 1000000000000) (-71867358562 / 1000000000000), orderedInterval (-24185986573 / 1000000000000) (-24185986572 / 1000000000000))
    | 21 => (orderedInterval (-47244773636 / 1000000000000) (-47244773635 / 1000000000000), orderedInterval (-91738660621 / 1000000000000) (-91738660620 / 1000000000000))
    | 22 => (orderedInterval (-61281013497 / 1000000000000) (-61281012507 / 1000000000000), orderedInterval (14087153711 / 1000000000000) (14087154701 / 1000000000000))
    | 23 => (orderedInterval (45813329394 / 1000000000000) (45813329395 / 1000000000000), orderedInterval (28055108049 / 1000000000000) (28055108050 / 1000000000000))
    | 24 => (orderedInterval (-30467424672 / 1000000000000) (-30467423370 / 1000000000000), orderedInterval (77045548519 / 1000000000000) (77045549821 / 1000000000000))
    | 25 => (orderedInterval (33519290627 / 1000000000000) (33519385469 / 1000000000000), orderedInterval (-23685231961 / 1000000000000) (-23685137119 / 1000000000000))
    | _ => (orderedInterval (40421684789 / 1000000000000) (40421778715 / 1000000000000), orderedInterval (-29826895630 / 1000000000000) (-29826801703 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-4723622696 / 1000000000000) (-4723622681 / 1000000000000)
      | 1 => orderedInterval (-1159940473 / 1000000000000) (-1159939543 / 1000000000000)
      | 2 => orderedInterval (-196257644 / 1000000000000) (-196256846 / 1000000000000)
      | 3 => orderedInterval (5252655884 / 1000000000000) (5252663249 / 1000000000000)
      | 4 => orderedInterval (-2907679837 / 1000000000000) (-2907679811 / 1000000000000)
      | 5 => orderedInterval (-1222525873 / 1000000000000) (-1222525718 / 1000000000000)
      | 6 => orderedInterval (-14460997885 / 1000000000000) (-14460997819 / 1000000000000)
      | 7 => orderedInterval (-1248427661 / 1000000000000) (-1248427614 / 1000000000000)
      | _ => orderedInterval (-10496403154 / 1000000000000) (-10496377746 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-22767723952 / 1000000000000) (-22767723934 / 1000000000000)
      | 1 => orderedInterval (-3513942125 / 1000000000000) (-3513941070 / 1000000000000)
      | 2 => orderedInterval (-1403577284 / 1000000000000) (-1403576118 / 1000000000000)
      | 3 => orderedInterval (13272132309 / 1000000000000) (13272149121 / 1000000000000)
      | 4 => orderedInterval (-3977079701 / 1000000000000) (-3977079659 / 1000000000000)
      | 5 => orderedInterval (5967480083 / 1000000000000) (5967480304 / 1000000000000)
      | 6 => orderedInterval (-1024516540 / 1000000000000) (-1024516477 / 1000000000000)
      | 7 => orderedInterval (-2084906110 / 1000000000000) (-2084906070 / 1000000000000)
      | _ => orderedInterval (10748054744 / 1000000000000) (10748091071 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (5998298656 / 1000000000000) (5998298676 / 1000000000000)
      | 1 => orderedInterval (-3856108873 / 1000000000000) (-3856107447 / 1000000000000)
      | 2 => orderedInterval (2543569952 / 1000000000000) (2543571663 / 1000000000000)
      | 3 => orderedInterval (-32138432147 / 1000000000000) (-32138393628 / 1000000000000)
      | 4 => orderedInterval (7426039719 / 1000000000000) (7426039790 / 1000000000000)
      | 5 => orderedInterval (2023296438 / 1000000000000) (2023296755 / 1000000000000)
      | 6 => orderedInterval (12409558583 / 1000000000000) (12409558644 / 1000000000000)
      | 7 => orderedInterval (3172254258 / 1000000000000) (3172254294 / 1000000000000)
      | _ => orderedInterval (21118458259 / 1000000000000) (21118512433 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (23409920326 / 1000000000000) (23409920349 / 1000000000000)
      | 1 => orderedInterval (9567891392 / 1000000000000) (9567893494 / 1000000000000)
      | 2 => orderedInterval (4100304202 / 1000000000000) (4100306708 / 1000000000000)
      | 3 => orderedInterval (-50367290146 / 1000000000000) (-50367202010 / 1000000000000)
      | 4 => orderedInterval (6126353465 / 1000000000000) (6126353587 / 1000000000000)
      | 5 => orderedInterval (-13484695903 / 1000000000000) (-13484695445 / 1000000000000)
      | 6 => orderedInterval (463651515 / 1000000000000) (463651575 / 1000000000000)
      | 7 => orderedInterval (2823306411 / 1000000000000) (2823306445 / 1000000000000)
      | _ => orderedInterval (-23264692695 / 1000000000000) (-23264608854 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-7793590847 / 1000000000000) (-7793590821 / 1000000000000)
      | 1 => orderedInterval (11199894897 / 1000000000000) (11199898123 / 1000000000000)
      | 2 => orderedInterval (-13727097642 / 1000000000000) (-13727093951 / 1000000000000)
      | 3 => orderedInterval (174737241925 / 1000000000000) (174737444122 / 1000000000000)
      | 4 => orderedInterval (-19967729874 / 1000000000000) (-19967729657 / 1000000000000)
      | 5 => orderedInterval (-3219247112 / 1000000000000) (-3219246447 / 1000000000000)
      | 6 => orderedInterval (-11738107891 / 1000000000000) (-11738107831 / 1000000000000)
      | 7 => orderedInterval (-4282251100 / 1000000000000) (-4282251066 / 1000000000000)
      | _ => orderedInterval (-50442121034 / 1000000000000) (-50441985706 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-31163199339 / 1000000000000) (-31163164529 / 1000000000000)
    | 1 => orderedInterval (-4784078576 / 1000000000000) (-4784022832 / 1000000000000)
    | 2 => orderedInterval (18696934845 / 1000000000000) (18697031180 / 1000000000000)
    | 3 => orderedInterval (-40625251433 / 1000000000000) (-40625074151 / 1000000000000)
    | _ => orderedInterval (74766991322 / 1000000000000) (74767336766 / 1000000000000)

theorem compactCertificate331_stateChecks0 :
    compactCertificate331.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 65 12 (407 / 2)) (orderedInterval (-4540081211 / 1000000000000) (-4540081210 / 1000000000000), orderedInterval (-55736039359 / 1000000000000) (-55736039358 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 48 12 (599588715795707 / 4000000000000)) (orderedInterval (-7458791762 / 1000000000000) (-7458791735 / 1000000000000), orderedInterval (64766152823 / 1000000000000) (64766152850 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 77 12 (193894671360731 / 800000000000)) (orderedInterval (-48645816396 / 1000000000000) (-48645816394 / 1000000000000), orderedInterval (-16031673588 / 1000000000000) (-16031673586 / 1000000000000))) = true
  rfl'

theorem compactCertificate331_stateChecks1 :
    compactCertificate331.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 14 12 (174958491873649 / 4000000000000)) (orderedInterval (62011174283 / 1000000000000) (62011174284 / 1000000000000), orderedInterval (102779503147 / 1000000000000) (102779503148 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (469963119120253 / 4000000000000)) (orderedInterval (-65781253616 / 1000000000000) (-65781242785 / 1000000000000), orderedInterval (33314214414 / 1000000000000) (33314225245 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 102 12 (1276041289257801 / 4000000000000)) (orderedInterval (-26932556145 / 1000000000000) (-26932548986 / 1000000000000), orderedInterval (35682733128 / 1000000000000) (35682740287 / 1000000000000))) = true
  rfl'

theorem compactCertificate331_stateChecks2 :
    compactCertificate331.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 75 12 (939926238240913 / 4000000000000)) (orderedInterval (-7622660592 / 1000000000000) (-7622660591 / 1000000000000), orderedInterval (-51472942504 / 1000000000000) (-51472942503 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 128 12 (1610579629755349 / 4000000000000)) (orderedInterval (38378471796 / 1000000000000) (38378471802 / 1000000000000), orderedInterval (10353623642 / 1000000000000) (10353623647 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 94 12 (1186345665713791 / 4000000000000)) (orderedInterval (40859271841 / 1000000000000) (40859304347 / 1000000000000), orderedInterval (-21909383984 / 1000000000000) (-21909351478 / 1000000000000))) = true
  rfl'

theorem compactCertificate331_stateChecks3 :
    compactCertificate331.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 145 12 (1820159333684593 / 4000000000000)) (orderedInterval (-10839760805 / 1000000000000) (-10839760804 / 1000000000000), orderedInterval (-35786722486 / 1000000000000) (-35786722485 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 84 12 (1050869481270697 / 4000000000000)) (orderedInterval (-18783014590 / 1000000000000) (-18783014036 / 1000000000000), orderedInterval (45537538957 / 1000000000000) (45537539510 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 148 12 (1864786335512573 / 4000000000000)) (orderedInterval (33190521044 / 1000000000000) (33190571991 / 1000000000000), orderedInterval (-16282094696 / 1000000000000) (-16282043750 / 1000000000000))) = true
  rfl'

theorem compactCertificate331_stateChecks4 :
    compactCertificate331.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 139 12 (1742325288357137 / 4000000000000)) (orderedInterval (11842332272 / 1000000000000) (11842332333 / 1000000000000), orderedInterval (-36363291252 / 1000000000000) (-36363291191 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 99 12 (1243405538564321 / 4000000000000)) (orderedInterval (-26246943583 / 1000000000000) (-26246943582 / 1000000000000), orderedInterval (-36823571176 / 1000000000000) (-36823571175 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 112 12 (1409889357360759 / 4000000000000)) (orderedInterval (41873290959 / 1000000000000) (41873290976 / 1000000000000), orderedInterval (7205658182 / 1000000000000) (7205658199 / 1000000000000))) = true
  rfl'

theorem compactCertificate331_stateChecks5 :
    compactCertificate331.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 94 12 (1175418757812871 / 4000000000000)) (orderedInterval (-28905546206 / 1000000000000) (-28905535948 / 1000000000000), orderedInterval (36530879554 / 1000000000000) (36530889812 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 83 12 (1038518119402291 / 4000000000000)) (orderedInterval (16408221331 / 1000000000000) (16408221616 / 1000000000000), orderedInterval (-46752100875 / 1000000000000) (-46752100590 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 120 12 (301003029190809 / 800000000000)) (orderedInterval (1962737944 / 1000000000000) (1962737945 / 1000000000000), orderedInterval (41084431098 / 1000000000000) (41084431099 / 1000000000000))) = true
  rfl'

theorem compactCertificate331_stateChecks6 :
    compactCertificate331.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (832590219663323 / 4000000000000)) (orderedInterval (55296173386 / 1000000000000) (55296173478 / 1000000000000), orderedInterval (-1042042300 / 1000000000000) (-1042042208 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 56 12 (705795949892803 / 4000000000000)) (orderedInterval (57948743187 / 1000000000000) (57948743188 / 1000000000000), orderedInterval (15643524044 / 1000000000000) (15643524046 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 35 12 (441654334286209 / 4000000000000)) (orderedInterval (-71867358564 / 1000000000000) (-71867358562 / 1000000000000), orderedInterval (-24185986573 / 1000000000000) (-24185986572 / 1000000000000))) = true
  rfl'

theorem compactCertificate331_stateChecks7 :
    compactCertificate331.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 19 12 (237523169855103 / 4000000000000)) (orderedInterval (-47244773636 / 1000000000000) (-47244773635 / 1000000000000), orderedInterval (-91738660621 / 1000000000000) (-91738660620 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (644921610994309 / 4000000000000)) (orderedInterval (-61281013497 / 1000000000000) (-61281012507 / 1000000000000), orderedInterval (14087153711 / 1000000000000) (14087154701 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (880585323768293 / 4000000000000)) (orderedInterval (45813329394 / 1000000000000) (45813329395 / 1000000000000), orderedInterval (28055108049 / 1000000000000) (28055108050 / 1000000000000))) = true
  rfl'

theorem compactCertificate331_stateChecks8 :
    compactCertificate331.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (372345665713791 / 4000000000000)) (orderedInterval (-30467424672 / 1000000000000) (-30467423370 / 1000000000000), orderedInterval (77045548519 / 1000000000000) (77045549821 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 121 12 (1513564459113311 / 4000000000000)) (orderedInterval (33519290627 / 1000000000000) (33519385469 / 1000000000000), orderedInterval (-23685231961 / 1000000000000) (-23685137119 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 80 12 (1010990913960049 / 4000000000000)) (orderedInterval (40421684789 / 1000000000000) (40421778715 / 1000000000000), orderedInterval (-29826895630 / 1000000000000) (-29826801703 / 1000000000000))) = true
  rfl'

theorem compactCertificate331_states : ∀ j,
    BesselStateValid (compactCertificate331.point j) (compactCertificate331.state j) :=
  compactCertificate331.statesValid_of_checks3 compactCertificate331_stateChecks0
    compactCertificate331_stateChecks1 compactCertificate331_stateChecks2
    compactCertificate331_stateChecks3 compactCertificate331_stateChecks4
    compactCertificate331_stateChecks5 compactCertificate331_stateChecks6
    compactCertificate331_stateChecks7 compactCertificate331_stateChecks8

theorem compactCertificate331_chunkChecks0_0 :
    compactCertificate331.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (407 / 2) 0 (IntervalRat.scale (407 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-4540081211 / 1000000000000) (-4540081210 / 1000000000000), orderedInterval (-55736039359 / 1000000000000) (-55736039358 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (599588715795707 / 4000000000000) 0 (IntervalRat.scale (407 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-7458791762 / 1000000000000) (-7458791735 / 1000000000000), orderedInterval (64766152823 / 1000000000000) (64766152850 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (193894671360731 / 800000000000) 0 (IntervalRat.scale (407 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-48645816396 / 1000000000000) (-48645816394 / 1000000000000), orderedInterval (-16031673588 / 1000000000000) (-16031673586 / 1000000000000)))) (orderedInterval (-4723622696 / 1000000000000) (-4723622681 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (174958491873649 / 4000000000000) 0 (IntervalRat.scale (407 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (62011174283 / 1000000000000) (62011174284 / 1000000000000), orderedInterval (102779503147 / 1000000000000) (102779503148 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (469963119120253 / 4000000000000) 0 (IntervalRat.scale (407 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-65781253616 / 1000000000000) (-65781242785 / 1000000000000), orderedInterval (33314214414 / 1000000000000) (33314225245 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1276041289257801 / 4000000000000) 0 (IntervalRat.scale (407 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-26932556145 / 1000000000000) (-26932548986 / 1000000000000), orderedInterval (35682733128 / 1000000000000) (35682740287 / 1000000000000)))) (orderedInterval (-1159940473 / 1000000000000) (-1159939543 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (939926238240913 / 4000000000000) 0 (IntervalRat.scale (407 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-7622660592 / 1000000000000) (-7622660591 / 1000000000000), orderedInterval (-51472942504 / 1000000000000) (-51472942503 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1610579629755349 / 4000000000000) 0 (IntervalRat.scale (407 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (38378471796 / 1000000000000) (38378471802 / 1000000000000), orderedInterval (10353623642 / 1000000000000) (10353623647 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1186345665713791 / 4000000000000) 0 (IntervalRat.scale (407 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (40859271841 / 1000000000000) (40859304347 / 1000000000000), orderedInterval (-21909383984 / 1000000000000) (-21909351478 / 1000000000000)))) (orderedInterval (-196257644 / 1000000000000) (-196256846 / 1000000000000))) = true
  rfl'

theorem compactCertificate331_chunkChecks0_1 :
    compactCertificate331.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1820159333684593 / 4000000000000) 0 (IntervalRat.scale (407 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-10839760805 / 1000000000000) (-10839760804 / 1000000000000), orderedInterval (-35786722486 / 1000000000000) (-35786722485 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1050869481270697 / 4000000000000) 0 (IntervalRat.scale (407 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-18783014590 / 1000000000000) (-18783014036 / 1000000000000), orderedInterval (45537538957 / 1000000000000) (45537539510 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1864786335512573 / 4000000000000) 0 (IntervalRat.scale (407 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (33190521044 / 1000000000000) (33190571991 / 1000000000000), orderedInterval (-16282094696 / 1000000000000) (-16282043750 / 1000000000000)))) (orderedInterval (5252655884 / 1000000000000) (5252663249 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1742325288357137 / 4000000000000) 0 (IntervalRat.scale (407 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (11842332272 / 1000000000000) (11842332333 / 1000000000000), orderedInterval (-36363291252 / 1000000000000) (-36363291191 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1243405538564321 / 4000000000000) 0 (IntervalRat.scale (407 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-26246943583 / 1000000000000) (-26246943582 / 1000000000000), orderedInterval (-36823571176 / 1000000000000) (-36823571175 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1409889357360759 / 4000000000000) 0 (IntervalRat.scale (407 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (41873290959 / 1000000000000) (41873290976 / 1000000000000), orderedInterval (7205658182 / 1000000000000) (7205658199 / 1000000000000)))) (orderedInterval (-2907679837 / 1000000000000) (-2907679811 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1175418757812871 / 4000000000000) 0 (IntervalRat.scale (407 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-28905546206 / 1000000000000) (-28905535948 / 1000000000000), orderedInterval (36530879554 / 1000000000000) (36530889812 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1038518119402291 / 4000000000000) 0 (IntervalRat.scale (407 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (16408221331 / 1000000000000) (16408221616 / 1000000000000), orderedInterval (-46752100875 / 1000000000000) (-46752100590 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (301003029190809 / 800000000000) 0 (IntervalRat.scale (407 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (1962737944 / 1000000000000) (1962737945 / 1000000000000), orderedInterval (41084431098 / 1000000000000) (41084431099 / 1000000000000)))) (orderedInterval (-1222525873 / 1000000000000) (-1222525718 / 1000000000000))) = true
  rfl'

theorem compactCertificate331_chunkChecks0_2 :
    compactCertificate331.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (832590219663323 / 4000000000000) 0 (IntervalRat.scale (407 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (55296173386 / 1000000000000) (55296173478 / 1000000000000), orderedInterval (-1042042300 / 1000000000000) (-1042042208 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (705795949892803 / 4000000000000) 0 (IntervalRat.scale (407 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (57948743187 / 1000000000000) (57948743188 / 1000000000000), orderedInterval (15643524044 / 1000000000000) (15643524046 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (441654334286209 / 4000000000000) 0 (IntervalRat.scale (407 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-71867358564 / 1000000000000) (-71867358562 / 1000000000000), orderedInterval (-24185986573 / 1000000000000) (-24185986572 / 1000000000000)))) (orderedInterval (-14460997885 / 1000000000000) (-14460997819 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (237523169855103 / 4000000000000) 0 (IntervalRat.scale (407 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-47244773636 / 1000000000000) (-47244773635 / 1000000000000), orderedInterval (-91738660621 / 1000000000000) (-91738660620 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (644921610994309 / 4000000000000) 0 (IntervalRat.scale (407 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-61281013497 / 1000000000000) (-61281012507 / 1000000000000), orderedInterval (14087153711 / 1000000000000) (14087154701 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (880585323768293 / 4000000000000) 0 (IntervalRat.scale (407 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (45813329394 / 1000000000000) (45813329395 / 1000000000000), orderedInterval (28055108049 / 1000000000000) (28055108050 / 1000000000000)))) (orderedInterval (-1248427661 / 1000000000000) (-1248427614 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (372345665713791 / 4000000000000) 0 (IntervalRat.scale (407 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-30467424672 / 1000000000000) (-30467423370 / 1000000000000), orderedInterval (77045548519 / 1000000000000) (77045549821 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1513564459113311 / 4000000000000) 0 (IntervalRat.scale (407 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (33519290627 / 1000000000000) (33519385469 / 1000000000000), orderedInterval (-23685231961 / 1000000000000) (-23685137119 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1010990913960049 / 4000000000000) 0 (IntervalRat.scale (407 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (40421684789 / 1000000000000) (40421778715 / 1000000000000), orderedInterval (-29826895630 / 1000000000000) (-29826801703 / 1000000000000)))) (orderedInterval (-10496403154 / 1000000000000) (-10496377746 / 1000000000000))) = true
  rfl'

theorem compactCertificate331_chunkChecks0 :
    compactCertificate331.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate331.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate331_chunkChecks0_0
    compactCertificate331_chunkChecks0_1 compactCertificate331_chunkChecks0_2

theorem compactCertificate331_chunkChecks1_0 :
    compactCertificate331.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (407 / 2) 1 (IntervalRat.scale (407 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-4540081211 / 1000000000000) (-4540081210 / 1000000000000), orderedInterval (-55736039359 / 1000000000000) (-55736039358 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (599588715795707 / 4000000000000) 1 (IntervalRat.scale (407 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-7458791762 / 1000000000000) (-7458791735 / 1000000000000), orderedInterval (64766152823 / 1000000000000) (64766152850 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (193894671360731 / 800000000000) 1 (IntervalRat.scale (407 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-48645816396 / 1000000000000) (-48645816394 / 1000000000000), orderedInterval (-16031673588 / 1000000000000) (-16031673586 / 1000000000000)))) (orderedInterval (-22767723952 / 1000000000000) (-22767723934 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (174958491873649 / 4000000000000) 1 (IntervalRat.scale (407 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (62011174283 / 1000000000000) (62011174284 / 1000000000000), orderedInterval (102779503147 / 1000000000000) (102779503148 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (469963119120253 / 4000000000000) 1 (IntervalRat.scale (407 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-65781253616 / 1000000000000) (-65781242785 / 1000000000000), orderedInterval (33314214414 / 1000000000000) (33314225245 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1276041289257801 / 4000000000000) 1 (IntervalRat.scale (407 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-26932556145 / 1000000000000) (-26932548986 / 1000000000000), orderedInterval (35682733128 / 1000000000000) (35682740287 / 1000000000000)))) (orderedInterval (-3513942125 / 1000000000000) (-3513941070 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (939926238240913 / 4000000000000) 1 (IntervalRat.scale (407 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-7622660592 / 1000000000000) (-7622660591 / 1000000000000), orderedInterval (-51472942504 / 1000000000000) (-51472942503 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1610579629755349 / 4000000000000) 1 (IntervalRat.scale (407 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (38378471796 / 1000000000000) (38378471802 / 1000000000000), orderedInterval (10353623642 / 1000000000000) (10353623647 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1186345665713791 / 4000000000000) 1 (IntervalRat.scale (407 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (40859271841 / 1000000000000) (40859304347 / 1000000000000), orderedInterval (-21909383984 / 1000000000000) (-21909351478 / 1000000000000)))) (orderedInterval (-1403577284 / 1000000000000) (-1403576118 / 1000000000000))) = true
  rfl'

theorem compactCertificate331_chunkChecks1_1 :
    compactCertificate331.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1820159333684593 / 4000000000000) 1 (IntervalRat.scale (407 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-10839760805 / 1000000000000) (-10839760804 / 1000000000000), orderedInterval (-35786722486 / 1000000000000) (-35786722485 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1050869481270697 / 4000000000000) 1 (IntervalRat.scale (407 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-18783014590 / 1000000000000) (-18783014036 / 1000000000000), orderedInterval (45537538957 / 1000000000000) (45537539510 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1864786335512573 / 4000000000000) 1 (IntervalRat.scale (407 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (33190521044 / 1000000000000) (33190571991 / 1000000000000), orderedInterval (-16282094696 / 1000000000000) (-16282043750 / 1000000000000)))) (orderedInterval (13272132309 / 1000000000000) (13272149121 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1742325288357137 / 4000000000000) 1 (IntervalRat.scale (407 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (11842332272 / 1000000000000) (11842332333 / 1000000000000), orderedInterval (-36363291252 / 1000000000000) (-36363291191 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1243405538564321 / 4000000000000) 1 (IntervalRat.scale (407 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-26246943583 / 1000000000000) (-26246943582 / 1000000000000), orderedInterval (-36823571176 / 1000000000000) (-36823571175 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1409889357360759 / 4000000000000) 1 (IntervalRat.scale (407 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (41873290959 / 1000000000000) (41873290976 / 1000000000000), orderedInterval (7205658182 / 1000000000000) (7205658199 / 1000000000000)))) (orderedInterval (-3977079701 / 1000000000000) (-3977079659 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1175418757812871 / 4000000000000) 1 (IntervalRat.scale (407 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-28905546206 / 1000000000000) (-28905535948 / 1000000000000), orderedInterval (36530879554 / 1000000000000) (36530889812 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1038518119402291 / 4000000000000) 1 (IntervalRat.scale (407 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (16408221331 / 1000000000000) (16408221616 / 1000000000000), orderedInterval (-46752100875 / 1000000000000) (-46752100590 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (301003029190809 / 800000000000) 1 (IntervalRat.scale (407 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (1962737944 / 1000000000000) (1962737945 / 1000000000000), orderedInterval (41084431098 / 1000000000000) (41084431099 / 1000000000000)))) (orderedInterval (5967480083 / 1000000000000) (5967480304 / 1000000000000))) = true
  rfl'

theorem compactCertificate331_chunkChecks1_2 :
    compactCertificate331.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (832590219663323 / 4000000000000) 1 (IntervalRat.scale (407 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (55296173386 / 1000000000000) (55296173478 / 1000000000000), orderedInterval (-1042042300 / 1000000000000) (-1042042208 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (705795949892803 / 4000000000000) 1 (IntervalRat.scale (407 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (57948743187 / 1000000000000) (57948743188 / 1000000000000), orderedInterval (15643524044 / 1000000000000) (15643524046 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (441654334286209 / 4000000000000) 1 (IntervalRat.scale (407 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-71867358564 / 1000000000000) (-71867358562 / 1000000000000), orderedInterval (-24185986573 / 1000000000000) (-24185986572 / 1000000000000)))) (orderedInterval (-1024516540 / 1000000000000) (-1024516477 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (237523169855103 / 4000000000000) 1 (IntervalRat.scale (407 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-47244773636 / 1000000000000) (-47244773635 / 1000000000000), orderedInterval (-91738660621 / 1000000000000) (-91738660620 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (644921610994309 / 4000000000000) 1 (IntervalRat.scale (407 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-61281013497 / 1000000000000) (-61281012507 / 1000000000000), orderedInterval (14087153711 / 1000000000000) (14087154701 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (880585323768293 / 4000000000000) 1 (IntervalRat.scale (407 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (45813329394 / 1000000000000) (45813329395 / 1000000000000), orderedInterval (28055108049 / 1000000000000) (28055108050 / 1000000000000)))) (orderedInterval (-2084906110 / 1000000000000) (-2084906070 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (372345665713791 / 4000000000000) 1 (IntervalRat.scale (407 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-30467424672 / 1000000000000) (-30467423370 / 1000000000000), orderedInterval (77045548519 / 1000000000000) (77045549821 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1513564459113311 / 4000000000000) 1 (IntervalRat.scale (407 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (33519290627 / 1000000000000) (33519385469 / 1000000000000), orderedInterval (-23685231961 / 1000000000000) (-23685137119 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1010990913960049 / 4000000000000) 1 (IntervalRat.scale (407 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (40421684789 / 1000000000000) (40421778715 / 1000000000000), orderedInterval (-29826895630 / 1000000000000) (-29826801703 / 1000000000000)))) (orderedInterval (10748054744 / 1000000000000) (10748091071 / 1000000000000))) = true
  rfl'

theorem compactCertificate331_chunkChecks1 :
    compactCertificate331.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate331.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate331_chunkChecks1_0
    compactCertificate331_chunkChecks1_1 compactCertificate331_chunkChecks1_2

theorem compactCertificate331_chunkChecks2_0 :
    compactCertificate331.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (407 / 2) 2 (IntervalRat.scale (407 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-4540081211 / 1000000000000) (-4540081210 / 1000000000000), orderedInterval (-55736039359 / 1000000000000) (-55736039358 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (599588715795707 / 4000000000000) 2 (IntervalRat.scale (407 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-7458791762 / 1000000000000) (-7458791735 / 1000000000000), orderedInterval (64766152823 / 1000000000000) (64766152850 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (193894671360731 / 800000000000) 2 (IntervalRat.scale (407 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-48645816396 / 1000000000000) (-48645816394 / 1000000000000), orderedInterval (-16031673588 / 1000000000000) (-16031673586 / 1000000000000)))) (orderedInterval (5998298656 / 1000000000000) (5998298676 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (174958491873649 / 4000000000000) 2 (IntervalRat.scale (407 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (62011174283 / 1000000000000) (62011174284 / 1000000000000), orderedInterval (102779503147 / 1000000000000) (102779503148 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (469963119120253 / 4000000000000) 2 (IntervalRat.scale (407 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-65781253616 / 1000000000000) (-65781242785 / 1000000000000), orderedInterval (33314214414 / 1000000000000) (33314225245 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1276041289257801 / 4000000000000) 2 (IntervalRat.scale (407 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-26932556145 / 1000000000000) (-26932548986 / 1000000000000), orderedInterval (35682733128 / 1000000000000) (35682740287 / 1000000000000)))) (orderedInterval (-3856108873 / 1000000000000) (-3856107447 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (939926238240913 / 4000000000000) 2 (IntervalRat.scale (407 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-7622660592 / 1000000000000) (-7622660591 / 1000000000000), orderedInterval (-51472942504 / 1000000000000) (-51472942503 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1610579629755349 / 4000000000000) 2 (IntervalRat.scale (407 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (38378471796 / 1000000000000) (38378471802 / 1000000000000), orderedInterval (10353623642 / 1000000000000) (10353623647 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1186345665713791 / 4000000000000) 2 (IntervalRat.scale (407 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (40859271841 / 1000000000000) (40859304347 / 1000000000000), orderedInterval (-21909383984 / 1000000000000) (-21909351478 / 1000000000000)))) (orderedInterval (2543569952 / 1000000000000) (2543571663 / 1000000000000))) = true
  rfl'

theorem compactCertificate331_chunkChecks2_1 :
    compactCertificate331.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1820159333684593 / 4000000000000) 2 (IntervalRat.scale (407 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-10839760805 / 1000000000000) (-10839760804 / 1000000000000), orderedInterval (-35786722486 / 1000000000000) (-35786722485 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1050869481270697 / 4000000000000) 2 (IntervalRat.scale (407 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-18783014590 / 1000000000000) (-18783014036 / 1000000000000), orderedInterval (45537538957 / 1000000000000) (45537539510 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1864786335512573 / 4000000000000) 2 (IntervalRat.scale (407 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (33190521044 / 1000000000000) (33190571991 / 1000000000000), orderedInterval (-16282094696 / 1000000000000) (-16282043750 / 1000000000000)))) (orderedInterval (-32138432147 / 1000000000000) (-32138393628 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1742325288357137 / 4000000000000) 2 (IntervalRat.scale (407 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (11842332272 / 1000000000000) (11842332333 / 1000000000000), orderedInterval (-36363291252 / 1000000000000) (-36363291191 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1243405538564321 / 4000000000000) 2 (IntervalRat.scale (407 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-26246943583 / 1000000000000) (-26246943582 / 1000000000000), orderedInterval (-36823571176 / 1000000000000) (-36823571175 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1409889357360759 / 4000000000000) 2 (IntervalRat.scale (407 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (41873290959 / 1000000000000) (41873290976 / 1000000000000), orderedInterval (7205658182 / 1000000000000) (7205658199 / 1000000000000)))) (orderedInterval (7426039719 / 1000000000000) (7426039790 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1175418757812871 / 4000000000000) 2 (IntervalRat.scale (407 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-28905546206 / 1000000000000) (-28905535948 / 1000000000000), orderedInterval (36530879554 / 1000000000000) (36530889812 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1038518119402291 / 4000000000000) 2 (IntervalRat.scale (407 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (16408221331 / 1000000000000) (16408221616 / 1000000000000), orderedInterval (-46752100875 / 1000000000000) (-46752100590 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (301003029190809 / 800000000000) 2 (IntervalRat.scale (407 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (1962737944 / 1000000000000) (1962737945 / 1000000000000), orderedInterval (41084431098 / 1000000000000) (41084431099 / 1000000000000)))) (orderedInterval (2023296438 / 1000000000000) (2023296755 / 1000000000000))) = true
  rfl'

theorem compactCertificate331_chunkChecks2_2 :
    compactCertificate331.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (832590219663323 / 4000000000000) 2 (IntervalRat.scale (407 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (55296173386 / 1000000000000) (55296173478 / 1000000000000), orderedInterval (-1042042300 / 1000000000000) (-1042042208 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (705795949892803 / 4000000000000) 2 (IntervalRat.scale (407 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (57948743187 / 1000000000000) (57948743188 / 1000000000000), orderedInterval (15643524044 / 1000000000000) (15643524046 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (441654334286209 / 4000000000000) 2 (IntervalRat.scale (407 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-71867358564 / 1000000000000) (-71867358562 / 1000000000000), orderedInterval (-24185986573 / 1000000000000) (-24185986572 / 1000000000000)))) (orderedInterval (12409558583 / 1000000000000) (12409558644 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (237523169855103 / 4000000000000) 2 (IntervalRat.scale (407 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-47244773636 / 1000000000000) (-47244773635 / 1000000000000), orderedInterval (-91738660621 / 1000000000000) (-91738660620 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (644921610994309 / 4000000000000) 2 (IntervalRat.scale (407 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-61281013497 / 1000000000000) (-61281012507 / 1000000000000), orderedInterval (14087153711 / 1000000000000) (14087154701 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (880585323768293 / 4000000000000) 2 (IntervalRat.scale (407 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (45813329394 / 1000000000000) (45813329395 / 1000000000000), orderedInterval (28055108049 / 1000000000000) (28055108050 / 1000000000000)))) (orderedInterval (3172254258 / 1000000000000) (3172254294 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (372345665713791 / 4000000000000) 2 (IntervalRat.scale (407 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-30467424672 / 1000000000000) (-30467423370 / 1000000000000), orderedInterval (77045548519 / 1000000000000) (77045549821 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1513564459113311 / 4000000000000) 2 (IntervalRat.scale (407 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (33519290627 / 1000000000000) (33519385469 / 1000000000000), orderedInterval (-23685231961 / 1000000000000) (-23685137119 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1010990913960049 / 4000000000000) 2 (IntervalRat.scale (407 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (40421684789 / 1000000000000) (40421778715 / 1000000000000), orderedInterval (-29826895630 / 1000000000000) (-29826801703 / 1000000000000)))) (orderedInterval (21118458259 / 1000000000000) (21118512433 / 1000000000000))) = true
  rfl'

theorem compactCertificate331_chunkChecks2 :
    compactCertificate331.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate331.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate331_chunkChecks2_0
    compactCertificate331_chunkChecks2_1 compactCertificate331_chunkChecks2_2

theorem compactCertificate331_chunkChecks3_0 :
    compactCertificate331.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (407 / 2) 3 (IntervalRat.scale (407 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-4540081211 / 1000000000000) (-4540081210 / 1000000000000), orderedInterval (-55736039359 / 1000000000000) (-55736039358 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (599588715795707 / 4000000000000) 3 (IntervalRat.scale (407 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-7458791762 / 1000000000000) (-7458791735 / 1000000000000), orderedInterval (64766152823 / 1000000000000) (64766152850 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (193894671360731 / 800000000000) 3 (IntervalRat.scale (407 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-48645816396 / 1000000000000) (-48645816394 / 1000000000000), orderedInterval (-16031673588 / 1000000000000) (-16031673586 / 1000000000000)))) (orderedInterval (23409920326 / 1000000000000) (23409920349 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (174958491873649 / 4000000000000) 3 (IntervalRat.scale (407 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (62011174283 / 1000000000000) (62011174284 / 1000000000000), orderedInterval (102779503147 / 1000000000000) (102779503148 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (469963119120253 / 4000000000000) 3 (IntervalRat.scale (407 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-65781253616 / 1000000000000) (-65781242785 / 1000000000000), orderedInterval (33314214414 / 1000000000000) (33314225245 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1276041289257801 / 4000000000000) 3 (IntervalRat.scale (407 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-26932556145 / 1000000000000) (-26932548986 / 1000000000000), orderedInterval (35682733128 / 1000000000000) (35682740287 / 1000000000000)))) (orderedInterval (9567891392 / 1000000000000) (9567893494 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (939926238240913 / 4000000000000) 3 (IntervalRat.scale (407 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-7622660592 / 1000000000000) (-7622660591 / 1000000000000), orderedInterval (-51472942504 / 1000000000000) (-51472942503 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1610579629755349 / 4000000000000) 3 (IntervalRat.scale (407 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (38378471796 / 1000000000000) (38378471802 / 1000000000000), orderedInterval (10353623642 / 1000000000000) (10353623647 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1186345665713791 / 4000000000000) 3 (IntervalRat.scale (407 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (40859271841 / 1000000000000) (40859304347 / 1000000000000), orderedInterval (-21909383984 / 1000000000000) (-21909351478 / 1000000000000)))) (orderedInterval (4100304202 / 1000000000000) (4100306708 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate331_chunkChecks3_1 :
    compactCertificate331.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1820159333684593 / 4000000000000) 3 (IntervalRat.scale (407 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-10839760805 / 1000000000000) (-10839760804 / 1000000000000), orderedInterval (-35786722486 / 1000000000000) (-35786722485 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1050869481270697 / 4000000000000) 3 (IntervalRat.scale (407 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-18783014590 / 1000000000000) (-18783014036 / 1000000000000), orderedInterval (45537538957 / 1000000000000) (45537539510 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1864786335512573 / 4000000000000) 3 (IntervalRat.scale (407 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (33190521044 / 1000000000000) (33190571991 / 1000000000000), orderedInterval (-16282094696 / 1000000000000) (-16282043750 / 1000000000000)))) (orderedInterval (-50367290146 / 1000000000000) (-50367202010 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1742325288357137 / 4000000000000) 3 (IntervalRat.scale (407 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (11842332272 / 1000000000000) (11842332333 / 1000000000000), orderedInterval (-36363291252 / 1000000000000) (-36363291191 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1243405538564321 / 4000000000000) 3 (IntervalRat.scale (407 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-26246943583 / 1000000000000) (-26246943582 / 1000000000000), orderedInterval (-36823571176 / 1000000000000) (-36823571175 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1409889357360759 / 4000000000000) 3 (IntervalRat.scale (407 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (41873290959 / 1000000000000) (41873290976 / 1000000000000), orderedInterval (7205658182 / 1000000000000) (7205658199 / 1000000000000)))) (orderedInterval (6126353465 / 1000000000000) (6126353587 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1175418757812871 / 4000000000000) 3 (IntervalRat.scale (407 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-28905546206 / 1000000000000) (-28905535948 / 1000000000000), orderedInterval (36530879554 / 1000000000000) (36530889812 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1038518119402291 / 4000000000000) 3 (IntervalRat.scale (407 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (16408221331 / 1000000000000) (16408221616 / 1000000000000), orderedInterval (-46752100875 / 1000000000000) (-46752100590 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (301003029190809 / 800000000000) 3 (IntervalRat.scale (407 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (1962737944 / 1000000000000) (1962737945 / 1000000000000), orderedInterval (41084431098 / 1000000000000) (41084431099 / 1000000000000)))) (orderedInterval (-13484695903 / 1000000000000) (-13484695445 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate331_chunkChecks3_2 :
    compactCertificate331.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (832590219663323 / 4000000000000) 3 (IntervalRat.scale (407 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (55296173386 / 1000000000000) (55296173478 / 1000000000000), orderedInterval (-1042042300 / 1000000000000) (-1042042208 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (705795949892803 / 4000000000000) 3 (IntervalRat.scale (407 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (57948743187 / 1000000000000) (57948743188 / 1000000000000), orderedInterval (15643524044 / 1000000000000) (15643524046 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (441654334286209 / 4000000000000) 3 (IntervalRat.scale (407 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-71867358564 / 1000000000000) (-71867358562 / 1000000000000), orderedInterval (-24185986573 / 1000000000000) (-24185986572 / 1000000000000)))) (orderedInterval (463651515 / 1000000000000) (463651575 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (237523169855103 / 4000000000000) 3 (IntervalRat.scale (407 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-47244773636 / 1000000000000) (-47244773635 / 1000000000000), orderedInterval (-91738660621 / 1000000000000) (-91738660620 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (644921610994309 / 4000000000000) 3 (IntervalRat.scale (407 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-61281013497 / 1000000000000) (-61281012507 / 1000000000000), orderedInterval (14087153711 / 1000000000000) (14087154701 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (880585323768293 / 4000000000000) 3 (IntervalRat.scale (407 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (45813329394 / 1000000000000) (45813329395 / 1000000000000), orderedInterval (28055108049 / 1000000000000) (28055108050 / 1000000000000)))) (orderedInterval (2823306411 / 1000000000000) (2823306445 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (372345665713791 / 4000000000000) 3 (IntervalRat.scale (407 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-30467424672 / 1000000000000) (-30467423370 / 1000000000000), orderedInterval (77045548519 / 1000000000000) (77045549821 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1513564459113311 / 4000000000000) 3 (IntervalRat.scale (407 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (33519290627 / 1000000000000) (33519385469 / 1000000000000), orderedInterval (-23685231961 / 1000000000000) (-23685137119 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1010990913960049 / 4000000000000) 3 (IntervalRat.scale (407 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (40421684789 / 1000000000000) (40421778715 / 1000000000000), orderedInterval (-29826895630 / 1000000000000) (-29826801703 / 1000000000000)))) (orderedInterval (-23264692695 / 1000000000000) (-23264608854 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate331_chunkChecks3 :
    compactCertificate331.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate331.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate331_chunkChecks3_0
    compactCertificate331_chunkChecks3_1 compactCertificate331_chunkChecks3_2

theorem compactCertificate331_chunkChecks4_0 :
    compactCertificate331.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (407 / 2) 4 (IntervalRat.scale (407 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-4540081211 / 1000000000000) (-4540081210 / 1000000000000), orderedInterval (-55736039359 / 1000000000000) (-55736039358 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (599588715795707 / 4000000000000) 4 (IntervalRat.scale (407 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-7458791762 / 1000000000000) (-7458791735 / 1000000000000), orderedInterval (64766152823 / 1000000000000) (64766152850 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (193894671360731 / 800000000000) 4 (IntervalRat.scale (407 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-48645816396 / 1000000000000) (-48645816394 / 1000000000000), orderedInterval (-16031673588 / 1000000000000) (-16031673586 / 1000000000000)))) (orderedInterval (-7793590847 / 1000000000000) (-7793590821 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (174958491873649 / 4000000000000) 4 (IntervalRat.scale (407 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (62011174283 / 1000000000000) (62011174284 / 1000000000000), orderedInterval (102779503147 / 1000000000000) (102779503148 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (469963119120253 / 4000000000000) 4 (IntervalRat.scale (407 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-65781253616 / 1000000000000) (-65781242785 / 1000000000000), orderedInterval (33314214414 / 1000000000000) (33314225245 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1276041289257801 / 4000000000000) 4 (IntervalRat.scale (407 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-26932556145 / 1000000000000) (-26932548986 / 1000000000000), orderedInterval (35682733128 / 1000000000000) (35682740287 / 1000000000000)))) (orderedInterval (11199894897 / 1000000000000) (11199898123 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (939926238240913 / 4000000000000) 4 (IntervalRat.scale (407 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-7622660592 / 1000000000000) (-7622660591 / 1000000000000), orderedInterval (-51472942504 / 1000000000000) (-51472942503 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1610579629755349 / 4000000000000) 4 (IntervalRat.scale (407 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (38378471796 / 1000000000000) (38378471802 / 1000000000000), orderedInterval (10353623642 / 1000000000000) (10353623647 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1186345665713791 / 4000000000000) 4 (IntervalRat.scale (407 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (40859271841 / 1000000000000) (40859304347 / 1000000000000), orderedInterval (-21909383984 / 1000000000000) (-21909351478 / 1000000000000)))) (orderedInterval (-13727097642 / 1000000000000) (-13727093951 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate331_chunkChecks4_1 :
    compactCertificate331.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1820159333684593 / 4000000000000) 4 (IntervalRat.scale (407 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-10839760805 / 1000000000000) (-10839760804 / 1000000000000), orderedInterval (-35786722486 / 1000000000000) (-35786722485 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1050869481270697 / 4000000000000) 4 (IntervalRat.scale (407 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-18783014590 / 1000000000000) (-18783014036 / 1000000000000), orderedInterval (45537538957 / 1000000000000) (45537539510 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1864786335512573 / 4000000000000) 4 (IntervalRat.scale (407 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (33190521044 / 1000000000000) (33190571991 / 1000000000000), orderedInterval (-16282094696 / 1000000000000) (-16282043750 / 1000000000000)))) (orderedInterval (174737241925 / 1000000000000) (174737444122 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1742325288357137 / 4000000000000) 4 (IntervalRat.scale (407 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (11842332272 / 1000000000000) (11842332333 / 1000000000000), orderedInterval (-36363291252 / 1000000000000) (-36363291191 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1243405538564321 / 4000000000000) 4 (IntervalRat.scale (407 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-26246943583 / 1000000000000) (-26246943582 / 1000000000000), orderedInterval (-36823571176 / 1000000000000) (-36823571175 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1409889357360759 / 4000000000000) 4 (IntervalRat.scale (407 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (41873290959 / 1000000000000) (41873290976 / 1000000000000), orderedInterval (7205658182 / 1000000000000) (7205658199 / 1000000000000)))) (orderedInterval (-19967729874 / 1000000000000) (-19967729657 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1175418757812871 / 4000000000000) 4 (IntervalRat.scale (407 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-28905546206 / 1000000000000) (-28905535948 / 1000000000000), orderedInterval (36530879554 / 1000000000000) (36530889812 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1038518119402291 / 4000000000000) 4 (IntervalRat.scale (407 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (16408221331 / 1000000000000) (16408221616 / 1000000000000), orderedInterval (-46752100875 / 1000000000000) (-46752100590 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (301003029190809 / 800000000000) 4 (IntervalRat.scale (407 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (1962737944 / 1000000000000) (1962737945 / 1000000000000), orderedInterval (41084431098 / 1000000000000) (41084431099 / 1000000000000)))) (orderedInterval (-3219247112 / 1000000000000) (-3219246447 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate331_chunkChecks4_2 :
    compactCertificate331.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (832590219663323 / 4000000000000) 4 (IntervalRat.scale (407 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (55296173386 / 1000000000000) (55296173478 / 1000000000000), orderedInterval (-1042042300 / 1000000000000) (-1042042208 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (705795949892803 / 4000000000000) 4 (IntervalRat.scale (407 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (57948743187 / 1000000000000) (57948743188 / 1000000000000), orderedInterval (15643524044 / 1000000000000) (15643524046 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (441654334286209 / 4000000000000) 4 (IntervalRat.scale (407 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-71867358564 / 1000000000000) (-71867358562 / 1000000000000), orderedInterval (-24185986573 / 1000000000000) (-24185986572 / 1000000000000)))) (orderedInterval (-11738107891 / 1000000000000) (-11738107831 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (237523169855103 / 4000000000000) 4 (IntervalRat.scale (407 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-47244773636 / 1000000000000) (-47244773635 / 1000000000000), orderedInterval (-91738660621 / 1000000000000) (-91738660620 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (644921610994309 / 4000000000000) 4 (IntervalRat.scale (407 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-61281013497 / 1000000000000) (-61281012507 / 1000000000000), orderedInterval (14087153711 / 1000000000000) (14087154701 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (880585323768293 / 4000000000000) 4 (IntervalRat.scale (407 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (45813329394 / 1000000000000) (45813329395 / 1000000000000), orderedInterval (28055108049 / 1000000000000) (28055108050 / 1000000000000)))) (orderedInterval (-4282251100 / 1000000000000) (-4282251066 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (372345665713791 / 4000000000000) 4 (IntervalRat.scale (407 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-30467424672 / 1000000000000) (-30467423370 / 1000000000000), orderedInterval (77045548519 / 1000000000000) (77045549821 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1513564459113311 / 4000000000000) 4 (IntervalRat.scale (407 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (33519290627 / 1000000000000) (33519385469 / 1000000000000), orderedInterval (-23685231961 / 1000000000000) (-23685137119 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1010990913960049 / 4000000000000) 4 (IntervalRat.scale (407 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (40421684789 / 1000000000000) (40421778715 / 1000000000000), orderedInterval (-29826895630 / 1000000000000) (-29826801703 / 1000000000000)))) (orderedInterval (-50442121034 / 1000000000000) (-50441985706 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate331_chunkChecks4 :
    compactCertificate331.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate331.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate331_chunkChecks4_0
    compactCertificate331_chunkChecks4_1 compactCertificate331_chunkChecks4_2

theorem compactCertificate331_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate331.chunkCheck r b = true :=
  compactCertificate331.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate331_chunkChecks0
    · exact compactCertificate331_chunkChecks1
    · exact compactCertificate331_chunkChecks2
    · exact compactCertificate331_chunkChecks3
    · exact compactCertificate331_chunkChecks4)

theorem compactCertificate331_coefficient0 :
    compactCertificate331.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate331_coefficient1 :
    compactCertificate331.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate331_coefficient2 :
    compactCertificate331.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate331_coefficient3 :
    compactCertificate331.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate331_coefficient4 :
    compactCertificate331.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate331_coefficients : ∀ r : Fin 5,
    compactCertificate331.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate331_coefficient0
  · exact compactCertificate331_coefficient1
  · exact compactCertificate331_coefficient2
  · exact compactCertificate331_coefficient3
  · exact compactCertificate331_coefficient4

theorem compactCertificate331_lower : (1 : ℚ) ≤ compactCertificate331.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate331, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate331_proves {t : ℝ} (ht : t ∈ compactCertificate331.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate331.proves compactCertificate331_states compactCertificate331_chunks
    compactCertificate331_coefficients compactCertificate331_lower ht

end Erdos232
