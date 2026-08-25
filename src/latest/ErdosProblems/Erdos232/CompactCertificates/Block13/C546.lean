/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate546 : CompactCertificate where
  left := 417
  right := 418
  center := 835 / 2
  grid := fun i =>
    match i.val with
    | 0 => 133
    | 1 => 98
    | 2 => 158
    | 3 => 29
    | 4 => 77
    | 5 => 208
    | 6 => 154
    | 7 => 263
    | 8 => 194
    | 9 => 297
    | 10 => 172
    | 11 => 305
    | 12 => 285
    | 13 => 203
    | 14 => 230
    | 15 => 192
    | 16 => 170
    | 17 => 246
    | 18 => 136
    | 19 => 115
    | 20 => 72
    | 21 => 39
    | 22 => 105
    | 23 => 144
    | 24 => 61
    | 25 => 247
    | _ => 165
  point := fun i =>
    match i.val with
    | 0 => 835 / 2
    | 1 => 246022888299467 / 800000000000
    | 2 => 79558747216811 / 160000000000
    | 3 => 71788865215969 / 800000000000
    | 4 => 192834989909293 / 800000000000
    | 5 => 523584509351481 / 800000000000
    | 6 => 385669979818753 / 800000000000
    | 7 => 660852083953669 / 800000000000
    | 8 => 486780653990671 / 800000000000
    | 9 => 746846704484833 / 800000000000
    | 10 => 431192145877657 / 800000000000
    | 11 => 765158029559213 / 800000000000
    | 12 => 714909884903297 / 800000000000
    | 13 => 510193427371601 / 800000000000
    | 14 => 578504969727879 / 800000000000
    | 15 => 482297131584151 / 800000000000
    | 16 => 426124142359171 / 800000000000
    | 17 => 123507385441929 / 160000000000
    | 18 => 341627927969963 / 800000000000
    | 19 => 289601777965843 / 800000000000
    | 20 => 181219346009329 / 800000000000
    | 21 => 97460366992143 / 800000000000
    | 22 => 264623855125429 / 800000000000
    | 23 => 361321250784533 / 800000000000
    | 24 => 152780653990671 / 800000000000
    | 25 => 621044876343791 / 800000000000
    | _ => 414829195654369 / 800000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-17100130168 / 1000000000000) (-17100130167 / 1000000000000), orderedInterval (-35085417780 / 1000000000000) (-35085417779 / 1000000000000))
    | 1 => (orderedInterval (19277538783 / 1000000000000) (19277538784 / 1000000000000), orderedInterval (41181444835 / 1000000000000) (41181444836 / 1000000000000))
    | 2 => (orderedInterval (35652465983 / 1000000000000) (35652467421 / 1000000000000), orderedInterval (-3069368545 / 1000000000000) (-3069367107 / 1000000000000))
    | 3 => (orderedInterval (46587510670 / 1000000000000) (46587523001 / 1000000000000), orderedInterval (-70430816834 / 1000000000000) (-70430804504 / 1000000000000))
    | 4 => (orderedInterval (3800393569 / 1000000000000) (3800393576 / 1000000000000), orderedInterval (-51258825929 / 1000000000000) (-51258825922 / 1000000000000))
    | 5 => (orderedInterval (30266157408 / 1000000000000) (30266175005 / 1000000000000), orderedInterval (-7550998098 / 1000000000000) (-7550980501 / 1000000000000))
    | 6 => (orderedInterval (-29187939321 / 1000000000000) (-29187890165 / 1000000000000), orderedInterval (21677733027 / 1000000000000) (21677782183 / 1000000000000))
    | 7 => (orderedInterval (-15937039309 / 1000000000000) (-15937039308 / 1000000000000), orderedInterval (-22720866165 / 1000000000000) (-22720866164 / 1000000000000))
    | 8 => (orderedInterval (-6678403879 / 1000000000000) (-6678403875 / 1000000000000), orderedInterval (31654381102 / 1000000000000) (31654381106 / 1000000000000))
    | 9 => (orderedInterval (-25095540210 / 1000000000000) (-25095539968 / 1000000000000), orderedInterval (-7207499015 / 1000000000000) (-7207498772 / 1000000000000))
    | 10 => (orderedInterval (-18793667498 / 1000000000000) (-18793666514 / 1000000000000), orderedInterval (28791250693 / 1000000000000) (28791251676 / 1000000000000))
    | 11 => (orderedInterval (21029874691 / 1000000000000) (21029880686 / 1000000000000), orderedInterval (-14955991893 / 1000000000000) (-14955985898 / 1000000000000))
    | 12 => (orderedInterval (21416360468 / 1000000000000) (21416367128 / 1000000000000), orderedInterval (-15940920534 / 1000000000000) (-15940913874 / 1000000000000))
    | 13 => (orderedInterval (-22302527519 / 1000000000000) (-22302527518 / 1000000000000), orderedInterval (-22361922769 / 1000000000000) (-22361922768 / 1000000000000))
    | 14 => (orderedInterval (28951465112 / 1000000000000) (28951465240 / 1000000000000), orderedInterval (6474439107 / 1000000000000) (6474439236 / 1000000000000))
    | 15 => (orderedInterval (14740547023 / 1000000000000) (14740547024 / 1000000000000), orderedInterval (28948020760 / 1000000000000) (28948020761 / 1000000000000))
    | 16 => (orderedInterval (-20378998637 / 1000000000000) (-20378996772 / 1000000000000), orderedInterval (27945431833 / 1000000000000) (27945433698 / 1000000000000))
    | 17 => (orderedInterval (-3591730862 / 1000000000000) (-3591730861 / 1000000000000), orderedInterval (28494796949 / 1000000000000) (28494796950 / 1000000000000))
    | 18 => (orderedInterval (20621076801 / 1000000000000) (20621076802 / 1000000000000), orderedInterval (32618811367 / 1000000000000) (32618811368 / 1000000000000))
    | 19 => (orderedInterval (-41842550238 / 1000000000000) (-41842550152 / 1000000000000), orderedInterval (-2736252287 / 1000000000000) (-2736252202 / 1000000000000))
    | 20 => (orderedInterval (47585934280 / 1000000000000) (47585934281 / 1000000000000), orderedInterval (23260708401 / 1000000000000) (23260708402 / 1000000000000))
    | 21 => (orderedInterval (-6332830081 / 1000000000000) (-6332830079 / 1000000000000), orderedInterval (-71985186229 / 1000000000000) (-71985186227 / 1000000000000))
    | 22 => (orderedInterval (-43517985786 / 1000000000000) (-43517984913 / 1000000000000), orderedInterval (5614261330 / 1000000000000) (5614262203 / 1000000000000))
    | 23 => (orderedInterval (1776763198 / 1000000000000) (1776763199 / 1000000000000), orderedInterval (37499784686 / 1000000000000) (37499784687 / 1000000000000))
    | 24 => (orderedInterval (-7107141136 / 1000000000000) (-7107141134 / 1000000000000), orderedInterval (-57278944927 / 1000000000000) (-57278944926 / 1000000000000))
    | 25 => (orderedInterval (-25750272010 / 1000000000000) (-25750272004 / 1000000000000), orderedInterval (-12512828876 / 1000000000000) (-12512828870 / 1000000000000))
    | _ => (orderedInterval (-28680709921 / 1000000000000) (-28680709920 / 1000000000000), orderedInterval (-20100454915 / 1000000000000) (-20100454914 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-4506136378 / 1000000000000) (-4506136264 / 1000000000000)
      | 1 => orderedInterval (-2518294130 / 1000000000000) (-2518292695 / 1000000000000)
      | 2 => orderedInterval (330158199 / 1000000000000) (330158223 / 1000000000000)
      | 3 => orderedInterval (6056238853 / 1000000000000) (6056239986 / 1000000000000)
      | 4 => orderedInterval (-2642133554 / 1000000000000) (-2642133383 / 1000000000000)
      | 5 => orderedInterval (1244478721 / 1000000000000) (1244478868 / 1000000000000)
      | 6 => orderedInterval (620305105 / 1000000000000) (620305215 / 1000000000000)
      | 7 => orderedInterval (968053818 / 1000000000000) (968053888 / 1000000000000)
      | _ => orderedInterval (7434535658 / 1000000000000) (7434535774 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-13838492429 / 1000000000000) (-13838492295 / 1000000000000)
      | 1 => orderedInterval (-74809110 / 1000000000000) (-74807062 / 1000000000000)
      | 2 => orderedInterval (2501573606 / 1000000000000) (2501573647 / 1000000000000)
      | 3 => orderedInterval (747016532 / 1000000000000) (747019018 / 1000000000000)
      | 4 => orderedInterval (-2670881854 / 1000000000000) (-2670881514 / 1000000000000)
      | 5 => orderedInterval (-208690301 / 1000000000000) (-208690107 / 1000000000000)
      | 6 => orderedInterval (-4789460775 / 1000000000000) (-4789460674 / 1000000000000)
      | 7 => orderedInterval (-2822081966 / 1000000000000) (-2822081905 / 1000000000000)
      | _ => orderedInterval (6420056352 / 1000000000000) (6420056516 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (3745938001 / 1000000000000) (3745938160 / 1000000000000)
      | 1 => orderedInterval (5264701808 / 1000000000000) (5264704972 / 1000000000000)
      | 2 => orderedInterval (-1587548715 / 1000000000000) (-1587548642 / 1000000000000)
      | 3 => orderedInterval (-35666471272 / 1000000000000) (-35666465723 / 1000000000000)
      | 4 => orderedInterval (7138269159 / 1000000000000) (7138269847 / 1000000000000)
      | 5 => orderedInterval (-1938341620 / 1000000000000) (-1938341359 / 1000000000000)
      | 6 => orderedInterval (1224386198 / 1000000000000) (1224386295 / 1000000000000)
      | 7 => orderedInterval (-463577812 / 1000000000000) (-463577755 / 1000000000000)
      | _ => orderedInterval (-15554576530 / 1000000000000) (-15554576288 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (14048504781 / 1000000000000) (14048504968 / 1000000000000)
      | 1 => orderedInterval (-1727928268 / 1000000000000) (-1727923322 / 1000000000000)
      | 2 => orderedInterval (-7792841137 / 1000000000000) (-7792841004 / 1000000000000)
      | 3 => orderedInterval (6738975014 / 1000000000000) (6738987522 / 1000000000000)
      | 4 => orderedInterval (4867928571 / 1000000000000) (4867929982 / 1000000000000)
      | 5 => orderedInterval (-2292080071 / 1000000000000) (-2292079716 / 1000000000000)
      | 6 => orderedInterval (5356190246 / 1000000000000) (5356190340 / 1000000000000)
      | 7 => orderedInterval (3669886239 / 1000000000000) (3669886295 / 1000000000000)
      | _ => orderedInterval (-13703325480 / 1000000000000) (-13703325107 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-2582755438 / 1000000000000) (-2582755216 / 1000000000000)
      | 1 => orderedInterval (-12970823510 / 1000000000000) (-12970815751 / 1000000000000)
      | 2 => orderedInterval (6842825115 / 1000000000000) (6842825360 / 1000000000000)
      | 3 => orderedInterval (189920717044 / 1000000000000) (189920745424 / 1000000000000)
      | 4 => orderedInterval (-20939686880 / 1000000000000) (-20939683951 / 1000000000000)
      | 5 => orderedInterval (2766247440 / 1000000000000) (2766247935 / 1000000000000)
      | 6 => orderedInterval (-2161621999 / 1000000000000) (-2161621907 / 1000000000000)
      | 7 => orderedInterval (185791233 / 1000000000000) (185791289 / 1000000000000)
      | _ => orderedInterval (37925138471 / 1000000000000) (37925139072 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (6987206292 / 1000000000000) (6987209612 / 1000000000000)
    | 1 => orderedInterval (-14735769945 / 1000000000000) (-14735764376 / 1000000000000)
    | 2 => orderedInterval (-37837220783 / 1000000000000) (-37837210493 / 1000000000000)
    | 3 => orderedInterval (9165309895 / 1000000000000) (9165329958 / 1000000000000)
    | _ => orderedInterval (198985831476 / 1000000000000) (198985872255 / 1000000000000)

theorem compactCertificate546_stateChecks0 :
    compactCertificate546.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 133 12 (835 / 2)) (orderedInterval (-17100130168 / 1000000000000) (-17100130167 / 1000000000000), orderedInterval (-35085417780 / 1000000000000) (-35085417779 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 98 12 (246022888299467 / 800000000000)) (orderedInterval (19277538783 / 1000000000000) (19277538784 / 1000000000000), orderedInterval (41181444835 / 1000000000000) (41181444836 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 158 12 (79558747216811 / 160000000000)) (orderedInterval (35652465983 / 1000000000000) (35652467421 / 1000000000000), orderedInterval (-3069368545 / 1000000000000) (-3069367107 / 1000000000000))) = true
  rfl'

theorem compactCertificate546_stateChecks1 :
    compactCertificate546.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 29 12 (71788865215969 / 800000000000)) (orderedInterval (46587510670 / 1000000000000) (46587523001 / 1000000000000), orderedInterval (-70430816834 / 1000000000000) (-70430804504 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 77 12 (192834989909293 / 800000000000)) (orderedInterval (3800393569 / 1000000000000) (3800393576 / 1000000000000), orderedInterval (-51258825929 / 1000000000000) (-51258825922 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 208 12 (523584509351481 / 800000000000)) (orderedInterval (30266157408 / 1000000000000) (30266175005 / 1000000000000), orderedInterval (-7550998098 / 1000000000000) (-7550980501 / 1000000000000))) = true
  rfl'

theorem compactCertificate546_stateChecks2 :
    compactCertificate546.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 154 12 (385669979818753 / 800000000000)) (orderedInterval (-29187939321 / 1000000000000) (-29187890165 / 1000000000000), orderedInterval (21677733027 / 1000000000000) (21677782183 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 263 12 (660852083953669 / 800000000000)) (orderedInterval (-15937039309 / 1000000000000) (-15937039308 / 1000000000000), orderedInterval (-22720866165 / 1000000000000) (-22720866164 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 194 12 (486780653990671 / 800000000000)) (orderedInterval (-6678403879 / 1000000000000) (-6678403875 / 1000000000000), orderedInterval (31654381102 / 1000000000000) (31654381106 / 1000000000000))) = true
  rfl'

theorem compactCertificate546_stateChecks3 :
    compactCertificate546.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 297 12 (746846704484833 / 800000000000)) (orderedInterval (-25095540210 / 1000000000000) (-25095539968 / 1000000000000), orderedInterval (-7207499015 / 1000000000000) (-7207498772 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 172 12 (431192145877657 / 800000000000)) (orderedInterval (-18793667498 / 1000000000000) (-18793666514 / 1000000000000), orderedInterval (28791250693 / 1000000000000) (28791251676 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 305 12 (765158029559213 / 800000000000)) (orderedInterval (21029874691 / 1000000000000) (21029880686 / 1000000000000), orderedInterval (-14955991893 / 1000000000000) (-14955985898 / 1000000000000))) = true
  rfl'

theorem compactCertificate546_stateChecks4 :
    compactCertificate546.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 285 12 (714909884903297 / 800000000000)) (orderedInterval (21416360468 / 1000000000000) (21416367128 / 1000000000000), orderedInterval (-15940920534 / 1000000000000) (-15940913874 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 203 12 (510193427371601 / 800000000000)) (orderedInterval (-22302527519 / 1000000000000) (-22302527518 / 1000000000000), orderedInterval (-22361922769 / 1000000000000) (-22361922768 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 230 12 (578504969727879 / 800000000000)) (orderedInterval (28951465112 / 1000000000000) (28951465240 / 1000000000000), orderedInterval (6474439107 / 1000000000000) (6474439236 / 1000000000000))) = true
  rfl'

theorem compactCertificate546_stateChecks5 :
    compactCertificate546.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 192 12 (482297131584151 / 800000000000)) (orderedInterval (14740547023 / 1000000000000) (14740547024 / 1000000000000), orderedInterval (28948020760 / 1000000000000) (28948020761 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 170 12 (426124142359171 / 800000000000)) (orderedInterval (-20378998637 / 1000000000000) (-20378996772 / 1000000000000), orderedInterval (27945431833 / 1000000000000) (27945433698 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 246 12 (123507385441929 / 160000000000)) (orderedInterval (-3591730862 / 1000000000000) (-3591730861 / 1000000000000), orderedInterval (28494796949 / 1000000000000) (28494796950 / 1000000000000))) = true
  rfl'

theorem compactCertificate546_stateChecks6 :
    compactCertificate546.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 136 12 (341627927969963 / 800000000000)) (orderedInterval (20621076801 / 1000000000000) (20621076802 / 1000000000000), orderedInterval (32618811367 / 1000000000000) (32618811368 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 115 12 (289601777965843 / 800000000000)) (orderedInterval (-41842550238 / 1000000000000) (-41842550152 / 1000000000000), orderedInterval (-2736252287 / 1000000000000) (-2736252202 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 72 12 (181219346009329 / 800000000000)) (orderedInterval (47585934280 / 1000000000000) (47585934281 / 1000000000000), orderedInterval (23260708401 / 1000000000000) (23260708402 / 1000000000000))) = true
  rfl'

theorem compactCertificate546_stateChecks7 :
    compactCertificate546.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 39 12 (97460366992143 / 800000000000)) (orderedInterval (-6332830081 / 1000000000000) (-6332830079 / 1000000000000), orderedInterval (-71985186229 / 1000000000000) (-71985186227 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 105 12 (264623855125429 / 800000000000)) (orderedInterval (-43517985786 / 1000000000000) (-43517984913 / 1000000000000), orderedInterval (5614261330 / 1000000000000) (5614262203 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 144 12 (361321250784533 / 800000000000)) (orderedInterval (1776763198 / 1000000000000) (1776763199 / 1000000000000), orderedInterval (37499784686 / 1000000000000) (37499784687 / 1000000000000))) = true
  rfl'

theorem compactCertificate546_stateChecks8 :
    compactCertificate546.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 61 12 (152780653990671 / 800000000000)) (orderedInterval (-7107141136 / 1000000000000) (-7107141134 / 1000000000000), orderedInterval (-57278944927 / 1000000000000) (-57278944926 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 247 12 (621044876343791 / 800000000000)) (orderedInterval (-25750272010 / 1000000000000) (-25750272004 / 1000000000000), orderedInterval (-12512828876 / 1000000000000) (-12512828870 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 165 12 (414829195654369 / 800000000000)) (orderedInterval (-28680709921 / 1000000000000) (-28680709920 / 1000000000000), orderedInterval (-20100454915 / 1000000000000) (-20100454914 / 1000000000000))) = true
  rfl'

theorem compactCertificate546_states : ∀ j,
    BesselStateValid (compactCertificate546.point j) (compactCertificate546.state j) :=
  compactCertificate546.statesValid_of_checks3 compactCertificate546_stateChecks0
    compactCertificate546_stateChecks1 compactCertificate546_stateChecks2
    compactCertificate546_stateChecks3 compactCertificate546_stateChecks4
    compactCertificate546_stateChecks5 compactCertificate546_stateChecks6
    compactCertificate546_stateChecks7 compactCertificate546_stateChecks8

theorem compactCertificate546_chunkChecks0_0 :
    compactCertificate546.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (835 / 2) 0 (IntervalRat.scale (835 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-17100130168 / 1000000000000) (-17100130167 / 1000000000000), orderedInterval (-35085417780 / 1000000000000) (-35085417779 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (246022888299467 / 800000000000) 0 (IntervalRat.scale (835 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (19277538783 / 1000000000000) (19277538784 / 1000000000000), orderedInterval (41181444835 / 1000000000000) (41181444836 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (79558747216811 / 160000000000) 0 (IntervalRat.scale (835 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (35652465983 / 1000000000000) (35652467421 / 1000000000000), orderedInterval (-3069368545 / 1000000000000) (-3069367107 / 1000000000000)))) (orderedInterval (-4506136378 / 1000000000000) (-4506136264 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (71788865215969 / 800000000000) 0 (IntervalRat.scale (835 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (46587510670 / 1000000000000) (46587523001 / 1000000000000), orderedInterval (-70430816834 / 1000000000000) (-70430804504 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (192834989909293 / 800000000000) 0 (IntervalRat.scale (835 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (3800393569 / 1000000000000) (3800393576 / 1000000000000), orderedInterval (-51258825929 / 1000000000000) (-51258825922 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (523584509351481 / 800000000000) 0 (IntervalRat.scale (835 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30266157408 / 1000000000000) (30266175005 / 1000000000000), orderedInterval (-7550998098 / 1000000000000) (-7550980501 / 1000000000000)))) (orderedInterval (-2518294130 / 1000000000000) (-2518292695 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (385669979818753 / 800000000000) 0 (IntervalRat.scale (835 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-29187939321 / 1000000000000) (-29187890165 / 1000000000000), orderedInterval (21677733027 / 1000000000000) (21677782183 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (660852083953669 / 800000000000) 0 (IntervalRat.scale (835 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-15937039309 / 1000000000000) (-15937039308 / 1000000000000), orderedInterval (-22720866165 / 1000000000000) (-22720866164 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (486780653990671 / 800000000000) 0 (IntervalRat.scale (835 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-6678403879 / 1000000000000) (-6678403875 / 1000000000000), orderedInterval (31654381102 / 1000000000000) (31654381106 / 1000000000000)))) (orderedInterval (330158199 / 1000000000000) (330158223 / 1000000000000))) = true
  rfl'

theorem compactCertificate546_chunkChecks0_1 :
    compactCertificate546.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (746846704484833 / 800000000000) 0 (IntervalRat.scale (835 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-25095540210 / 1000000000000) (-25095539968 / 1000000000000), orderedInterval (-7207499015 / 1000000000000) (-7207498772 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (431192145877657 / 800000000000) 0 (IntervalRat.scale (835 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-18793667498 / 1000000000000) (-18793666514 / 1000000000000), orderedInterval (28791250693 / 1000000000000) (28791251676 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (765158029559213 / 800000000000) 0 (IntervalRat.scale (835 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (21029874691 / 1000000000000) (21029880686 / 1000000000000), orderedInterval (-14955991893 / 1000000000000) (-14955985898 / 1000000000000)))) (orderedInterval (6056238853 / 1000000000000) (6056239986 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (714909884903297 / 800000000000) 0 (IntervalRat.scale (835 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (21416360468 / 1000000000000) (21416367128 / 1000000000000), orderedInterval (-15940920534 / 1000000000000) (-15940913874 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (510193427371601 / 800000000000) 0 (IntervalRat.scale (835 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-22302527519 / 1000000000000) (-22302527518 / 1000000000000), orderedInterval (-22361922769 / 1000000000000) (-22361922768 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (578504969727879 / 800000000000) 0 (IntervalRat.scale (835 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (28951465112 / 1000000000000) (28951465240 / 1000000000000), orderedInterval (6474439107 / 1000000000000) (6474439236 / 1000000000000)))) (orderedInterval (-2642133554 / 1000000000000) (-2642133383 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (482297131584151 / 800000000000) 0 (IntervalRat.scale (835 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (14740547023 / 1000000000000) (14740547024 / 1000000000000), orderedInterval (28948020760 / 1000000000000) (28948020761 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (426124142359171 / 800000000000) 0 (IntervalRat.scale (835 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-20378998637 / 1000000000000) (-20378996772 / 1000000000000), orderedInterval (27945431833 / 1000000000000) (27945433698 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (123507385441929 / 160000000000) 0 (IntervalRat.scale (835 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-3591730862 / 1000000000000) (-3591730861 / 1000000000000), orderedInterval (28494796949 / 1000000000000) (28494796950 / 1000000000000)))) (orderedInterval (1244478721 / 1000000000000) (1244478868 / 1000000000000))) = true
  rfl'

theorem compactCertificate546_chunkChecks0_2 :
    compactCertificate546.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (341627927969963 / 800000000000) 0 (IntervalRat.scale (835 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (20621076801 / 1000000000000) (20621076802 / 1000000000000), orderedInterval (32618811367 / 1000000000000) (32618811368 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (289601777965843 / 800000000000) 0 (IntervalRat.scale (835 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-41842550238 / 1000000000000) (-41842550152 / 1000000000000), orderedInterval (-2736252287 / 1000000000000) (-2736252202 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (181219346009329 / 800000000000) 0 (IntervalRat.scale (835 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (47585934280 / 1000000000000) (47585934281 / 1000000000000), orderedInterval (23260708401 / 1000000000000) (23260708402 / 1000000000000)))) (orderedInterval (620305105 / 1000000000000) (620305215 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (97460366992143 / 800000000000) 0 (IntervalRat.scale (835 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-6332830081 / 1000000000000) (-6332830079 / 1000000000000), orderedInterval (-71985186229 / 1000000000000) (-71985186227 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (264623855125429 / 800000000000) 0 (IntervalRat.scale (835 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-43517985786 / 1000000000000) (-43517984913 / 1000000000000), orderedInterval (5614261330 / 1000000000000) (5614262203 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (361321250784533 / 800000000000) 0 (IntervalRat.scale (835 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (1776763198 / 1000000000000) (1776763199 / 1000000000000), orderedInterval (37499784686 / 1000000000000) (37499784687 / 1000000000000)))) (orderedInterval (968053818 / 1000000000000) (968053888 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (152780653990671 / 800000000000) 0 (IntervalRat.scale (835 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-7107141136 / 1000000000000) (-7107141134 / 1000000000000), orderedInterval (-57278944927 / 1000000000000) (-57278944926 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (621044876343791 / 800000000000) 0 (IntervalRat.scale (835 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-25750272010 / 1000000000000) (-25750272004 / 1000000000000), orderedInterval (-12512828876 / 1000000000000) (-12512828870 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (414829195654369 / 800000000000) 0 (IntervalRat.scale (835 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-28680709921 / 1000000000000) (-28680709920 / 1000000000000), orderedInterval (-20100454915 / 1000000000000) (-20100454914 / 1000000000000)))) (orderedInterval (7434535658 / 1000000000000) (7434535774 / 1000000000000))) = true
  rfl'

theorem compactCertificate546_chunkChecks0 :
    compactCertificate546.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate546.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate546_chunkChecks0_0
    compactCertificate546_chunkChecks0_1 compactCertificate546_chunkChecks0_2

theorem compactCertificate546_chunkChecks1_0 :
    compactCertificate546.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (835 / 2) 1 (IntervalRat.scale (835 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-17100130168 / 1000000000000) (-17100130167 / 1000000000000), orderedInterval (-35085417780 / 1000000000000) (-35085417779 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (246022888299467 / 800000000000) 1 (IntervalRat.scale (835 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (19277538783 / 1000000000000) (19277538784 / 1000000000000), orderedInterval (41181444835 / 1000000000000) (41181444836 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (79558747216811 / 160000000000) 1 (IntervalRat.scale (835 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (35652465983 / 1000000000000) (35652467421 / 1000000000000), orderedInterval (-3069368545 / 1000000000000) (-3069367107 / 1000000000000)))) (orderedInterval (-13838492429 / 1000000000000) (-13838492295 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (71788865215969 / 800000000000) 1 (IntervalRat.scale (835 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (46587510670 / 1000000000000) (46587523001 / 1000000000000), orderedInterval (-70430816834 / 1000000000000) (-70430804504 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (192834989909293 / 800000000000) 1 (IntervalRat.scale (835 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (3800393569 / 1000000000000) (3800393576 / 1000000000000), orderedInterval (-51258825929 / 1000000000000) (-51258825922 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (523584509351481 / 800000000000) 1 (IntervalRat.scale (835 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30266157408 / 1000000000000) (30266175005 / 1000000000000), orderedInterval (-7550998098 / 1000000000000) (-7550980501 / 1000000000000)))) (orderedInterval (-74809110 / 1000000000000) (-74807062 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (385669979818753 / 800000000000) 1 (IntervalRat.scale (835 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-29187939321 / 1000000000000) (-29187890165 / 1000000000000), orderedInterval (21677733027 / 1000000000000) (21677782183 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (660852083953669 / 800000000000) 1 (IntervalRat.scale (835 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-15937039309 / 1000000000000) (-15937039308 / 1000000000000), orderedInterval (-22720866165 / 1000000000000) (-22720866164 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (486780653990671 / 800000000000) 1 (IntervalRat.scale (835 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-6678403879 / 1000000000000) (-6678403875 / 1000000000000), orderedInterval (31654381102 / 1000000000000) (31654381106 / 1000000000000)))) (orderedInterval (2501573606 / 1000000000000) (2501573647 / 1000000000000))) = true
  rfl'

theorem compactCertificate546_chunkChecks1_1 :
    compactCertificate546.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (746846704484833 / 800000000000) 1 (IntervalRat.scale (835 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-25095540210 / 1000000000000) (-25095539968 / 1000000000000), orderedInterval (-7207499015 / 1000000000000) (-7207498772 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (431192145877657 / 800000000000) 1 (IntervalRat.scale (835 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-18793667498 / 1000000000000) (-18793666514 / 1000000000000), orderedInterval (28791250693 / 1000000000000) (28791251676 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (765158029559213 / 800000000000) 1 (IntervalRat.scale (835 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (21029874691 / 1000000000000) (21029880686 / 1000000000000), orderedInterval (-14955991893 / 1000000000000) (-14955985898 / 1000000000000)))) (orderedInterval (747016532 / 1000000000000) (747019018 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (714909884903297 / 800000000000) 1 (IntervalRat.scale (835 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (21416360468 / 1000000000000) (21416367128 / 1000000000000), orderedInterval (-15940920534 / 1000000000000) (-15940913874 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (510193427371601 / 800000000000) 1 (IntervalRat.scale (835 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-22302527519 / 1000000000000) (-22302527518 / 1000000000000), orderedInterval (-22361922769 / 1000000000000) (-22361922768 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (578504969727879 / 800000000000) 1 (IntervalRat.scale (835 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (28951465112 / 1000000000000) (28951465240 / 1000000000000), orderedInterval (6474439107 / 1000000000000) (6474439236 / 1000000000000)))) (orderedInterval (-2670881854 / 1000000000000) (-2670881514 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (482297131584151 / 800000000000) 1 (IntervalRat.scale (835 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (14740547023 / 1000000000000) (14740547024 / 1000000000000), orderedInterval (28948020760 / 1000000000000) (28948020761 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (426124142359171 / 800000000000) 1 (IntervalRat.scale (835 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-20378998637 / 1000000000000) (-20378996772 / 1000000000000), orderedInterval (27945431833 / 1000000000000) (27945433698 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (123507385441929 / 160000000000) 1 (IntervalRat.scale (835 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-3591730862 / 1000000000000) (-3591730861 / 1000000000000), orderedInterval (28494796949 / 1000000000000) (28494796950 / 1000000000000)))) (orderedInterval (-208690301 / 1000000000000) (-208690107 / 1000000000000))) = true
  rfl'

theorem compactCertificate546_chunkChecks1_2 :
    compactCertificate546.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (341627927969963 / 800000000000) 1 (IntervalRat.scale (835 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (20621076801 / 1000000000000) (20621076802 / 1000000000000), orderedInterval (32618811367 / 1000000000000) (32618811368 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (289601777965843 / 800000000000) 1 (IntervalRat.scale (835 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-41842550238 / 1000000000000) (-41842550152 / 1000000000000), orderedInterval (-2736252287 / 1000000000000) (-2736252202 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (181219346009329 / 800000000000) 1 (IntervalRat.scale (835 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (47585934280 / 1000000000000) (47585934281 / 1000000000000), orderedInterval (23260708401 / 1000000000000) (23260708402 / 1000000000000)))) (orderedInterval (-4789460775 / 1000000000000) (-4789460674 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (97460366992143 / 800000000000) 1 (IntervalRat.scale (835 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-6332830081 / 1000000000000) (-6332830079 / 1000000000000), orderedInterval (-71985186229 / 1000000000000) (-71985186227 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (264623855125429 / 800000000000) 1 (IntervalRat.scale (835 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-43517985786 / 1000000000000) (-43517984913 / 1000000000000), orderedInterval (5614261330 / 1000000000000) (5614262203 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (361321250784533 / 800000000000) 1 (IntervalRat.scale (835 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (1776763198 / 1000000000000) (1776763199 / 1000000000000), orderedInterval (37499784686 / 1000000000000) (37499784687 / 1000000000000)))) (orderedInterval (-2822081966 / 1000000000000) (-2822081905 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (152780653990671 / 800000000000) 1 (IntervalRat.scale (835 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-7107141136 / 1000000000000) (-7107141134 / 1000000000000), orderedInterval (-57278944927 / 1000000000000) (-57278944926 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (621044876343791 / 800000000000) 1 (IntervalRat.scale (835 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-25750272010 / 1000000000000) (-25750272004 / 1000000000000), orderedInterval (-12512828876 / 1000000000000) (-12512828870 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (414829195654369 / 800000000000) 1 (IntervalRat.scale (835 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-28680709921 / 1000000000000) (-28680709920 / 1000000000000), orderedInterval (-20100454915 / 1000000000000) (-20100454914 / 1000000000000)))) (orderedInterval (6420056352 / 1000000000000) (6420056516 / 1000000000000))) = true
  rfl'

theorem compactCertificate546_chunkChecks1 :
    compactCertificate546.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate546.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate546_chunkChecks1_0
    compactCertificate546_chunkChecks1_1 compactCertificate546_chunkChecks1_2

theorem compactCertificate546_chunkChecks2_0 :
    compactCertificate546.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (835 / 2) 2 (IntervalRat.scale (835 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-17100130168 / 1000000000000) (-17100130167 / 1000000000000), orderedInterval (-35085417780 / 1000000000000) (-35085417779 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (246022888299467 / 800000000000) 2 (IntervalRat.scale (835 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (19277538783 / 1000000000000) (19277538784 / 1000000000000), orderedInterval (41181444835 / 1000000000000) (41181444836 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (79558747216811 / 160000000000) 2 (IntervalRat.scale (835 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (35652465983 / 1000000000000) (35652467421 / 1000000000000), orderedInterval (-3069368545 / 1000000000000) (-3069367107 / 1000000000000)))) (orderedInterval (3745938001 / 1000000000000) (3745938160 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (71788865215969 / 800000000000) 2 (IntervalRat.scale (835 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (46587510670 / 1000000000000) (46587523001 / 1000000000000), orderedInterval (-70430816834 / 1000000000000) (-70430804504 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (192834989909293 / 800000000000) 2 (IntervalRat.scale (835 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (3800393569 / 1000000000000) (3800393576 / 1000000000000), orderedInterval (-51258825929 / 1000000000000) (-51258825922 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (523584509351481 / 800000000000) 2 (IntervalRat.scale (835 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30266157408 / 1000000000000) (30266175005 / 1000000000000), orderedInterval (-7550998098 / 1000000000000) (-7550980501 / 1000000000000)))) (orderedInterval (5264701808 / 1000000000000) (5264704972 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (385669979818753 / 800000000000) 2 (IntervalRat.scale (835 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-29187939321 / 1000000000000) (-29187890165 / 1000000000000), orderedInterval (21677733027 / 1000000000000) (21677782183 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (660852083953669 / 800000000000) 2 (IntervalRat.scale (835 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-15937039309 / 1000000000000) (-15937039308 / 1000000000000), orderedInterval (-22720866165 / 1000000000000) (-22720866164 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (486780653990671 / 800000000000) 2 (IntervalRat.scale (835 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-6678403879 / 1000000000000) (-6678403875 / 1000000000000), orderedInterval (31654381102 / 1000000000000) (31654381106 / 1000000000000)))) (orderedInterval (-1587548715 / 1000000000000) (-1587548642 / 1000000000000))) = true
  rfl'

theorem compactCertificate546_chunkChecks2_1 :
    compactCertificate546.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (746846704484833 / 800000000000) 2 (IntervalRat.scale (835 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-25095540210 / 1000000000000) (-25095539968 / 1000000000000), orderedInterval (-7207499015 / 1000000000000) (-7207498772 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (431192145877657 / 800000000000) 2 (IntervalRat.scale (835 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-18793667498 / 1000000000000) (-18793666514 / 1000000000000), orderedInterval (28791250693 / 1000000000000) (28791251676 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (765158029559213 / 800000000000) 2 (IntervalRat.scale (835 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (21029874691 / 1000000000000) (21029880686 / 1000000000000), orderedInterval (-14955991893 / 1000000000000) (-14955985898 / 1000000000000)))) (orderedInterval (-35666471272 / 1000000000000) (-35666465723 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (714909884903297 / 800000000000) 2 (IntervalRat.scale (835 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (21416360468 / 1000000000000) (21416367128 / 1000000000000), orderedInterval (-15940920534 / 1000000000000) (-15940913874 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (510193427371601 / 800000000000) 2 (IntervalRat.scale (835 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-22302527519 / 1000000000000) (-22302527518 / 1000000000000), orderedInterval (-22361922769 / 1000000000000) (-22361922768 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (578504969727879 / 800000000000) 2 (IntervalRat.scale (835 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (28951465112 / 1000000000000) (28951465240 / 1000000000000), orderedInterval (6474439107 / 1000000000000) (6474439236 / 1000000000000)))) (orderedInterval (7138269159 / 1000000000000) (7138269847 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (482297131584151 / 800000000000) 2 (IntervalRat.scale (835 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (14740547023 / 1000000000000) (14740547024 / 1000000000000), orderedInterval (28948020760 / 1000000000000) (28948020761 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (426124142359171 / 800000000000) 2 (IntervalRat.scale (835 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-20378998637 / 1000000000000) (-20378996772 / 1000000000000), orderedInterval (27945431833 / 1000000000000) (27945433698 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (123507385441929 / 160000000000) 2 (IntervalRat.scale (835 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-3591730862 / 1000000000000) (-3591730861 / 1000000000000), orderedInterval (28494796949 / 1000000000000) (28494796950 / 1000000000000)))) (orderedInterval (-1938341620 / 1000000000000) (-1938341359 / 1000000000000))) = true
  rfl'

theorem compactCertificate546_chunkChecks2_2 :
    compactCertificate546.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (341627927969963 / 800000000000) 2 (IntervalRat.scale (835 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (20621076801 / 1000000000000) (20621076802 / 1000000000000), orderedInterval (32618811367 / 1000000000000) (32618811368 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (289601777965843 / 800000000000) 2 (IntervalRat.scale (835 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-41842550238 / 1000000000000) (-41842550152 / 1000000000000), orderedInterval (-2736252287 / 1000000000000) (-2736252202 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (181219346009329 / 800000000000) 2 (IntervalRat.scale (835 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (47585934280 / 1000000000000) (47585934281 / 1000000000000), orderedInterval (23260708401 / 1000000000000) (23260708402 / 1000000000000)))) (orderedInterval (1224386198 / 1000000000000) (1224386295 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (97460366992143 / 800000000000) 2 (IntervalRat.scale (835 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-6332830081 / 1000000000000) (-6332830079 / 1000000000000), orderedInterval (-71985186229 / 1000000000000) (-71985186227 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (264623855125429 / 800000000000) 2 (IntervalRat.scale (835 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-43517985786 / 1000000000000) (-43517984913 / 1000000000000), orderedInterval (5614261330 / 1000000000000) (5614262203 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (361321250784533 / 800000000000) 2 (IntervalRat.scale (835 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (1776763198 / 1000000000000) (1776763199 / 1000000000000), orderedInterval (37499784686 / 1000000000000) (37499784687 / 1000000000000)))) (orderedInterval (-463577812 / 1000000000000) (-463577755 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (152780653990671 / 800000000000) 2 (IntervalRat.scale (835 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-7107141136 / 1000000000000) (-7107141134 / 1000000000000), orderedInterval (-57278944927 / 1000000000000) (-57278944926 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (621044876343791 / 800000000000) 2 (IntervalRat.scale (835 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-25750272010 / 1000000000000) (-25750272004 / 1000000000000), orderedInterval (-12512828876 / 1000000000000) (-12512828870 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (414829195654369 / 800000000000) 2 (IntervalRat.scale (835 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-28680709921 / 1000000000000) (-28680709920 / 1000000000000), orderedInterval (-20100454915 / 1000000000000) (-20100454914 / 1000000000000)))) (orderedInterval (-15554576530 / 1000000000000) (-15554576288 / 1000000000000))) = true
  rfl'

theorem compactCertificate546_chunkChecks2 :
    compactCertificate546.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate546.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate546_chunkChecks2_0
    compactCertificate546_chunkChecks2_1 compactCertificate546_chunkChecks2_2

theorem compactCertificate546_chunkChecks3_0 :
    compactCertificate546.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (835 / 2) 3 (IntervalRat.scale (835 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-17100130168 / 1000000000000) (-17100130167 / 1000000000000), orderedInterval (-35085417780 / 1000000000000) (-35085417779 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (246022888299467 / 800000000000) 3 (IntervalRat.scale (835 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (19277538783 / 1000000000000) (19277538784 / 1000000000000), orderedInterval (41181444835 / 1000000000000) (41181444836 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (79558747216811 / 160000000000) 3 (IntervalRat.scale (835 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (35652465983 / 1000000000000) (35652467421 / 1000000000000), orderedInterval (-3069368545 / 1000000000000) (-3069367107 / 1000000000000)))) (orderedInterval (14048504781 / 1000000000000) (14048504968 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (71788865215969 / 800000000000) 3 (IntervalRat.scale (835 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (46587510670 / 1000000000000) (46587523001 / 1000000000000), orderedInterval (-70430816834 / 1000000000000) (-70430804504 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (192834989909293 / 800000000000) 3 (IntervalRat.scale (835 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (3800393569 / 1000000000000) (3800393576 / 1000000000000), orderedInterval (-51258825929 / 1000000000000) (-51258825922 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (523584509351481 / 800000000000) 3 (IntervalRat.scale (835 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30266157408 / 1000000000000) (30266175005 / 1000000000000), orderedInterval (-7550998098 / 1000000000000) (-7550980501 / 1000000000000)))) (orderedInterval (-1727928268 / 1000000000000) (-1727923322 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (385669979818753 / 800000000000) 3 (IntervalRat.scale (835 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-29187939321 / 1000000000000) (-29187890165 / 1000000000000), orderedInterval (21677733027 / 1000000000000) (21677782183 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (660852083953669 / 800000000000) 3 (IntervalRat.scale (835 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-15937039309 / 1000000000000) (-15937039308 / 1000000000000), orderedInterval (-22720866165 / 1000000000000) (-22720866164 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (486780653990671 / 800000000000) 3 (IntervalRat.scale (835 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-6678403879 / 1000000000000) (-6678403875 / 1000000000000), orderedInterval (31654381102 / 1000000000000) (31654381106 / 1000000000000)))) (orderedInterval (-7792841137 / 1000000000000) (-7792841004 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate546_chunkChecks3_1 :
    compactCertificate546.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (746846704484833 / 800000000000) 3 (IntervalRat.scale (835 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-25095540210 / 1000000000000) (-25095539968 / 1000000000000), orderedInterval (-7207499015 / 1000000000000) (-7207498772 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (431192145877657 / 800000000000) 3 (IntervalRat.scale (835 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-18793667498 / 1000000000000) (-18793666514 / 1000000000000), orderedInterval (28791250693 / 1000000000000) (28791251676 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (765158029559213 / 800000000000) 3 (IntervalRat.scale (835 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (21029874691 / 1000000000000) (21029880686 / 1000000000000), orderedInterval (-14955991893 / 1000000000000) (-14955985898 / 1000000000000)))) (orderedInterval (6738975014 / 1000000000000) (6738987522 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (714909884903297 / 800000000000) 3 (IntervalRat.scale (835 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (21416360468 / 1000000000000) (21416367128 / 1000000000000), orderedInterval (-15940920534 / 1000000000000) (-15940913874 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (510193427371601 / 800000000000) 3 (IntervalRat.scale (835 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-22302527519 / 1000000000000) (-22302527518 / 1000000000000), orderedInterval (-22361922769 / 1000000000000) (-22361922768 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (578504969727879 / 800000000000) 3 (IntervalRat.scale (835 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (28951465112 / 1000000000000) (28951465240 / 1000000000000), orderedInterval (6474439107 / 1000000000000) (6474439236 / 1000000000000)))) (orderedInterval (4867928571 / 1000000000000) (4867929982 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (482297131584151 / 800000000000) 3 (IntervalRat.scale (835 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (14740547023 / 1000000000000) (14740547024 / 1000000000000), orderedInterval (28948020760 / 1000000000000) (28948020761 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (426124142359171 / 800000000000) 3 (IntervalRat.scale (835 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-20378998637 / 1000000000000) (-20378996772 / 1000000000000), orderedInterval (27945431833 / 1000000000000) (27945433698 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (123507385441929 / 160000000000) 3 (IntervalRat.scale (835 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-3591730862 / 1000000000000) (-3591730861 / 1000000000000), orderedInterval (28494796949 / 1000000000000) (28494796950 / 1000000000000)))) (orderedInterval (-2292080071 / 1000000000000) (-2292079716 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate546_chunkChecks3_2 :
    compactCertificate546.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (341627927969963 / 800000000000) 3 (IntervalRat.scale (835 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (20621076801 / 1000000000000) (20621076802 / 1000000000000), orderedInterval (32618811367 / 1000000000000) (32618811368 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (289601777965843 / 800000000000) 3 (IntervalRat.scale (835 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-41842550238 / 1000000000000) (-41842550152 / 1000000000000), orderedInterval (-2736252287 / 1000000000000) (-2736252202 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (181219346009329 / 800000000000) 3 (IntervalRat.scale (835 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (47585934280 / 1000000000000) (47585934281 / 1000000000000), orderedInterval (23260708401 / 1000000000000) (23260708402 / 1000000000000)))) (orderedInterval (5356190246 / 1000000000000) (5356190340 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (97460366992143 / 800000000000) 3 (IntervalRat.scale (835 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-6332830081 / 1000000000000) (-6332830079 / 1000000000000), orderedInterval (-71985186229 / 1000000000000) (-71985186227 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (264623855125429 / 800000000000) 3 (IntervalRat.scale (835 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-43517985786 / 1000000000000) (-43517984913 / 1000000000000), orderedInterval (5614261330 / 1000000000000) (5614262203 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (361321250784533 / 800000000000) 3 (IntervalRat.scale (835 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (1776763198 / 1000000000000) (1776763199 / 1000000000000), orderedInterval (37499784686 / 1000000000000) (37499784687 / 1000000000000)))) (orderedInterval (3669886239 / 1000000000000) (3669886295 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (152780653990671 / 800000000000) 3 (IntervalRat.scale (835 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-7107141136 / 1000000000000) (-7107141134 / 1000000000000), orderedInterval (-57278944927 / 1000000000000) (-57278944926 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (621044876343791 / 800000000000) 3 (IntervalRat.scale (835 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-25750272010 / 1000000000000) (-25750272004 / 1000000000000), orderedInterval (-12512828876 / 1000000000000) (-12512828870 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (414829195654369 / 800000000000) 3 (IntervalRat.scale (835 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-28680709921 / 1000000000000) (-28680709920 / 1000000000000), orderedInterval (-20100454915 / 1000000000000) (-20100454914 / 1000000000000)))) (orderedInterval (-13703325480 / 1000000000000) (-13703325107 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate546_chunkChecks3 :
    compactCertificate546.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate546.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate546_chunkChecks3_0
    compactCertificate546_chunkChecks3_1 compactCertificate546_chunkChecks3_2

theorem compactCertificate546_chunkChecks4_0 :
    compactCertificate546.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (835 / 2) 4 (IntervalRat.scale (835 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-17100130168 / 1000000000000) (-17100130167 / 1000000000000), orderedInterval (-35085417780 / 1000000000000) (-35085417779 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (246022888299467 / 800000000000) 4 (IntervalRat.scale (835 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (19277538783 / 1000000000000) (19277538784 / 1000000000000), orderedInterval (41181444835 / 1000000000000) (41181444836 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (79558747216811 / 160000000000) 4 (IntervalRat.scale (835 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (35652465983 / 1000000000000) (35652467421 / 1000000000000), orderedInterval (-3069368545 / 1000000000000) (-3069367107 / 1000000000000)))) (orderedInterval (-2582755438 / 1000000000000) (-2582755216 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (71788865215969 / 800000000000) 4 (IntervalRat.scale (835 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (46587510670 / 1000000000000) (46587523001 / 1000000000000), orderedInterval (-70430816834 / 1000000000000) (-70430804504 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (192834989909293 / 800000000000) 4 (IntervalRat.scale (835 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (3800393569 / 1000000000000) (3800393576 / 1000000000000), orderedInterval (-51258825929 / 1000000000000) (-51258825922 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (523584509351481 / 800000000000) 4 (IntervalRat.scale (835 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30266157408 / 1000000000000) (30266175005 / 1000000000000), orderedInterval (-7550998098 / 1000000000000) (-7550980501 / 1000000000000)))) (orderedInterval (-12970823510 / 1000000000000) (-12970815751 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (385669979818753 / 800000000000) 4 (IntervalRat.scale (835 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-29187939321 / 1000000000000) (-29187890165 / 1000000000000), orderedInterval (21677733027 / 1000000000000) (21677782183 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (660852083953669 / 800000000000) 4 (IntervalRat.scale (835 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-15937039309 / 1000000000000) (-15937039308 / 1000000000000), orderedInterval (-22720866165 / 1000000000000) (-22720866164 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (486780653990671 / 800000000000) 4 (IntervalRat.scale (835 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-6678403879 / 1000000000000) (-6678403875 / 1000000000000), orderedInterval (31654381102 / 1000000000000) (31654381106 / 1000000000000)))) (orderedInterval (6842825115 / 1000000000000) (6842825360 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate546_chunkChecks4_1 :
    compactCertificate546.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (746846704484833 / 800000000000) 4 (IntervalRat.scale (835 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-25095540210 / 1000000000000) (-25095539968 / 1000000000000), orderedInterval (-7207499015 / 1000000000000) (-7207498772 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (431192145877657 / 800000000000) 4 (IntervalRat.scale (835 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-18793667498 / 1000000000000) (-18793666514 / 1000000000000), orderedInterval (28791250693 / 1000000000000) (28791251676 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (765158029559213 / 800000000000) 4 (IntervalRat.scale (835 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (21029874691 / 1000000000000) (21029880686 / 1000000000000), orderedInterval (-14955991893 / 1000000000000) (-14955985898 / 1000000000000)))) (orderedInterval (189920717044 / 1000000000000) (189920745424 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (714909884903297 / 800000000000) 4 (IntervalRat.scale (835 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (21416360468 / 1000000000000) (21416367128 / 1000000000000), orderedInterval (-15940920534 / 1000000000000) (-15940913874 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (510193427371601 / 800000000000) 4 (IntervalRat.scale (835 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-22302527519 / 1000000000000) (-22302527518 / 1000000000000), orderedInterval (-22361922769 / 1000000000000) (-22361922768 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (578504969727879 / 800000000000) 4 (IntervalRat.scale (835 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (28951465112 / 1000000000000) (28951465240 / 1000000000000), orderedInterval (6474439107 / 1000000000000) (6474439236 / 1000000000000)))) (orderedInterval (-20939686880 / 1000000000000) (-20939683951 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (482297131584151 / 800000000000) 4 (IntervalRat.scale (835 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (14740547023 / 1000000000000) (14740547024 / 1000000000000), orderedInterval (28948020760 / 1000000000000) (28948020761 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (426124142359171 / 800000000000) 4 (IntervalRat.scale (835 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-20378998637 / 1000000000000) (-20378996772 / 1000000000000), orderedInterval (27945431833 / 1000000000000) (27945433698 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (123507385441929 / 160000000000) 4 (IntervalRat.scale (835 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-3591730862 / 1000000000000) (-3591730861 / 1000000000000), orderedInterval (28494796949 / 1000000000000) (28494796950 / 1000000000000)))) (orderedInterval (2766247440 / 1000000000000) (2766247935 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate546_chunkChecks4_2 :
    compactCertificate546.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (341627927969963 / 800000000000) 4 (IntervalRat.scale (835 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (20621076801 / 1000000000000) (20621076802 / 1000000000000), orderedInterval (32618811367 / 1000000000000) (32618811368 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (289601777965843 / 800000000000) 4 (IntervalRat.scale (835 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-41842550238 / 1000000000000) (-41842550152 / 1000000000000), orderedInterval (-2736252287 / 1000000000000) (-2736252202 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (181219346009329 / 800000000000) 4 (IntervalRat.scale (835 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (47585934280 / 1000000000000) (47585934281 / 1000000000000), orderedInterval (23260708401 / 1000000000000) (23260708402 / 1000000000000)))) (orderedInterval (-2161621999 / 1000000000000) (-2161621907 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (97460366992143 / 800000000000) 4 (IntervalRat.scale (835 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-6332830081 / 1000000000000) (-6332830079 / 1000000000000), orderedInterval (-71985186229 / 1000000000000) (-71985186227 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (264623855125429 / 800000000000) 4 (IntervalRat.scale (835 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-43517985786 / 1000000000000) (-43517984913 / 1000000000000), orderedInterval (5614261330 / 1000000000000) (5614262203 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (361321250784533 / 800000000000) 4 (IntervalRat.scale (835 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (1776763198 / 1000000000000) (1776763199 / 1000000000000), orderedInterval (37499784686 / 1000000000000) (37499784687 / 1000000000000)))) (orderedInterval (185791233 / 1000000000000) (185791289 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (152780653990671 / 800000000000) 4 (IntervalRat.scale (835 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-7107141136 / 1000000000000) (-7107141134 / 1000000000000), orderedInterval (-57278944927 / 1000000000000) (-57278944926 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (621044876343791 / 800000000000) 4 (IntervalRat.scale (835 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-25750272010 / 1000000000000) (-25750272004 / 1000000000000), orderedInterval (-12512828876 / 1000000000000) (-12512828870 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (414829195654369 / 800000000000) 4 (IntervalRat.scale (835 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-28680709921 / 1000000000000) (-28680709920 / 1000000000000), orderedInterval (-20100454915 / 1000000000000) (-20100454914 / 1000000000000)))) (orderedInterval (37925138471 / 1000000000000) (37925139072 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate546_chunkChecks4 :
    compactCertificate546.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate546.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate546_chunkChecks4_0
    compactCertificate546_chunkChecks4_1 compactCertificate546_chunkChecks4_2

theorem compactCertificate546_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate546.chunkCheck r b = true :=
  compactCertificate546.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate546_chunkChecks0
    · exact compactCertificate546_chunkChecks1
    · exact compactCertificate546_chunkChecks2
    · exact compactCertificate546_chunkChecks3
    · exact compactCertificate546_chunkChecks4)

theorem compactCertificate546_coefficient0 :
    compactCertificate546.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate546_coefficient1 :
    compactCertificate546.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate546_coefficient2 :
    compactCertificate546.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate546_coefficient3 :
    compactCertificate546.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate546_coefficient4 :
    compactCertificate546.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate546_coefficients : ∀ r : Fin 5,
    compactCertificate546.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate546_coefficient0
  · exact compactCertificate546_coefficient1
  · exact compactCertificate546_coefficient2
  · exact compactCertificate546_coefficient3
  · exact compactCertificate546_coefficient4

theorem compactCertificate546_lower : (1 : ℚ) ≤ compactCertificate546.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate546, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate546_proves {t : ℝ} (ht : t ∈ compactCertificate546.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate546.proves compactCertificate546_states compactCertificate546_chunks
    compactCertificate546_coefficients compactCertificate546_lower ht

end Erdos232
