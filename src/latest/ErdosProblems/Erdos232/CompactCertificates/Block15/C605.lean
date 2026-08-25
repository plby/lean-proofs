/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate605 : CompactCertificate where
  left := 476
  right := 477
  center := 953 / 2
  grid := fun i =>
    match i.val with
    | 0 => 152
    | 1 => 112
    | 2 => 181
    | 3 => 33
    | 4 => 88
    | 5 => 238
    | 6 => 175
    | 7 => 300
    | 8 => 221
    | 9 => 339
    | 10 => 196
    | 11 => 348
    | 12 => 325
    | 13 => 232
    | 14 => 263
    | 15 => 219
    | 16 => 194
    | 17 => 281
    | 18 => 155
    | 19 => 132
    | 20 => 82
    | 21 => 44
    | 22 => 120
    | 23 => 164
    | 24 => 69
    | 25 => 282
    | _ => 188
  point := fun i =>
    match i.val with
    | 0 => 953 / 2
    | 1 => 1403950973349653 / 4000000000000
    | 2 => 454008898788149 / 800000000000
    | 3 => 409669392519871 / 4000000000000
    | 4 => 1100429613075187 / 4000000000000
    | 5 => 2987880463544679 / 4000000000000
    | 6 => 2200859226151327 / 4000000000000
    | 7 => 3771209796454171 / 4000000000000
    | 8 => 2777856067383889 / 4000000000000
    | 9 => 4261945565114047 / 4000000000000
    | 10 => 2460635419289863 / 4000000000000
    | 11 => 4366440731556467 / 4000000000000
    | 12 => 4079695331214623 / 4000000000000
    | 13 => 2911463091527759 / 4000000000000
    | 14 => 3301288839225561 / 4000000000000
    | 15 => 2752270457483209 / 4000000000000
    | 16 => 2431714417175389 / 4000000000000
    | 17 => 704805618719511 / 800000000000
    | 18 => 1949529433265717 / 4000000000000
    | 19 => 1652637691026637 / 4000000000000
    | 20 => 1034143932616111 / 4000000000000
    | 21 => 556166046368337 / 4000000000000
    | 22 => 1510099005596011 / 4000000000000
    | 23 => 2061911089806347 / 4000000000000
    | 24 => 871856067383889 / 4000000000000
    | 25 => 3544046509913969 / 4000000000000
    | _ => 2367258823105471 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-8580037013 / 1000000000000) (-8580036999 / 1000000000000), orderedInterval (35539507246 / 1000000000000) (35539507260 / 1000000000000))
    | 1 => (orderedInterval (-3640791559 / 1000000000000) (-3640791555 / 1000000000000), orderedInterval (42437972531 / 1000000000000) (42437972535 / 1000000000000))
    | 2 => (orderedInterval (10915506861 / 1000000000000) (10915506890 / 1000000000000), orderedInterval (-31673903204 / 1000000000000) (-31673903175 / 1000000000000))
    | 3 => (orderedInterval (35778391470 / 1000000000000) (35778395007 / 1000000000000), orderedInterval (-70430535321 / 1000000000000) (-70430531783 / 1000000000000))
    | 4 => (orderedInterval (-25870002574 / 1000000000000) (-25869998637 / 1000000000000), orderedInterval (40603419591 / 1000000000000) (40603423529 / 1000000000000))
    | 5 => (orderedInterval (1642593068 / 1000000000000) (1642593069 / 1000000000000), orderedInterval (29146309945 / 1000000000000) (29146309946 / 1000000000000))
    | 6 => (orderedInterval (-31958451339 / 1000000000000) (-31958451334 / 1000000000000), orderedInterval (-11619804859 / 1000000000000) (-11619804854 / 1000000000000))
    | 7 => (orderedInterval (23274162837 / 1000000000000) (23274162856 / 1000000000000), orderedInterval (11544267366 / 1000000000000) (11544267386 / 1000000000000))
    | 8 => (orderedInterval (-24755097082 / 1000000000000) (-24755097081 / 1000000000000), orderedInterval (-17414667310 / 1000000000000) (-17414667309 / 1000000000000))
    | 9 => (orderedInterval (-23358881225 / 1000000000000) (-23358880773 / 1000000000000), orderedInterval (-7190065666 / 1000000000000) (-7190065214 / 1000000000000))
    | 10 => (orderedInterval (6135210335 / 1000000000000) (6135210336 / 1000000000000), orderedInterval (31574220093 / 1000000000000) (31574220094 / 1000000000000))
    | 11 => (orderedInterval (-18594044568 / 1000000000000) (-18594043323 / 1000000000000), orderedInterval (15418086022 / 1000000000000) (15418087268 / 1000000000000))
    | 12 => (orderedInterval (7585880747 / 1000000000000) (7585880749 / 1000000000000), orderedInterval (-23807880590 / 1000000000000) (-23807880588 / 1000000000000))
    | 13 => (orderedInterval (-5831914481 / 1000000000000) (-5831914479 / 1000000000000), orderedInterval (28997590587 / 1000000000000) (28997590588 / 1000000000000))
    | 14 => (orderedInterval (3639238711 / 1000000000000) (3639238712 / 1000000000000), orderedInterval (-27536095645 / 1000000000000) (-27536095644 / 1000000000000))
    | 15 => (orderedInterval (-22732062502 / 1000000000000) (-22732062501 / 1000000000000), orderedInterval (-20194414271 / 1000000000000) (-20194414270 / 1000000000000))
    | 16 => (orderedInterval (-22180402001 / 1000000000000) (-22180397192 / 1000000000000), orderedInterval (23581449935 / 1000000000000) (23581454744 / 1000000000000))
    | 17 => (orderedInterval (22550674314 / 1000000000000) (22550687787 / 1000000000000), orderedInterval (-14643983266 / 1000000000000) (-14643969793 / 1000000000000))
    | 18 => (orderedInterval (-33948296833 / 1000000000000) (-33948296830 / 1000000000000), orderedInterval (-12363339546 / 1000000000000) (-12363339543 / 1000000000000))
    | 19 => (orderedInterval (-26633471850 / 1000000000000) (-26633459918 / 1000000000000), orderedInterval (28868244797 / 1000000000000) (28868256729 / 1000000000000))
    | 20 => (orderedInterval (49140480509 / 1000000000000) (49140481162 / 1000000000000), orderedInterval (-6995158030 / 1000000000000) (-6995157377 / 1000000000000))
    | 21 => (orderedInterval (67643985319 / 1000000000000) (67643985382 / 1000000000000), orderedInterval (-1944030231 / 1000000000000) (-1944030168 / 1000000000000))
    | 22 => (orderedInterval (39766575815 / 1000000000000) (39766575821 / 1000000000000), orderedInterval (10190260917 / 1000000000000) (10190260923 / 1000000000000))
    | 23 => (orderedInterval (30337986709 / 1000000000000) (30337986710 / 1000000000000), orderedInterval (17707975276 / 1000000000000) (17707975278 / 1000000000000))
    | 24 => (orderedInterval (-49604560911 / 1000000000000) (-49604550784 / 1000000000000), orderedInterval (21564636646 / 1000000000000) (21564646773 / 1000000000000))
    | 25 => (orderedInterval (20449215422 / 1000000000000) (20449215423 / 1000000000000), orderedInterval (17319144162 / 1000000000000) (17319144163 / 1000000000000))
    | _ => (orderedInterval (30083894869 / 1000000000000) (30083954570 / 1000000000000), orderedInterval (-13089331040 / 1000000000000) (-13089271339 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-2794217055 / 1000000000000) (-2794217015 / 1000000000000)
      | 1 => orderedInterval (-1449500562 / 1000000000000) (-1449500323 / 1000000000000)
      | 2 => orderedInterval (-1316150171 / 1000000000000) (-1316150143 / 1000000000000)
      | 3 => orderedInterval (1961906592 / 1000000000000) (1961907038 / 1000000000000)
      | 4 => orderedInterval (-706847778 / 1000000000000) (-706847720 / 1000000000000)
      | 5 => orderedInterval (1584194384 / 1000000000000) (1584195050 / 1000000000000)
      | 6 => orderedInterval (8535310342 / 1000000000000) (8535311158 / 1000000000000)
      | 7 => orderedInterval (-4476301970 / 1000000000000) (-4476301912 / 1000000000000)
      | _ => orderedInterval (-7608183018 / 1000000000000) (-7608171623 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (12164232040 / 1000000000000) (12164232085 / 1000000000000)
      | 1 => orderedInterval (-2227945731 / 1000000000000) (-2227945574 / 1000000000000)
      | 2 => orderedInterval (-1317921773 / 1000000000000) (-1317921725 / 1000000000000)
      | 3 => orderedInterval (10898025356 / 1000000000000) (10898026332 / 1000000000000)
      | 4 => orderedInterval (5349955471 / 1000000000000) (5349955564 / 1000000000000)
      | 5 => orderedInterval (-2751683052 / 1000000000000) (-2751681996 / 1000000000000)
      | 6 => orderedInterval (481647155 / 1000000000000) (481647863 / 1000000000000)
      | 7 => orderedInterval (-1640822121 / 1000000000000) (-1640822069 / 1000000000000)
      | _ => orderedInterval (488273294 / 1000000000000) (488287420 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (2485120183 / 1000000000000) (2485120234 / 1000000000000)
      | 1 => orderedInterval (624418232 / 1000000000000) (624418372 / 1000000000000)
      | 2 => orderedInterval (4083922307 / 1000000000000) (4083922392 / 1000000000000)
      | 3 => orderedInterval (-7661155024 / 1000000000000) (-7661152853 / 1000000000000)
      | 4 => orderedInterval (1958247534 / 1000000000000) (1958247687 / 1000000000000)
      | 5 => orderedInterval (-3486734641 / 1000000000000) (-3486732913 / 1000000000000)
      | 6 => orderedInterval (-7284126548 / 1000000000000) (-7284125927 / 1000000000000)
      | 7 => orderedInterval (3397118318 / 1000000000000) (3397118370 / 1000000000000)
      | _ => orderedInterval (14523895593 / 1000000000000) (14523913188 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-11109783028 / 1000000000000) (-11109782970 / 1000000000000)
      | 1 => orderedInterval (7687768909 / 1000000000000) (7687769072 / 1000000000000)
      | 2 => orderedInterval (4052443900 / 1000000000000) (4052444055 / 1000000000000)
      | 3 => orderedInterval (-45653052302 / 1000000000000) (-45653047434 / 1000000000000)
      | 4 => orderedInterval (-14716502634 / 1000000000000) (-14716502375 / 1000000000000)
      | 5 => orderedInterval (5881726016 / 1000000000000) (5881728923 / 1000000000000)
      | 6 => orderedInterval (-998572331 / 1000000000000) (-998571783 / 1000000000000)
      | 7 => orderedInterval (1825089833 / 1000000000000) (1825089886 / 1000000000000)
      | _ => orderedInterval (4315229040 / 1000000000000) (4315250965 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-2075363431 / 1000000000000) (-2075363363 / 1000000000000)
      | 1 => orderedInterval (-843220551 / 1000000000000) (-843220327 / 1000000000000)
      | 2 => orderedInterval (-13718413648 / 1000000000000) (-13718413360 / 1000000000000)
      | 3 => orderedInterval (32414683670 / 1000000000000) (32414694647 / 1000000000000)
      | 4 => orderedInterval (-5981084286 / 1000000000000) (-5981083835 / 1000000000000)
      | 5 => orderedInterval (8944314853 / 1000000000000) (8944319865 / 1000000000000)
      | 6 => orderedInterval (6936037103 / 1000000000000) (6936037590 / 1000000000000)
      | 7 => orderedInterval (-3556560538 / 1000000000000) (-3556560483 / 1000000000000)
      | _ => orderedInterval (-33360846845 / 1000000000000) (-33360819419 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-6269789236 / 1000000000000) (-6269775490 / 1000000000000)
    | 1 => orderedInterval (21443760639 / 1000000000000) (21443777900 / 1000000000000)
    | 2 => orderedInterval (8640705954 / 1000000000000) (8640728550 / 1000000000000)
    | 3 => orderedInterval (-48715652597 / 1000000000000) (-48715621661 / 1000000000000)
    | _ => orderedInterval (-11240453673 / 1000000000000) (-11240408685 / 1000000000000)

theorem compactCertificate605_stateChecks0 :
    compactCertificate605.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 152 12 (953 / 2)) (orderedInterval (-8580037013 / 1000000000000) (-8580036999 / 1000000000000), orderedInterval (35539507246 / 1000000000000) (35539507260 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 112 12 (1403950973349653 / 4000000000000)) (orderedInterval (-3640791559 / 1000000000000) (-3640791555 / 1000000000000), orderedInterval (42437972531 / 1000000000000) (42437972535 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 181 12 (454008898788149 / 800000000000)) (orderedInterval (10915506861 / 1000000000000) (10915506890 / 1000000000000), orderedInterval (-31673903204 / 1000000000000) (-31673903175 / 1000000000000))) = true
  rfl'

theorem compactCertificate605_stateChecks1 :
    compactCertificate605.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 33 12 (409669392519871 / 4000000000000)) (orderedInterval (35778391470 / 1000000000000) (35778395007 / 1000000000000), orderedInterval (-70430535321 / 1000000000000) (-70430531783 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 88 12 (1100429613075187 / 4000000000000)) (orderedInterval (-25870002574 / 1000000000000) (-25869998637 / 1000000000000), orderedInterval (40603419591 / 1000000000000) (40603423529 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 238 12 (2987880463544679 / 4000000000000)) (orderedInterval (1642593068 / 1000000000000) (1642593069 / 1000000000000), orderedInterval (29146309945 / 1000000000000) (29146309946 / 1000000000000))) = true
  rfl'

theorem compactCertificate605_stateChecks2 :
    compactCertificate605.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 175 12 (2200859226151327 / 4000000000000)) (orderedInterval (-31958451339 / 1000000000000) (-31958451334 / 1000000000000), orderedInterval (-11619804859 / 1000000000000) (-11619804854 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 300 12 (3771209796454171 / 4000000000000)) (orderedInterval (23274162837 / 1000000000000) (23274162856 / 1000000000000), orderedInterval (11544267366 / 1000000000000) (11544267386 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 221 12 (2777856067383889 / 4000000000000)) (orderedInterval (-24755097082 / 1000000000000) (-24755097081 / 1000000000000), orderedInterval (-17414667310 / 1000000000000) (-17414667309 / 1000000000000))) = true
  rfl'

theorem compactCertificate605_stateChecks3 :
    compactCertificate605.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 339 12 (4261945565114047 / 4000000000000)) (orderedInterval (-23358881225 / 1000000000000) (-23358880773 / 1000000000000), orderedInterval (-7190065666 / 1000000000000) (-7190065214 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 196 12 (2460635419289863 / 4000000000000)) (orderedInterval (6135210335 / 1000000000000) (6135210336 / 1000000000000), orderedInterval (31574220093 / 1000000000000) (31574220094 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 348 12 (4366440731556467 / 4000000000000)) (orderedInterval (-18594044568 / 1000000000000) (-18594043323 / 1000000000000), orderedInterval (15418086022 / 1000000000000) (15418087268 / 1000000000000))) = true
  rfl'

theorem compactCertificate605_stateChecks4 :
    compactCertificate605.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 325 12 (4079695331214623 / 4000000000000)) (orderedInterval (7585880747 / 1000000000000) (7585880749 / 1000000000000), orderedInterval (-23807880590 / 1000000000000) (-23807880588 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 232 12 (2911463091527759 / 4000000000000)) (orderedInterval (-5831914481 / 1000000000000) (-5831914479 / 1000000000000), orderedInterval (28997590587 / 1000000000000) (28997590588 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 263 12 (3301288839225561 / 4000000000000)) (orderedInterval (3639238711 / 1000000000000) (3639238712 / 1000000000000), orderedInterval (-27536095645 / 1000000000000) (-27536095644 / 1000000000000))) = true
  rfl'

theorem compactCertificate605_stateChecks5 :
    compactCertificate605.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 219 12 (2752270457483209 / 4000000000000)) (orderedInterval (-22732062502 / 1000000000000) (-22732062501 / 1000000000000), orderedInterval (-20194414271 / 1000000000000) (-20194414270 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 194 12 (2431714417175389 / 4000000000000)) (orderedInterval (-22180402001 / 1000000000000) (-22180397192 / 1000000000000), orderedInterval (23581449935 / 1000000000000) (23581454744 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 281 12 (704805618719511 / 800000000000)) (orderedInterval (22550674314 / 1000000000000) (22550687787 / 1000000000000), orderedInterval (-14643983266 / 1000000000000) (-14643969793 / 1000000000000))) = true
  rfl'

theorem compactCertificate605_stateChecks6 :
    compactCertificate605.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 155 12 (1949529433265717 / 4000000000000)) (orderedInterval (-33948296833 / 1000000000000) (-33948296830 / 1000000000000), orderedInterval (-12363339546 / 1000000000000) (-12363339543 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 132 12 (1652637691026637 / 4000000000000)) (orderedInterval (-26633471850 / 1000000000000) (-26633459918 / 1000000000000), orderedInterval (28868244797 / 1000000000000) (28868256729 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 82 12 (1034143932616111 / 4000000000000)) (orderedInterval (49140480509 / 1000000000000) (49140481162 / 1000000000000), orderedInterval (-6995158030 / 1000000000000) (-6995157377 / 1000000000000))) = true
  rfl'

theorem compactCertificate605_stateChecks7 :
    compactCertificate605.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 44 12 (556166046368337 / 4000000000000)) (orderedInterval (67643985319 / 1000000000000) (67643985382 / 1000000000000), orderedInterval (-1944030231 / 1000000000000) (-1944030168 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 120 12 (1510099005596011 / 4000000000000)) (orderedInterval (39766575815 / 1000000000000) (39766575821 / 1000000000000), orderedInterval (10190260917 / 1000000000000) (10190260923 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 164 12 (2061911089806347 / 4000000000000)) (orderedInterval (30337986709 / 1000000000000) (30337986710 / 1000000000000), orderedInterval (17707975276 / 1000000000000) (17707975278 / 1000000000000))) = true
  rfl'

theorem compactCertificate605_stateChecks8 :
    compactCertificate605.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (871856067383889 / 4000000000000)) (orderedInterval (-49604560911 / 1000000000000) (-49604550784 / 1000000000000), orderedInterval (21564636646 / 1000000000000) (21564646773 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 282 12 (3544046509913969 / 4000000000000)) (orderedInterval (20449215422 / 1000000000000) (20449215423 / 1000000000000), orderedInterval (17319144162 / 1000000000000) (17319144163 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 188 12 (2367258823105471 / 4000000000000)) (orderedInterval (30083894869 / 1000000000000) (30083954570 / 1000000000000), orderedInterval (-13089331040 / 1000000000000) (-13089271339 / 1000000000000))) = true
  rfl'

theorem compactCertificate605_states : ∀ j,
    BesselStateValid (compactCertificate605.point j) (compactCertificate605.state j) :=
  compactCertificate605.statesValid_of_checks3 compactCertificate605_stateChecks0
    compactCertificate605_stateChecks1 compactCertificate605_stateChecks2
    compactCertificate605_stateChecks3 compactCertificate605_stateChecks4
    compactCertificate605_stateChecks5 compactCertificate605_stateChecks6
    compactCertificate605_stateChecks7 compactCertificate605_stateChecks8

theorem compactCertificate605_chunkChecks0_0 :
    compactCertificate605.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (953 / 2) 0 (IntervalRat.scale (953 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-8580037013 / 1000000000000) (-8580036999 / 1000000000000), orderedInterval (35539507246 / 1000000000000) (35539507260 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1403950973349653 / 4000000000000) 0 (IntervalRat.scale (953 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-3640791559 / 1000000000000) (-3640791555 / 1000000000000), orderedInterval (42437972531 / 1000000000000) (42437972535 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (454008898788149 / 800000000000) 0 (IntervalRat.scale (953 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (10915506861 / 1000000000000) (10915506890 / 1000000000000), orderedInterval (-31673903204 / 1000000000000) (-31673903175 / 1000000000000)))) (orderedInterval (-2794217055 / 1000000000000) (-2794217015 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (409669392519871 / 4000000000000) 0 (IntervalRat.scale (953 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (35778391470 / 1000000000000) (35778395007 / 1000000000000), orderedInterval (-70430535321 / 1000000000000) (-70430531783 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (1100429613075187 / 4000000000000) 0 (IntervalRat.scale (953 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-25870002574 / 1000000000000) (-25869998637 / 1000000000000), orderedInterval (40603419591 / 1000000000000) (40603423529 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2987880463544679 / 4000000000000) 0 (IntervalRat.scale (953 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (1642593068 / 1000000000000) (1642593069 / 1000000000000), orderedInterval (29146309945 / 1000000000000) (29146309946 / 1000000000000)))) (orderedInterval (-1449500562 / 1000000000000) (-1449500323 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (2200859226151327 / 4000000000000) 0 (IntervalRat.scale (953 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-31958451339 / 1000000000000) (-31958451334 / 1000000000000), orderedInterval (-11619804859 / 1000000000000) (-11619804854 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3771209796454171 / 4000000000000) 0 (IntervalRat.scale (953 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (23274162837 / 1000000000000) (23274162856 / 1000000000000), orderedInterval (11544267366 / 1000000000000) (11544267386 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2777856067383889 / 4000000000000) 0 (IntervalRat.scale (953 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-24755097082 / 1000000000000) (-24755097081 / 1000000000000), orderedInterval (-17414667310 / 1000000000000) (-17414667309 / 1000000000000)))) (orderedInterval (-1316150171 / 1000000000000) (-1316150143 / 1000000000000))) = true
  rfl'

theorem compactCertificate605_chunkChecks0_1 :
    compactCertificate605.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (4261945565114047 / 4000000000000) 0 (IntervalRat.scale (953 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-23358881225 / 1000000000000) (-23358880773 / 1000000000000), orderedInterval (-7190065666 / 1000000000000) (-7190065214 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2460635419289863 / 4000000000000) 0 (IntervalRat.scale (953 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (6135210335 / 1000000000000) (6135210336 / 1000000000000), orderedInterval (31574220093 / 1000000000000) (31574220094 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (4366440731556467 / 4000000000000) 0 (IntervalRat.scale (953 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-18594044568 / 1000000000000) (-18594043323 / 1000000000000), orderedInterval (15418086022 / 1000000000000) (15418087268 / 1000000000000)))) (orderedInterval (1961906592 / 1000000000000) (1961907038 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (4079695331214623 / 4000000000000) 0 (IntervalRat.scale (953 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (7585880747 / 1000000000000) (7585880749 / 1000000000000), orderedInterval (-23807880590 / 1000000000000) (-23807880588 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2911463091527759 / 4000000000000) 0 (IntervalRat.scale (953 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-5831914481 / 1000000000000) (-5831914479 / 1000000000000), orderedInterval (28997590587 / 1000000000000) (28997590588 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (3301288839225561 / 4000000000000) 0 (IntervalRat.scale (953 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (3639238711 / 1000000000000) (3639238712 / 1000000000000), orderedInterval (-27536095645 / 1000000000000) (-27536095644 / 1000000000000)))) (orderedInterval (-706847778 / 1000000000000) (-706847720 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2752270457483209 / 4000000000000) 0 (IntervalRat.scale (953 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-22732062502 / 1000000000000) (-22732062501 / 1000000000000), orderedInterval (-20194414271 / 1000000000000) (-20194414270 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2431714417175389 / 4000000000000) 0 (IntervalRat.scale (953 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-22180402001 / 1000000000000) (-22180397192 / 1000000000000), orderedInterval (23581449935 / 1000000000000) (23581454744 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (704805618719511 / 800000000000) 0 (IntervalRat.scale (953 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (22550674314 / 1000000000000) (22550687787 / 1000000000000), orderedInterval (-14643983266 / 1000000000000) (-14643969793 / 1000000000000)))) (orderedInterval (1584194384 / 1000000000000) (1584195050 / 1000000000000))) = true
  rfl'

theorem compactCertificate605_chunkChecks0_2 :
    compactCertificate605.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1949529433265717 / 4000000000000) 0 (IntervalRat.scale (953 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-33948296833 / 1000000000000) (-33948296830 / 1000000000000), orderedInterval (-12363339546 / 1000000000000) (-12363339543 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1652637691026637 / 4000000000000) 0 (IntervalRat.scale (953 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-26633471850 / 1000000000000) (-26633459918 / 1000000000000), orderedInterval (28868244797 / 1000000000000) (28868256729 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (1034143932616111 / 4000000000000) 0 (IntervalRat.scale (953 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (49140480509 / 1000000000000) (49140481162 / 1000000000000), orderedInterval (-6995158030 / 1000000000000) (-6995157377 / 1000000000000)))) (orderedInterval (8535310342 / 1000000000000) (8535311158 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (556166046368337 / 4000000000000) 0 (IntervalRat.scale (953 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (67643985319 / 1000000000000) (67643985382 / 1000000000000), orderedInterval (-1944030231 / 1000000000000) (-1944030168 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1510099005596011 / 4000000000000) 0 (IntervalRat.scale (953 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (39766575815 / 1000000000000) (39766575821 / 1000000000000), orderedInterval (10190260917 / 1000000000000) (10190260923 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (2061911089806347 / 4000000000000) 0 (IntervalRat.scale (953 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (30337986709 / 1000000000000) (30337986710 / 1000000000000), orderedInterval (17707975276 / 1000000000000) (17707975278 / 1000000000000)))) (orderedInterval (-4476301970 / 1000000000000) (-4476301912 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (871856067383889 / 4000000000000) 0 (IntervalRat.scale (953 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-49604560911 / 1000000000000) (-49604550784 / 1000000000000), orderedInterval (21564636646 / 1000000000000) (21564646773 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3544046509913969 / 4000000000000) 0 (IntervalRat.scale (953 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (20449215422 / 1000000000000) (20449215423 / 1000000000000), orderedInterval (17319144162 / 1000000000000) (17319144163 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2367258823105471 / 4000000000000) 0 (IntervalRat.scale (953 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (30083894869 / 1000000000000) (30083954570 / 1000000000000), orderedInterval (-13089331040 / 1000000000000) (-13089271339 / 1000000000000)))) (orderedInterval (-7608183018 / 1000000000000) (-7608171623 / 1000000000000))) = true
  rfl'

theorem compactCertificate605_chunkChecks0 :
    compactCertificate605.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate605.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate605_chunkChecks0_0
    compactCertificate605_chunkChecks0_1 compactCertificate605_chunkChecks0_2

theorem compactCertificate605_chunkChecks1_0 :
    compactCertificate605.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (953 / 2) 1 (IntervalRat.scale (953 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-8580037013 / 1000000000000) (-8580036999 / 1000000000000), orderedInterval (35539507246 / 1000000000000) (35539507260 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1403950973349653 / 4000000000000) 1 (IntervalRat.scale (953 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-3640791559 / 1000000000000) (-3640791555 / 1000000000000), orderedInterval (42437972531 / 1000000000000) (42437972535 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (454008898788149 / 800000000000) 1 (IntervalRat.scale (953 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (10915506861 / 1000000000000) (10915506890 / 1000000000000), orderedInterval (-31673903204 / 1000000000000) (-31673903175 / 1000000000000)))) (orderedInterval (12164232040 / 1000000000000) (12164232085 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (409669392519871 / 4000000000000) 1 (IntervalRat.scale (953 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (35778391470 / 1000000000000) (35778395007 / 1000000000000), orderedInterval (-70430535321 / 1000000000000) (-70430531783 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (1100429613075187 / 4000000000000) 1 (IntervalRat.scale (953 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-25870002574 / 1000000000000) (-25869998637 / 1000000000000), orderedInterval (40603419591 / 1000000000000) (40603423529 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2987880463544679 / 4000000000000) 1 (IntervalRat.scale (953 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (1642593068 / 1000000000000) (1642593069 / 1000000000000), orderedInterval (29146309945 / 1000000000000) (29146309946 / 1000000000000)))) (orderedInterval (-2227945731 / 1000000000000) (-2227945574 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (2200859226151327 / 4000000000000) 1 (IntervalRat.scale (953 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-31958451339 / 1000000000000) (-31958451334 / 1000000000000), orderedInterval (-11619804859 / 1000000000000) (-11619804854 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3771209796454171 / 4000000000000) 1 (IntervalRat.scale (953 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (23274162837 / 1000000000000) (23274162856 / 1000000000000), orderedInterval (11544267366 / 1000000000000) (11544267386 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2777856067383889 / 4000000000000) 1 (IntervalRat.scale (953 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-24755097082 / 1000000000000) (-24755097081 / 1000000000000), orderedInterval (-17414667310 / 1000000000000) (-17414667309 / 1000000000000)))) (orderedInterval (-1317921773 / 1000000000000) (-1317921725 / 1000000000000))) = true
  rfl'

theorem compactCertificate605_chunkChecks1_1 :
    compactCertificate605.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (4261945565114047 / 4000000000000) 1 (IntervalRat.scale (953 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-23358881225 / 1000000000000) (-23358880773 / 1000000000000), orderedInterval (-7190065666 / 1000000000000) (-7190065214 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2460635419289863 / 4000000000000) 1 (IntervalRat.scale (953 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (6135210335 / 1000000000000) (6135210336 / 1000000000000), orderedInterval (31574220093 / 1000000000000) (31574220094 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (4366440731556467 / 4000000000000) 1 (IntervalRat.scale (953 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-18594044568 / 1000000000000) (-18594043323 / 1000000000000), orderedInterval (15418086022 / 1000000000000) (15418087268 / 1000000000000)))) (orderedInterval (10898025356 / 1000000000000) (10898026332 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (4079695331214623 / 4000000000000) 1 (IntervalRat.scale (953 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (7585880747 / 1000000000000) (7585880749 / 1000000000000), orderedInterval (-23807880590 / 1000000000000) (-23807880588 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2911463091527759 / 4000000000000) 1 (IntervalRat.scale (953 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-5831914481 / 1000000000000) (-5831914479 / 1000000000000), orderedInterval (28997590587 / 1000000000000) (28997590588 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (3301288839225561 / 4000000000000) 1 (IntervalRat.scale (953 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (3639238711 / 1000000000000) (3639238712 / 1000000000000), orderedInterval (-27536095645 / 1000000000000) (-27536095644 / 1000000000000)))) (orderedInterval (5349955471 / 1000000000000) (5349955564 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2752270457483209 / 4000000000000) 1 (IntervalRat.scale (953 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-22732062502 / 1000000000000) (-22732062501 / 1000000000000), orderedInterval (-20194414271 / 1000000000000) (-20194414270 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2431714417175389 / 4000000000000) 1 (IntervalRat.scale (953 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-22180402001 / 1000000000000) (-22180397192 / 1000000000000), orderedInterval (23581449935 / 1000000000000) (23581454744 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (704805618719511 / 800000000000) 1 (IntervalRat.scale (953 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (22550674314 / 1000000000000) (22550687787 / 1000000000000), orderedInterval (-14643983266 / 1000000000000) (-14643969793 / 1000000000000)))) (orderedInterval (-2751683052 / 1000000000000) (-2751681996 / 1000000000000))) = true
  rfl'

theorem compactCertificate605_chunkChecks1_2 :
    compactCertificate605.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1949529433265717 / 4000000000000) 1 (IntervalRat.scale (953 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-33948296833 / 1000000000000) (-33948296830 / 1000000000000), orderedInterval (-12363339546 / 1000000000000) (-12363339543 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1652637691026637 / 4000000000000) 1 (IntervalRat.scale (953 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-26633471850 / 1000000000000) (-26633459918 / 1000000000000), orderedInterval (28868244797 / 1000000000000) (28868256729 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (1034143932616111 / 4000000000000) 1 (IntervalRat.scale (953 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (49140480509 / 1000000000000) (49140481162 / 1000000000000), orderedInterval (-6995158030 / 1000000000000) (-6995157377 / 1000000000000)))) (orderedInterval (481647155 / 1000000000000) (481647863 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (556166046368337 / 4000000000000) 1 (IntervalRat.scale (953 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (67643985319 / 1000000000000) (67643985382 / 1000000000000), orderedInterval (-1944030231 / 1000000000000) (-1944030168 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1510099005596011 / 4000000000000) 1 (IntervalRat.scale (953 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (39766575815 / 1000000000000) (39766575821 / 1000000000000), orderedInterval (10190260917 / 1000000000000) (10190260923 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (2061911089806347 / 4000000000000) 1 (IntervalRat.scale (953 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (30337986709 / 1000000000000) (30337986710 / 1000000000000), orderedInterval (17707975276 / 1000000000000) (17707975278 / 1000000000000)))) (orderedInterval (-1640822121 / 1000000000000) (-1640822069 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (871856067383889 / 4000000000000) 1 (IntervalRat.scale (953 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-49604560911 / 1000000000000) (-49604550784 / 1000000000000), orderedInterval (21564636646 / 1000000000000) (21564646773 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3544046509913969 / 4000000000000) 1 (IntervalRat.scale (953 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (20449215422 / 1000000000000) (20449215423 / 1000000000000), orderedInterval (17319144162 / 1000000000000) (17319144163 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2367258823105471 / 4000000000000) 1 (IntervalRat.scale (953 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (30083894869 / 1000000000000) (30083954570 / 1000000000000), orderedInterval (-13089331040 / 1000000000000) (-13089271339 / 1000000000000)))) (orderedInterval (488273294 / 1000000000000) (488287420 / 1000000000000))) = true
  rfl'

theorem compactCertificate605_chunkChecks1 :
    compactCertificate605.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate605.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate605_chunkChecks1_0
    compactCertificate605_chunkChecks1_1 compactCertificate605_chunkChecks1_2

theorem compactCertificate605_chunkChecks2_0 :
    compactCertificate605.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (953 / 2) 2 (IntervalRat.scale (953 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-8580037013 / 1000000000000) (-8580036999 / 1000000000000), orderedInterval (35539507246 / 1000000000000) (35539507260 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1403950973349653 / 4000000000000) 2 (IntervalRat.scale (953 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-3640791559 / 1000000000000) (-3640791555 / 1000000000000), orderedInterval (42437972531 / 1000000000000) (42437972535 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (454008898788149 / 800000000000) 2 (IntervalRat.scale (953 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (10915506861 / 1000000000000) (10915506890 / 1000000000000), orderedInterval (-31673903204 / 1000000000000) (-31673903175 / 1000000000000)))) (orderedInterval (2485120183 / 1000000000000) (2485120234 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (409669392519871 / 4000000000000) 2 (IntervalRat.scale (953 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (35778391470 / 1000000000000) (35778395007 / 1000000000000), orderedInterval (-70430535321 / 1000000000000) (-70430531783 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (1100429613075187 / 4000000000000) 2 (IntervalRat.scale (953 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-25870002574 / 1000000000000) (-25869998637 / 1000000000000), orderedInterval (40603419591 / 1000000000000) (40603423529 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2987880463544679 / 4000000000000) 2 (IntervalRat.scale (953 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (1642593068 / 1000000000000) (1642593069 / 1000000000000), orderedInterval (29146309945 / 1000000000000) (29146309946 / 1000000000000)))) (orderedInterval (624418232 / 1000000000000) (624418372 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (2200859226151327 / 4000000000000) 2 (IntervalRat.scale (953 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-31958451339 / 1000000000000) (-31958451334 / 1000000000000), orderedInterval (-11619804859 / 1000000000000) (-11619804854 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3771209796454171 / 4000000000000) 2 (IntervalRat.scale (953 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (23274162837 / 1000000000000) (23274162856 / 1000000000000), orderedInterval (11544267366 / 1000000000000) (11544267386 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2777856067383889 / 4000000000000) 2 (IntervalRat.scale (953 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-24755097082 / 1000000000000) (-24755097081 / 1000000000000), orderedInterval (-17414667310 / 1000000000000) (-17414667309 / 1000000000000)))) (orderedInterval (4083922307 / 1000000000000) (4083922392 / 1000000000000))) = true
  rfl'

theorem compactCertificate605_chunkChecks2_1 :
    compactCertificate605.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (4261945565114047 / 4000000000000) 2 (IntervalRat.scale (953 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-23358881225 / 1000000000000) (-23358880773 / 1000000000000), orderedInterval (-7190065666 / 1000000000000) (-7190065214 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2460635419289863 / 4000000000000) 2 (IntervalRat.scale (953 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (6135210335 / 1000000000000) (6135210336 / 1000000000000), orderedInterval (31574220093 / 1000000000000) (31574220094 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (4366440731556467 / 4000000000000) 2 (IntervalRat.scale (953 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-18594044568 / 1000000000000) (-18594043323 / 1000000000000), orderedInterval (15418086022 / 1000000000000) (15418087268 / 1000000000000)))) (orderedInterval (-7661155024 / 1000000000000) (-7661152853 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (4079695331214623 / 4000000000000) 2 (IntervalRat.scale (953 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (7585880747 / 1000000000000) (7585880749 / 1000000000000), orderedInterval (-23807880590 / 1000000000000) (-23807880588 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2911463091527759 / 4000000000000) 2 (IntervalRat.scale (953 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-5831914481 / 1000000000000) (-5831914479 / 1000000000000), orderedInterval (28997590587 / 1000000000000) (28997590588 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (3301288839225561 / 4000000000000) 2 (IntervalRat.scale (953 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (3639238711 / 1000000000000) (3639238712 / 1000000000000), orderedInterval (-27536095645 / 1000000000000) (-27536095644 / 1000000000000)))) (orderedInterval (1958247534 / 1000000000000) (1958247687 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2752270457483209 / 4000000000000) 2 (IntervalRat.scale (953 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-22732062502 / 1000000000000) (-22732062501 / 1000000000000), orderedInterval (-20194414271 / 1000000000000) (-20194414270 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2431714417175389 / 4000000000000) 2 (IntervalRat.scale (953 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-22180402001 / 1000000000000) (-22180397192 / 1000000000000), orderedInterval (23581449935 / 1000000000000) (23581454744 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (704805618719511 / 800000000000) 2 (IntervalRat.scale (953 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (22550674314 / 1000000000000) (22550687787 / 1000000000000), orderedInterval (-14643983266 / 1000000000000) (-14643969793 / 1000000000000)))) (orderedInterval (-3486734641 / 1000000000000) (-3486732913 / 1000000000000))) = true
  rfl'

theorem compactCertificate605_chunkChecks2_2 :
    compactCertificate605.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1949529433265717 / 4000000000000) 2 (IntervalRat.scale (953 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-33948296833 / 1000000000000) (-33948296830 / 1000000000000), orderedInterval (-12363339546 / 1000000000000) (-12363339543 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1652637691026637 / 4000000000000) 2 (IntervalRat.scale (953 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-26633471850 / 1000000000000) (-26633459918 / 1000000000000), orderedInterval (28868244797 / 1000000000000) (28868256729 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (1034143932616111 / 4000000000000) 2 (IntervalRat.scale (953 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (49140480509 / 1000000000000) (49140481162 / 1000000000000), orderedInterval (-6995158030 / 1000000000000) (-6995157377 / 1000000000000)))) (orderedInterval (-7284126548 / 1000000000000) (-7284125927 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (556166046368337 / 4000000000000) 2 (IntervalRat.scale (953 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (67643985319 / 1000000000000) (67643985382 / 1000000000000), orderedInterval (-1944030231 / 1000000000000) (-1944030168 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1510099005596011 / 4000000000000) 2 (IntervalRat.scale (953 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (39766575815 / 1000000000000) (39766575821 / 1000000000000), orderedInterval (10190260917 / 1000000000000) (10190260923 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (2061911089806347 / 4000000000000) 2 (IntervalRat.scale (953 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (30337986709 / 1000000000000) (30337986710 / 1000000000000), orderedInterval (17707975276 / 1000000000000) (17707975278 / 1000000000000)))) (orderedInterval (3397118318 / 1000000000000) (3397118370 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (871856067383889 / 4000000000000) 2 (IntervalRat.scale (953 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-49604560911 / 1000000000000) (-49604550784 / 1000000000000), orderedInterval (21564636646 / 1000000000000) (21564646773 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3544046509913969 / 4000000000000) 2 (IntervalRat.scale (953 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (20449215422 / 1000000000000) (20449215423 / 1000000000000), orderedInterval (17319144162 / 1000000000000) (17319144163 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2367258823105471 / 4000000000000) 2 (IntervalRat.scale (953 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (30083894869 / 1000000000000) (30083954570 / 1000000000000), orderedInterval (-13089331040 / 1000000000000) (-13089271339 / 1000000000000)))) (orderedInterval (14523895593 / 1000000000000) (14523913188 / 1000000000000))) = true
  rfl'

theorem compactCertificate605_chunkChecks2 :
    compactCertificate605.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate605.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate605_chunkChecks2_0
    compactCertificate605_chunkChecks2_1 compactCertificate605_chunkChecks2_2

theorem compactCertificate605_chunkChecks3_0 :
    compactCertificate605.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (953 / 2) 3 (IntervalRat.scale (953 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-8580037013 / 1000000000000) (-8580036999 / 1000000000000), orderedInterval (35539507246 / 1000000000000) (35539507260 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1403950973349653 / 4000000000000) 3 (IntervalRat.scale (953 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-3640791559 / 1000000000000) (-3640791555 / 1000000000000), orderedInterval (42437972531 / 1000000000000) (42437972535 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (454008898788149 / 800000000000) 3 (IntervalRat.scale (953 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (10915506861 / 1000000000000) (10915506890 / 1000000000000), orderedInterval (-31673903204 / 1000000000000) (-31673903175 / 1000000000000)))) (orderedInterval (-11109783028 / 1000000000000) (-11109782970 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (409669392519871 / 4000000000000) 3 (IntervalRat.scale (953 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (35778391470 / 1000000000000) (35778395007 / 1000000000000), orderedInterval (-70430535321 / 1000000000000) (-70430531783 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (1100429613075187 / 4000000000000) 3 (IntervalRat.scale (953 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-25870002574 / 1000000000000) (-25869998637 / 1000000000000), orderedInterval (40603419591 / 1000000000000) (40603423529 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2987880463544679 / 4000000000000) 3 (IntervalRat.scale (953 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (1642593068 / 1000000000000) (1642593069 / 1000000000000), orderedInterval (29146309945 / 1000000000000) (29146309946 / 1000000000000)))) (orderedInterval (7687768909 / 1000000000000) (7687769072 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (2200859226151327 / 4000000000000) 3 (IntervalRat.scale (953 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-31958451339 / 1000000000000) (-31958451334 / 1000000000000), orderedInterval (-11619804859 / 1000000000000) (-11619804854 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3771209796454171 / 4000000000000) 3 (IntervalRat.scale (953 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (23274162837 / 1000000000000) (23274162856 / 1000000000000), orderedInterval (11544267366 / 1000000000000) (11544267386 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2777856067383889 / 4000000000000) 3 (IntervalRat.scale (953 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-24755097082 / 1000000000000) (-24755097081 / 1000000000000), orderedInterval (-17414667310 / 1000000000000) (-17414667309 / 1000000000000)))) (orderedInterval (4052443900 / 1000000000000) (4052444055 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate605_chunkChecks3_1 :
    compactCertificate605.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (4261945565114047 / 4000000000000) 3 (IntervalRat.scale (953 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-23358881225 / 1000000000000) (-23358880773 / 1000000000000), orderedInterval (-7190065666 / 1000000000000) (-7190065214 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2460635419289863 / 4000000000000) 3 (IntervalRat.scale (953 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (6135210335 / 1000000000000) (6135210336 / 1000000000000), orderedInterval (31574220093 / 1000000000000) (31574220094 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (4366440731556467 / 4000000000000) 3 (IntervalRat.scale (953 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-18594044568 / 1000000000000) (-18594043323 / 1000000000000), orderedInterval (15418086022 / 1000000000000) (15418087268 / 1000000000000)))) (orderedInterval (-45653052302 / 1000000000000) (-45653047434 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (4079695331214623 / 4000000000000) 3 (IntervalRat.scale (953 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (7585880747 / 1000000000000) (7585880749 / 1000000000000), orderedInterval (-23807880590 / 1000000000000) (-23807880588 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2911463091527759 / 4000000000000) 3 (IntervalRat.scale (953 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-5831914481 / 1000000000000) (-5831914479 / 1000000000000), orderedInterval (28997590587 / 1000000000000) (28997590588 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (3301288839225561 / 4000000000000) 3 (IntervalRat.scale (953 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (3639238711 / 1000000000000) (3639238712 / 1000000000000), orderedInterval (-27536095645 / 1000000000000) (-27536095644 / 1000000000000)))) (orderedInterval (-14716502634 / 1000000000000) (-14716502375 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2752270457483209 / 4000000000000) 3 (IntervalRat.scale (953 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-22732062502 / 1000000000000) (-22732062501 / 1000000000000), orderedInterval (-20194414271 / 1000000000000) (-20194414270 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2431714417175389 / 4000000000000) 3 (IntervalRat.scale (953 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-22180402001 / 1000000000000) (-22180397192 / 1000000000000), orderedInterval (23581449935 / 1000000000000) (23581454744 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (704805618719511 / 800000000000) 3 (IntervalRat.scale (953 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (22550674314 / 1000000000000) (22550687787 / 1000000000000), orderedInterval (-14643983266 / 1000000000000) (-14643969793 / 1000000000000)))) (orderedInterval (5881726016 / 1000000000000) (5881728923 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate605_chunkChecks3_2 :
    compactCertificate605.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1949529433265717 / 4000000000000) 3 (IntervalRat.scale (953 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-33948296833 / 1000000000000) (-33948296830 / 1000000000000), orderedInterval (-12363339546 / 1000000000000) (-12363339543 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1652637691026637 / 4000000000000) 3 (IntervalRat.scale (953 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-26633471850 / 1000000000000) (-26633459918 / 1000000000000), orderedInterval (28868244797 / 1000000000000) (28868256729 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (1034143932616111 / 4000000000000) 3 (IntervalRat.scale (953 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (49140480509 / 1000000000000) (49140481162 / 1000000000000), orderedInterval (-6995158030 / 1000000000000) (-6995157377 / 1000000000000)))) (orderedInterval (-998572331 / 1000000000000) (-998571783 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (556166046368337 / 4000000000000) 3 (IntervalRat.scale (953 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (67643985319 / 1000000000000) (67643985382 / 1000000000000), orderedInterval (-1944030231 / 1000000000000) (-1944030168 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1510099005596011 / 4000000000000) 3 (IntervalRat.scale (953 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (39766575815 / 1000000000000) (39766575821 / 1000000000000), orderedInterval (10190260917 / 1000000000000) (10190260923 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (2061911089806347 / 4000000000000) 3 (IntervalRat.scale (953 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (30337986709 / 1000000000000) (30337986710 / 1000000000000), orderedInterval (17707975276 / 1000000000000) (17707975278 / 1000000000000)))) (orderedInterval (1825089833 / 1000000000000) (1825089886 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (871856067383889 / 4000000000000) 3 (IntervalRat.scale (953 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-49604560911 / 1000000000000) (-49604550784 / 1000000000000), orderedInterval (21564636646 / 1000000000000) (21564646773 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3544046509913969 / 4000000000000) 3 (IntervalRat.scale (953 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (20449215422 / 1000000000000) (20449215423 / 1000000000000), orderedInterval (17319144162 / 1000000000000) (17319144163 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2367258823105471 / 4000000000000) 3 (IntervalRat.scale (953 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (30083894869 / 1000000000000) (30083954570 / 1000000000000), orderedInterval (-13089331040 / 1000000000000) (-13089271339 / 1000000000000)))) (orderedInterval (4315229040 / 1000000000000) (4315250965 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate605_chunkChecks3 :
    compactCertificate605.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate605.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate605_chunkChecks3_0
    compactCertificate605_chunkChecks3_1 compactCertificate605_chunkChecks3_2

theorem compactCertificate605_chunkChecks4_0 :
    compactCertificate605.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (953 / 2) 4 (IntervalRat.scale (953 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-8580037013 / 1000000000000) (-8580036999 / 1000000000000), orderedInterval (35539507246 / 1000000000000) (35539507260 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1403950973349653 / 4000000000000) 4 (IntervalRat.scale (953 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-3640791559 / 1000000000000) (-3640791555 / 1000000000000), orderedInterval (42437972531 / 1000000000000) (42437972535 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (454008898788149 / 800000000000) 4 (IntervalRat.scale (953 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (10915506861 / 1000000000000) (10915506890 / 1000000000000), orderedInterval (-31673903204 / 1000000000000) (-31673903175 / 1000000000000)))) (orderedInterval (-2075363431 / 1000000000000) (-2075363363 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (409669392519871 / 4000000000000) 4 (IntervalRat.scale (953 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (35778391470 / 1000000000000) (35778395007 / 1000000000000), orderedInterval (-70430535321 / 1000000000000) (-70430531783 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (1100429613075187 / 4000000000000) 4 (IntervalRat.scale (953 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-25870002574 / 1000000000000) (-25869998637 / 1000000000000), orderedInterval (40603419591 / 1000000000000) (40603423529 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2987880463544679 / 4000000000000) 4 (IntervalRat.scale (953 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (1642593068 / 1000000000000) (1642593069 / 1000000000000), orderedInterval (29146309945 / 1000000000000) (29146309946 / 1000000000000)))) (orderedInterval (-843220551 / 1000000000000) (-843220327 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (2200859226151327 / 4000000000000) 4 (IntervalRat.scale (953 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-31958451339 / 1000000000000) (-31958451334 / 1000000000000), orderedInterval (-11619804859 / 1000000000000) (-11619804854 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3771209796454171 / 4000000000000) 4 (IntervalRat.scale (953 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (23274162837 / 1000000000000) (23274162856 / 1000000000000), orderedInterval (11544267366 / 1000000000000) (11544267386 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2777856067383889 / 4000000000000) 4 (IntervalRat.scale (953 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-24755097082 / 1000000000000) (-24755097081 / 1000000000000), orderedInterval (-17414667310 / 1000000000000) (-17414667309 / 1000000000000)))) (orderedInterval (-13718413648 / 1000000000000) (-13718413360 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate605_chunkChecks4_1 :
    compactCertificate605.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (4261945565114047 / 4000000000000) 4 (IntervalRat.scale (953 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-23358881225 / 1000000000000) (-23358880773 / 1000000000000), orderedInterval (-7190065666 / 1000000000000) (-7190065214 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2460635419289863 / 4000000000000) 4 (IntervalRat.scale (953 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (6135210335 / 1000000000000) (6135210336 / 1000000000000), orderedInterval (31574220093 / 1000000000000) (31574220094 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (4366440731556467 / 4000000000000) 4 (IntervalRat.scale (953 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-18594044568 / 1000000000000) (-18594043323 / 1000000000000), orderedInterval (15418086022 / 1000000000000) (15418087268 / 1000000000000)))) (orderedInterval (32414683670 / 1000000000000) (32414694647 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (4079695331214623 / 4000000000000) 4 (IntervalRat.scale (953 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (7585880747 / 1000000000000) (7585880749 / 1000000000000), orderedInterval (-23807880590 / 1000000000000) (-23807880588 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2911463091527759 / 4000000000000) 4 (IntervalRat.scale (953 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-5831914481 / 1000000000000) (-5831914479 / 1000000000000), orderedInterval (28997590587 / 1000000000000) (28997590588 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (3301288839225561 / 4000000000000) 4 (IntervalRat.scale (953 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (3639238711 / 1000000000000) (3639238712 / 1000000000000), orderedInterval (-27536095645 / 1000000000000) (-27536095644 / 1000000000000)))) (orderedInterval (-5981084286 / 1000000000000) (-5981083835 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2752270457483209 / 4000000000000) 4 (IntervalRat.scale (953 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-22732062502 / 1000000000000) (-22732062501 / 1000000000000), orderedInterval (-20194414271 / 1000000000000) (-20194414270 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2431714417175389 / 4000000000000) 4 (IntervalRat.scale (953 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-22180402001 / 1000000000000) (-22180397192 / 1000000000000), orderedInterval (23581449935 / 1000000000000) (23581454744 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (704805618719511 / 800000000000) 4 (IntervalRat.scale (953 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (22550674314 / 1000000000000) (22550687787 / 1000000000000), orderedInterval (-14643983266 / 1000000000000) (-14643969793 / 1000000000000)))) (orderedInterval (8944314853 / 1000000000000) (8944319865 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate605_chunkChecks4_2 :
    compactCertificate605.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1949529433265717 / 4000000000000) 4 (IntervalRat.scale (953 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-33948296833 / 1000000000000) (-33948296830 / 1000000000000), orderedInterval (-12363339546 / 1000000000000) (-12363339543 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1652637691026637 / 4000000000000) 4 (IntervalRat.scale (953 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-26633471850 / 1000000000000) (-26633459918 / 1000000000000), orderedInterval (28868244797 / 1000000000000) (28868256729 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (1034143932616111 / 4000000000000) 4 (IntervalRat.scale (953 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (49140480509 / 1000000000000) (49140481162 / 1000000000000), orderedInterval (-6995158030 / 1000000000000) (-6995157377 / 1000000000000)))) (orderedInterval (6936037103 / 1000000000000) (6936037590 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (556166046368337 / 4000000000000) 4 (IntervalRat.scale (953 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (67643985319 / 1000000000000) (67643985382 / 1000000000000), orderedInterval (-1944030231 / 1000000000000) (-1944030168 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1510099005596011 / 4000000000000) 4 (IntervalRat.scale (953 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (39766575815 / 1000000000000) (39766575821 / 1000000000000), orderedInterval (10190260917 / 1000000000000) (10190260923 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (2061911089806347 / 4000000000000) 4 (IntervalRat.scale (953 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (30337986709 / 1000000000000) (30337986710 / 1000000000000), orderedInterval (17707975276 / 1000000000000) (17707975278 / 1000000000000)))) (orderedInterval (-3556560538 / 1000000000000) (-3556560483 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (871856067383889 / 4000000000000) 4 (IntervalRat.scale (953 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-49604560911 / 1000000000000) (-49604550784 / 1000000000000), orderedInterval (21564636646 / 1000000000000) (21564646773 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3544046509913969 / 4000000000000) 4 (IntervalRat.scale (953 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (20449215422 / 1000000000000) (20449215423 / 1000000000000), orderedInterval (17319144162 / 1000000000000) (17319144163 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2367258823105471 / 4000000000000) 4 (IntervalRat.scale (953 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (30083894869 / 1000000000000) (30083954570 / 1000000000000), orderedInterval (-13089331040 / 1000000000000) (-13089271339 / 1000000000000)))) (orderedInterval (-33360846845 / 1000000000000) (-33360819419 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate605_chunkChecks4 :
    compactCertificate605.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate605.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate605_chunkChecks4_0
    compactCertificate605_chunkChecks4_1 compactCertificate605_chunkChecks4_2

theorem compactCertificate605_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate605.chunkCheck r b = true :=
  compactCertificate605.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate605_chunkChecks0
    · exact compactCertificate605_chunkChecks1
    · exact compactCertificate605_chunkChecks2
    · exact compactCertificate605_chunkChecks3
    · exact compactCertificate605_chunkChecks4)

theorem compactCertificate605_coefficient0 :
    compactCertificate605.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate605_coefficient1 :
    compactCertificate605.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate605_coefficient2 :
    compactCertificate605.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate605_coefficient3 :
    compactCertificate605.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate605_coefficient4 :
    compactCertificate605.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate605_coefficients : ∀ r : Fin 5,
    compactCertificate605.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate605_coefficient0
  · exact compactCertificate605_coefficient1
  · exact compactCertificate605_coefficient2
  · exact compactCertificate605_coefficient3
  · exact compactCertificate605_coefficient4

theorem compactCertificate605_lower : (1 : ℚ) ≤ compactCertificate605.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate605, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate605_proves {t : ℝ} (ht : t ∈ compactCertificate605.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate605.proves compactCertificate605_states compactCertificate605_chunks
    compactCertificate605_coefficients compactCertificate605_lower ht

end Erdos232
