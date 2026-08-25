/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate554 : CompactCertificate where
  left := 425
  right := 426
  center := 851 / 2
  grid := fun i =>
    match i.val with
    | 0 => 136
    | 1 => 100
    | 2 => 161
    | 3 => 29
    | 4 => 78
    | 5 => 212
    | 6 => 156
    | 7 => 268
    | 8 => 197
    | 9 => 303
    | 10 => 175
    | 11 => 310
    | 12 => 290
    | 13 => 207
    | 14 => 235
    | 15 => 196
    | 16 => 173
    | 17 => 251
    | 18 => 139
    | 19 => 117
    | 20 => 74
    | 21 => 40
    | 22 => 107
    | 23 => 147
    | 24 => 62
    | 25 => 252
    | _ => 168
  point := fun i =>
    match i.val with
    | 0 => 851 / 2
    | 1 => 1253685496663751 / 4000000000000
    | 2 => 405416131026983 / 800000000000
    | 3 => 365822301190357 / 4000000000000
    | 4 => 982650158160529 / 4000000000000
    | 5 => 2668086332084493 / 4000000000000
    | 6 => 1965300316321909 / 4000000000000
    | 7 => 3367575589488457 / 4000000000000
    | 8 => 2480540937401563 / 4000000000000
    | 9 => 3805787697704149 / 4000000000000
    | 10 => 2197272551747821 / 4000000000000
    | 11 => 3899098701526289 / 4000000000000
    | 12 => 3643043784746741 / 4000000000000
    | 13 => 2599847944270853 / 4000000000000
    | 14 => 2947950474481587 / 4000000000000
    | 15 => 2457693766336003 / 4000000000000
    | 16 => 2171446976932063 / 4000000000000
    | 17 => 629369970126237 / 800000000000
    | 18 => 1740870459296039 / 4000000000000
    | 19 => 1475755167957679 / 4000000000000
    | 20 => 923459062598437 / 4000000000000
    | 21 => 496639355151579 / 4000000000000
    | 22 => 1348472459351737 / 4000000000000
    | 23 => 1841223858788249 / 4000000000000
    | 24 => 778540937401563 / 4000000000000
    | 25 => 3164725687236923 / 4000000000000
    | _ => 2113890092825557 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-31939577672 / 1000000000000) (-31939489664 / 1000000000000), orderedInterval (21855699403 / 1000000000000) (21855787411 / 1000000000000))
    | 1 => (orderedInterval (2122320029 / 1000000000000) (2122320030 / 1000000000000), orderedInterval (45015419615 / 1000000000000) (45015419617 / 1000000000000))
    | 2 => (orderedInterval (-34818139827 / 1000000000000) (-34818135081 / 1000000000000), orderedInterval (6662058490 / 1000000000000) (6662063237 / 1000000000000))
    | 3 => (orderedInterval (-75578049559 / 1000000000000) (-75578049558 / 1000000000000), orderedInterval (-34926094499 / 1000000000000) (-34926094498 / 1000000000000))
    | 4 => (orderedInterval (50192885926 / 1000000000000) (50192885934 / 1000000000000), orderedInterval (8389561705 / 1000000000000) (8389561712 / 1000000000000))
    | 5 => (orderedInterval (30160135047 / 1000000000000) (30160149696 / 1000000000000), orderedInterval (-6714932230 / 1000000000000) (-6714917581 / 1000000000000))
    | 6 => (orderedInterval (32397315677 / 1000000000000) (32397370568 / 1000000000000), orderedInterval (-15721583588 / 1000000000000) (-15721528697 / 1000000000000))
    | 7 => (orderedInterval (18385419913 / 1000000000000) (18385419914 / 1000000000000), orderedInterval (20437849249 / 1000000000000) (20437849250 / 1000000000000))
    | 8 => (orderedInterval (-28768187403 / 1000000000000) (-28768087380 / 1000000000000), orderedInterval (14129034994 / 1000000000000) (14129135017 / 1000000000000))
    | 9 => (orderedInterval (-8372684622 / 1000000000000) (-8372684621 / 1000000000000), orderedInterval (-24470182742 / 1000000000000) (-24470182741 / 1000000000000))
    | 10 => (orderedInterval (-10857140026 / 1000000000000) (-10857140025 / 1000000000000), orderedInterval (-32255426667 / 1000000000000) (-32255426666 / 1000000000000))
    | 11 => (orderedInterval (25439428201 / 1000000000000) (25439448309 / 1000000000000), orderedInterval (-2448048090 / 1000000000000) (-2448027982 / 1000000000000))
    | 12 => (orderedInterval (12310381748 / 1000000000000) (12310381749 / 1000000000000), orderedInterval (23390938672 / 1000000000000) (23390938673 / 1000000000000))
    | 13 => (orderedInterval (-13259949272 / 1000000000000) (-13259949271 / 1000000000000), orderedInterval (-28338454584 / 1000000000000) (-28338454583 / 1000000000000))
    | 14 => (orderedInterval (14127428609 / 1000000000000) (14127428708 / 1000000000000), orderedInterval (-25782230105 / 1000000000000) (-25782230006 / 1000000000000))
    | 15 => (orderedInterval (-16646655444 / 1000000000000) (-16646655045 / 1000000000000), orderedInterval (27563763971 / 1000000000000) (27563764370 / 1000000000000))
    | 16 => (orderedInterval (-5164313505 / 1000000000000) (-5164313504 / 1000000000000), orderedInterval (-33848471262 / 1000000000000) (-33848471261 / 1000000000000))
    | 17 => (orderedInterval (24562071822 / 1000000000000) (24562104662 / 1000000000000), orderedInterval (-14365506063 / 1000000000000) (-14365473224 / 1000000000000))
    | 18 => (orderedInterval (24008773869 / 1000000000000) (24008779266 / 1000000000000), orderedInterval (-29799061567 / 1000000000000) (-29799056170 / 1000000000000))
    | 19 => (orderedInterval (-34592768221 / 1000000000000) (-34592665182 / 1000000000000), orderedInterval (23044356232 / 1000000000000) (23044459271 / 1000000000000))
    | 20 => (orderedInterval (-38687827519 / 1000000000000) (-38687767543 / 1000000000000), orderedInterval (35591471832 / 1000000000000) (35591531808 / 1000000000000))
    | 21 => (orderedInterval (-47187513888 / 1000000000000) (-47187477066 / 1000000000000), orderedInterval (54048771149 / 1000000000000) (54048807971 / 1000000000000))
    | 22 => (orderedInterval (-42738706655 / 1000000000000) (-42738704928 / 1000000000000), orderedInterval (7925871462 / 1000000000000) (7925873190 / 1000000000000))
    | 23 => (orderedInterval (24606542099 / 1000000000000) (24606549584 / 1000000000000), orderedInterval (-27911389376 / 1000000000000) (-27911381891 / 1000000000000))
    | 24 => (orderedInterval (34211397637 / 1000000000000) (34211397638 / 1000000000000), orderedInterval (45742437833 / 1000000000000) (45742437834 / 1000000000000))
    | 25 => (orderedInterval (7983911124 / 1000000000000) (7983911125 / 1000000000000), orderedInterval (27214465626 / 1000000000000) (27214465627 / 1000000000000))
    | _ => (orderedInterval (34532183700 / 1000000000000) (34532183872 / 1000000000000), orderedInterval (3455730527 / 1000000000000) (3455730699 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-14683122728 / 1000000000000) (-14683087536 / 1000000000000)
      | 1 => orderedInterval (508523915 / 1000000000000) (508525008 / 1000000000000)
      | 2 => orderedInterval (-1262350252 / 1000000000000) (-1262347811 / 1000000000000)
      | 3 => orderedInterval (4299664756 / 1000000000000) (4299667784 / 1000000000000)
      | 4 => orderedInterval (-1547632139 / 1000000000000) (-1547632087 / 1000000000000)
      | 5 => orderedInterval (732192455 / 1000000000000) (732193342 / 1000000000000)
      | 6 => orderedInterval (-3140371782 / 1000000000000) (-3140363027 / 1000000000000)
      | 7 => orderedInterval (-44888795 / 1000000000000) (-44887451 / 1000000000000)
      | _ => orderedInterval (-6922820815 / 1000000000000) (-6922820665 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (9437409676 / 1000000000000) (9437444925 / 1000000000000)
      | 1 => orderedInterval (1006616995 / 1000000000000) (1006618686 / 1000000000000)
      | 2 => orderedInterval (-749610325 / 1000000000000) (-749606760 / 1000000000000)
      | 3 => orderedInterval (5840009747 / 1000000000000) (5840016646 / 1000000000000)
      | 4 => orderedInterval (-4771289444 / 1000000000000) (-4771289361 / 1000000000000)
      | 5 => orderedInterval (2250876959 / 1000000000000) (2250878579 / 1000000000000)
      | 6 => orderedInterval (4371198759 / 1000000000000) (4371205857 / 1000000000000)
      | 7 => orderedInterval (1880392498 / 1000000000000) (1880393394 / 1000000000000)
      | _ => orderedInterval (-4798337746 / 1000000000000) (-4798337540 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (15524976991 / 1000000000000) (15525012391 / 1000000000000)
      | 1 => orderedInterval (4617780406 / 1000000000000) (4617783050 / 1000000000000)
      | 2 => orderedInterval (3698611092 / 1000000000000) (3698616310 / 1000000000000)
      | 3 => orderedInterval (-25091017092 / 1000000000000) (-25091001325 / 1000000000000)
      | 4 => orderedInterval (4169654906 / 1000000000000) (4169655044 / 1000000000000)
      | 5 => orderedInterval (-2235349282 / 1000000000000) (-2235346307 / 1000000000000)
      | 6 => orderedInterval (2904658481 / 1000000000000) (2904664454 / 1000000000000)
      | 7 => orderedInterval (1519707149 / 1000000000000) (1519707950 / 1000000000000)
      | _ => orderedInterval (12209688245 / 1000000000000) (12209688539 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-9527394694 / 1000000000000) (-9527359213 / 1000000000000)
      | 1 => orderedInterval (-1912506271 / 1000000000000) (-1912502133 / 1000000000000)
      | 2 => orderedInterval (3817116827 / 1000000000000) (3817124457 / 1000000000000)
      | 3 => orderedInterval (-39227546276 / 1000000000000) (-39227510229 / 1000000000000)
      | 4 => orderedInterval (13004585298 / 1000000000000) (13004585532 / 1000000000000)
      | 5 => orderedInterval (-2650961210 / 1000000000000) (-2650955740 / 1000000000000)
      | 6 => orderedInterval (-4440231662 / 1000000000000) (-4440226520 / 1000000000000)
      | 7 => orderedInterval (-2597481520 / 1000000000000) (-2597480709 / 1000000000000)
      | _ => orderedInterval (15428863959 / 1000000000000) (15428864398 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-16720065087 / 1000000000000) (-16720029425 / 1000000000000)
      | 1 => orderedInterval (-12733562282 / 1000000000000) (-12733555789 / 1000000000000)
      | 2 => orderedInterval (-11845938437 / 1000000000000) (-11845927246 / 1000000000000)
      | 3 => orderedInterval (134750092935 / 1000000000000) (134750175478 / 1000000000000)
      | 4 => orderedInterval (-12196221696 / 1000000000000) (-12196221290 / 1000000000000)
      | 5 => orderedInterval (7308840338 / 1000000000000) (7308850423 / 1000000000000)
      | 6 => orderedInterval (-3183297489 / 1000000000000) (-3183292965 / 1000000000000)
      | 7 => orderedInterval (-2182193935 / 1000000000000) (-2182193076 / 1000000000000)
      | _ => orderedInterval (-23249603039 / 1000000000000) (-23249602356 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-22060805385 / 1000000000000) (-22060752443 / 1000000000000)
    | 1 => orderedInterval (14467267119 / 1000000000000) (14467324426 / 1000000000000)
    | 2 => orderedInterval (17318710896 / 1000000000000) (17318780106 / 1000000000000)
    | 3 => orderedInterval (-28105555549 / 1000000000000) (-28105460157 / 1000000000000)
    | _ => orderedInterval (59948051308 / 1000000000000) (59948203754 / 1000000000000)

theorem compactCertificate554_stateChecks0 :
    compactCertificate554.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 136 12 (851 / 2)) (orderedInterval (-31939577672 / 1000000000000) (-31939489664 / 1000000000000), orderedInterval (21855699403 / 1000000000000) (21855787411 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 100 12 (1253685496663751 / 4000000000000)) (orderedInterval (2122320029 / 1000000000000) (2122320030 / 1000000000000), orderedInterval (45015419615 / 1000000000000) (45015419617 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 161 12 (405416131026983 / 800000000000)) (orderedInterval (-34818139827 / 1000000000000) (-34818135081 / 1000000000000), orderedInterval (6662058490 / 1000000000000) (6662063237 / 1000000000000))) = true
  rfl'

theorem compactCertificate554_stateChecks1 :
    compactCertificate554.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 29 12 (365822301190357 / 4000000000000)) (orderedInterval (-75578049559 / 1000000000000) (-75578049558 / 1000000000000), orderedInterval (-34926094499 / 1000000000000) (-34926094498 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 78 12 (982650158160529 / 4000000000000)) (orderedInterval (50192885926 / 1000000000000) (50192885934 / 1000000000000), orderedInterval (8389561705 / 1000000000000) (8389561712 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 212 12 (2668086332084493 / 4000000000000)) (orderedInterval (30160135047 / 1000000000000) (30160149696 / 1000000000000), orderedInterval (-6714932230 / 1000000000000) (-6714917581 / 1000000000000))) = true
  rfl'

theorem compactCertificate554_stateChecks2 :
    compactCertificate554.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 156 12 (1965300316321909 / 4000000000000)) (orderedInterval (32397315677 / 1000000000000) (32397370568 / 1000000000000), orderedInterval (-15721583588 / 1000000000000) (-15721528697 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 268 12 (3367575589488457 / 4000000000000)) (orderedInterval (18385419913 / 1000000000000) (18385419914 / 1000000000000), orderedInterval (20437849249 / 1000000000000) (20437849250 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 197 12 (2480540937401563 / 4000000000000)) (orderedInterval (-28768187403 / 1000000000000) (-28768087380 / 1000000000000), orderedInterval (14129034994 / 1000000000000) (14129135017 / 1000000000000))) = true
  rfl'

theorem compactCertificate554_stateChecks3 :
    compactCertificate554.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 303 12 (3805787697704149 / 4000000000000)) (orderedInterval (-8372684622 / 1000000000000) (-8372684621 / 1000000000000), orderedInterval (-24470182742 / 1000000000000) (-24470182741 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 175 12 (2197272551747821 / 4000000000000)) (orderedInterval (-10857140026 / 1000000000000) (-10857140025 / 1000000000000), orderedInterval (-32255426667 / 1000000000000) (-32255426666 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 310 12 (3899098701526289 / 4000000000000)) (orderedInterval (25439428201 / 1000000000000) (25439448309 / 1000000000000), orderedInterval (-2448048090 / 1000000000000) (-2448027982 / 1000000000000))) = true
  rfl'

theorem compactCertificate554_stateChecks4 :
    compactCertificate554.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 290 12 (3643043784746741 / 4000000000000)) (orderedInterval (12310381748 / 1000000000000) (12310381749 / 1000000000000), orderedInterval (23390938672 / 1000000000000) (23390938673 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 207 12 (2599847944270853 / 4000000000000)) (orderedInterval (-13259949272 / 1000000000000) (-13259949271 / 1000000000000), orderedInterval (-28338454584 / 1000000000000) (-28338454583 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 235 12 (2947950474481587 / 4000000000000)) (orderedInterval (14127428609 / 1000000000000) (14127428708 / 1000000000000), orderedInterval (-25782230105 / 1000000000000) (-25782230006 / 1000000000000))) = true
  rfl'

theorem compactCertificate554_stateChecks5 :
    compactCertificate554.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 196 12 (2457693766336003 / 4000000000000)) (orderedInterval (-16646655444 / 1000000000000) (-16646655045 / 1000000000000), orderedInterval (27563763971 / 1000000000000) (27563764370 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 173 12 (2171446976932063 / 4000000000000)) (orderedInterval (-5164313505 / 1000000000000) (-5164313504 / 1000000000000), orderedInterval (-33848471262 / 1000000000000) (-33848471261 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 251 12 (629369970126237 / 800000000000)) (orderedInterval (24562071822 / 1000000000000) (24562104662 / 1000000000000), orderedInterval (-14365506063 / 1000000000000) (-14365473224 / 1000000000000))) = true
  rfl'

theorem compactCertificate554_stateChecks6 :
    compactCertificate554.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 139 12 (1740870459296039 / 4000000000000)) (orderedInterval (24008773869 / 1000000000000) (24008779266 / 1000000000000), orderedInterval (-29799061567 / 1000000000000) (-29799056170 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 117 12 (1475755167957679 / 4000000000000)) (orderedInterval (-34592768221 / 1000000000000) (-34592665182 / 1000000000000), orderedInterval (23044356232 / 1000000000000) (23044459271 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 74 12 (923459062598437 / 4000000000000)) (orderedInterval (-38687827519 / 1000000000000) (-38687767543 / 1000000000000), orderedInterval (35591471832 / 1000000000000) (35591531808 / 1000000000000))) = true
  rfl'

theorem compactCertificate554_stateChecks7 :
    compactCertificate554.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 40 12 (496639355151579 / 4000000000000)) (orderedInterval (-47187513888 / 1000000000000) (-47187477066 / 1000000000000), orderedInterval (54048771149 / 1000000000000) (54048807971 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 107 12 (1348472459351737 / 4000000000000)) (orderedInterval (-42738706655 / 1000000000000) (-42738704928 / 1000000000000), orderedInterval (7925871462 / 1000000000000) (7925873190 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 147 12 (1841223858788249 / 4000000000000)) (orderedInterval (24606542099 / 1000000000000) (24606549584 / 1000000000000), orderedInterval (-27911389376 / 1000000000000) (-27911381891 / 1000000000000))) = true
  rfl'

theorem compactCertificate554_stateChecks8 :
    compactCertificate554.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (778540937401563 / 4000000000000)) (orderedInterval (34211397637 / 1000000000000) (34211397638 / 1000000000000), orderedInterval (45742437833 / 1000000000000) (45742437834 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 252 12 (3164725687236923 / 4000000000000)) (orderedInterval (7983911124 / 1000000000000) (7983911125 / 1000000000000), orderedInterval (27214465626 / 1000000000000) (27214465627 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 168 12 (2113890092825557 / 4000000000000)) (orderedInterval (34532183700 / 1000000000000) (34532183872 / 1000000000000), orderedInterval (3455730527 / 1000000000000) (3455730699 / 1000000000000))) = true
  rfl'

theorem compactCertificate554_states : ∀ j,
    BesselStateValid (compactCertificate554.point j) (compactCertificate554.state j) :=
  compactCertificate554.statesValid_of_checks3 compactCertificate554_stateChecks0
    compactCertificate554_stateChecks1 compactCertificate554_stateChecks2
    compactCertificate554_stateChecks3 compactCertificate554_stateChecks4
    compactCertificate554_stateChecks5 compactCertificate554_stateChecks6
    compactCertificate554_stateChecks7 compactCertificate554_stateChecks8

theorem compactCertificate554_chunkChecks0_0 :
    compactCertificate554.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (851 / 2) 0 (IntervalRat.scale (851 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-31939577672 / 1000000000000) (-31939489664 / 1000000000000), orderedInterval (21855699403 / 1000000000000) (21855787411 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1253685496663751 / 4000000000000) 0 (IntervalRat.scale (851 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (2122320029 / 1000000000000) (2122320030 / 1000000000000), orderedInterval (45015419615 / 1000000000000) (45015419617 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (405416131026983 / 800000000000) 0 (IntervalRat.scale (851 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-34818139827 / 1000000000000) (-34818135081 / 1000000000000), orderedInterval (6662058490 / 1000000000000) (6662063237 / 1000000000000)))) (orderedInterval (-14683122728 / 1000000000000) (-14683087536 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (365822301190357 / 4000000000000) 0 (IntervalRat.scale (851 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-75578049559 / 1000000000000) (-75578049558 / 1000000000000), orderedInterval (-34926094499 / 1000000000000) (-34926094498 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (982650158160529 / 4000000000000) 0 (IntervalRat.scale (851 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (50192885926 / 1000000000000) (50192885934 / 1000000000000), orderedInterval (8389561705 / 1000000000000) (8389561712 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2668086332084493 / 4000000000000) 0 (IntervalRat.scale (851 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30160135047 / 1000000000000) (30160149696 / 1000000000000), orderedInterval (-6714932230 / 1000000000000) (-6714917581 / 1000000000000)))) (orderedInterval (508523915 / 1000000000000) (508525008 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1965300316321909 / 4000000000000) 0 (IntervalRat.scale (851 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (32397315677 / 1000000000000) (32397370568 / 1000000000000), orderedInterval (-15721583588 / 1000000000000) (-15721528697 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3367575589488457 / 4000000000000) 0 (IntervalRat.scale (851 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (18385419913 / 1000000000000) (18385419914 / 1000000000000), orderedInterval (20437849249 / 1000000000000) (20437849250 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2480540937401563 / 4000000000000) 0 (IntervalRat.scale (851 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-28768187403 / 1000000000000) (-28768087380 / 1000000000000), orderedInterval (14129034994 / 1000000000000) (14129135017 / 1000000000000)))) (orderedInterval (-1262350252 / 1000000000000) (-1262347811 / 1000000000000))) = true
  rfl'

theorem compactCertificate554_chunkChecks0_1 :
    compactCertificate554.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3805787697704149 / 4000000000000) 0 (IntervalRat.scale (851 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-8372684622 / 1000000000000) (-8372684621 / 1000000000000), orderedInterval (-24470182742 / 1000000000000) (-24470182741 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2197272551747821 / 4000000000000) 0 (IntervalRat.scale (851 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-10857140026 / 1000000000000) (-10857140025 / 1000000000000), orderedInterval (-32255426667 / 1000000000000) (-32255426666 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3899098701526289 / 4000000000000) 0 (IntervalRat.scale (851 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (25439428201 / 1000000000000) (25439448309 / 1000000000000), orderedInterval (-2448048090 / 1000000000000) (-2448027982 / 1000000000000)))) (orderedInterval (4299664756 / 1000000000000) (4299667784 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3643043784746741 / 4000000000000) 0 (IntervalRat.scale (851 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (12310381748 / 1000000000000) (12310381749 / 1000000000000), orderedInterval (23390938672 / 1000000000000) (23390938673 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2599847944270853 / 4000000000000) 0 (IntervalRat.scale (851 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-13259949272 / 1000000000000) (-13259949271 / 1000000000000), orderedInterval (-28338454584 / 1000000000000) (-28338454583 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2947950474481587 / 4000000000000) 0 (IntervalRat.scale (851 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (14127428609 / 1000000000000) (14127428708 / 1000000000000), orderedInterval (-25782230105 / 1000000000000) (-25782230006 / 1000000000000)))) (orderedInterval (-1547632139 / 1000000000000) (-1547632087 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2457693766336003 / 4000000000000) 0 (IntervalRat.scale (851 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-16646655444 / 1000000000000) (-16646655045 / 1000000000000), orderedInterval (27563763971 / 1000000000000) (27563764370 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2171446976932063 / 4000000000000) 0 (IntervalRat.scale (851 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-5164313505 / 1000000000000) (-5164313504 / 1000000000000), orderedInterval (-33848471262 / 1000000000000) (-33848471261 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (629369970126237 / 800000000000) 0 (IntervalRat.scale (851 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (24562071822 / 1000000000000) (24562104662 / 1000000000000), orderedInterval (-14365506063 / 1000000000000) (-14365473224 / 1000000000000)))) (orderedInterval (732192455 / 1000000000000) (732193342 / 1000000000000))) = true
  rfl'

theorem compactCertificate554_chunkChecks0_2 :
    compactCertificate554.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1740870459296039 / 4000000000000) 0 (IntervalRat.scale (851 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (24008773869 / 1000000000000) (24008779266 / 1000000000000), orderedInterval (-29799061567 / 1000000000000) (-29799056170 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1475755167957679 / 4000000000000) 0 (IntervalRat.scale (851 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-34592768221 / 1000000000000) (-34592665182 / 1000000000000), orderedInterval (23044356232 / 1000000000000) (23044459271 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (923459062598437 / 4000000000000) 0 (IntervalRat.scale (851 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-38687827519 / 1000000000000) (-38687767543 / 1000000000000), orderedInterval (35591471832 / 1000000000000) (35591531808 / 1000000000000)))) (orderedInterval (-3140371782 / 1000000000000) (-3140363027 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (496639355151579 / 4000000000000) 0 (IntervalRat.scale (851 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-47187513888 / 1000000000000) (-47187477066 / 1000000000000), orderedInterval (54048771149 / 1000000000000) (54048807971 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1348472459351737 / 4000000000000) 0 (IntervalRat.scale (851 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-42738706655 / 1000000000000) (-42738704928 / 1000000000000), orderedInterval (7925871462 / 1000000000000) (7925873190 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1841223858788249 / 4000000000000) 0 (IntervalRat.scale (851 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (24606542099 / 1000000000000) (24606549584 / 1000000000000), orderedInterval (-27911389376 / 1000000000000) (-27911381891 / 1000000000000)))) (orderedInterval (-44888795 / 1000000000000) (-44887451 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (778540937401563 / 4000000000000) 0 (IntervalRat.scale (851 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (34211397637 / 1000000000000) (34211397638 / 1000000000000), orderedInterval (45742437833 / 1000000000000) (45742437834 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3164725687236923 / 4000000000000) 0 (IntervalRat.scale (851 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (7983911124 / 1000000000000) (7983911125 / 1000000000000), orderedInterval (27214465626 / 1000000000000) (27214465627 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2113890092825557 / 4000000000000) 0 (IntervalRat.scale (851 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (34532183700 / 1000000000000) (34532183872 / 1000000000000), orderedInterval (3455730527 / 1000000000000) (3455730699 / 1000000000000)))) (orderedInterval (-6922820815 / 1000000000000) (-6922820665 / 1000000000000))) = true
  rfl'

theorem compactCertificate554_chunkChecks0 :
    compactCertificate554.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate554.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate554_chunkChecks0_0
    compactCertificate554_chunkChecks0_1 compactCertificate554_chunkChecks0_2

theorem compactCertificate554_chunkChecks1_0 :
    compactCertificate554.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (851 / 2) 1 (IntervalRat.scale (851 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-31939577672 / 1000000000000) (-31939489664 / 1000000000000), orderedInterval (21855699403 / 1000000000000) (21855787411 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1253685496663751 / 4000000000000) 1 (IntervalRat.scale (851 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (2122320029 / 1000000000000) (2122320030 / 1000000000000), orderedInterval (45015419615 / 1000000000000) (45015419617 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (405416131026983 / 800000000000) 1 (IntervalRat.scale (851 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-34818139827 / 1000000000000) (-34818135081 / 1000000000000), orderedInterval (6662058490 / 1000000000000) (6662063237 / 1000000000000)))) (orderedInterval (9437409676 / 1000000000000) (9437444925 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (365822301190357 / 4000000000000) 1 (IntervalRat.scale (851 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-75578049559 / 1000000000000) (-75578049558 / 1000000000000), orderedInterval (-34926094499 / 1000000000000) (-34926094498 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (982650158160529 / 4000000000000) 1 (IntervalRat.scale (851 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (50192885926 / 1000000000000) (50192885934 / 1000000000000), orderedInterval (8389561705 / 1000000000000) (8389561712 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2668086332084493 / 4000000000000) 1 (IntervalRat.scale (851 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30160135047 / 1000000000000) (30160149696 / 1000000000000), orderedInterval (-6714932230 / 1000000000000) (-6714917581 / 1000000000000)))) (orderedInterval (1006616995 / 1000000000000) (1006618686 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1965300316321909 / 4000000000000) 1 (IntervalRat.scale (851 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (32397315677 / 1000000000000) (32397370568 / 1000000000000), orderedInterval (-15721583588 / 1000000000000) (-15721528697 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3367575589488457 / 4000000000000) 1 (IntervalRat.scale (851 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (18385419913 / 1000000000000) (18385419914 / 1000000000000), orderedInterval (20437849249 / 1000000000000) (20437849250 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2480540937401563 / 4000000000000) 1 (IntervalRat.scale (851 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-28768187403 / 1000000000000) (-28768087380 / 1000000000000), orderedInterval (14129034994 / 1000000000000) (14129135017 / 1000000000000)))) (orderedInterval (-749610325 / 1000000000000) (-749606760 / 1000000000000))) = true
  rfl'

theorem compactCertificate554_chunkChecks1_1 :
    compactCertificate554.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3805787697704149 / 4000000000000) 1 (IntervalRat.scale (851 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-8372684622 / 1000000000000) (-8372684621 / 1000000000000), orderedInterval (-24470182742 / 1000000000000) (-24470182741 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2197272551747821 / 4000000000000) 1 (IntervalRat.scale (851 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-10857140026 / 1000000000000) (-10857140025 / 1000000000000), orderedInterval (-32255426667 / 1000000000000) (-32255426666 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3899098701526289 / 4000000000000) 1 (IntervalRat.scale (851 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (25439428201 / 1000000000000) (25439448309 / 1000000000000), orderedInterval (-2448048090 / 1000000000000) (-2448027982 / 1000000000000)))) (orderedInterval (5840009747 / 1000000000000) (5840016646 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3643043784746741 / 4000000000000) 1 (IntervalRat.scale (851 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (12310381748 / 1000000000000) (12310381749 / 1000000000000), orderedInterval (23390938672 / 1000000000000) (23390938673 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2599847944270853 / 4000000000000) 1 (IntervalRat.scale (851 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-13259949272 / 1000000000000) (-13259949271 / 1000000000000), orderedInterval (-28338454584 / 1000000000000) (-28338454583 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2947950474481587 / 4000000000000) 1 (IntervalRat.scale (851 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (14127428609 / 1000000000000) (14127428708 / 1000000000000), orderedInterval (-25782230105 / 1000000000000) (-25782230006 / 1000000000000)))) (orderedInterval (-4771289444 / 1000000000000) (-4771289361 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2457693766336003 / 4000000000000) 1 (IntervalRat.scale (851 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-16646655444 / 1000000000000) (-16646655045 / 1000000000000), orderedInterval (27563763971 / 1000000000000) (27563764370 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2171446976932063 / 4000000000000) 1 (IntervalRat.scale (851 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-5164313505 / 1000000000000) (-5164313504 / 1000000000000), orderedInterval (-33848471262 / 1000000000000) (-33848471261 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (629369970126237 / 800000000000) 1 (IntervalRat.scale (851 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (24562071822 / 1000000000000) (24562104662 / 1000000000000), orderedInterval (-14365506063 / 1000000000000) (-14365473224 / 1000000000000)))) (orderedInterval (2250876959 / 1000000000000) (2250878579 / 1000000000000))) = true
  rfl'

theorem compactCertificate554_chunkChecks1_2 :
    compactCertificate554.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1740870459296039 / 4000000000000) 1 (IntervalRat.scale (851 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (24008773869 / 1000000000000) (24008779266 / 1000000000000), orderedInterval (-29799061567 / 1000000000000) (-29799056170 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1475755167957679 / 4000000000000) 1 (IntervalRat.scale (851 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-34592768221 / 1000000000000) (-34592665182 / 1000000000000), orderedInterval (23044356232 / 1000000000000) (23044459271 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (923459062598437 / 4000000000000) 1 (IntervalRat.scale (851 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-38687827519 / 1000000000000) (-38687767543 / 1000000000000), orderedInterval (35591471832 / 1000000000000) (35591531808 / 1000000000000)))) (orderedInterval (4371198759 / 1000000000000) (4371205857 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (496639355151579 / 4000000000000) 1 (IntervalRat.scale (851 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-47187513888 / 1000000000000) (-47187477066 / 1000000000000), orderedInterval (54048771149 / 1000000000000) (54048807971 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1348472459351737 / 4000000000000) 1 (IntervalRat.scale (851 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-42738706655 / 1000000000000) (-42738704928 / 1000000000000), orderedInterval (7925871462 / 1000000000000) (7925873190 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1841223858788249 / 4000000000000) 1 (IntervalRat.scale (851 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (24606542099 / 1000000000000) (24606549584 / 1000000000000), orderedInterval (-27911389376 / 1000000000000) (-27911381891 / 1000000000000)))) (orderedInterval (1880392498 / 1000000000000) (1880393394 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (778540937401563 / 4000000000000) 1 (IntervalRat.scale (851 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (34211397637 / 1000000000000) (34211397638 / 1000000000000), orderedInterval (45742437833 / 1000000000000) (45742437834 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3164725687236923 / 4000000000000) 1 (IntervalRat.scale (851 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (7983911124 / 1000000000000) (7983911125 / 1000000000000), orderedInterval (27214465626 / 1000000000000) (27214465627 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2113890092825557 / 4000000000000) 1 (IntervalRat.scale (851 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (34532183700 / 1000000000000) (34532183872 / 1000000000000), orderedInterval (3455730527 / 1000000000000) (3455730699 / 1000000000000)))) (orderedInterval (-4798337746 / 1000000000000) (-4798337540 / 1000000000000))) = true
  rfl'

theorem compactCertificate554_chunkChecks1 :
    compactCertificate554.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate554.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate554_chunkChecks1_0
    compactCertificate554_chunkChecks1_1 compactCertificate554_chunkChecks1_2

theorem compactCertificate554_chunkChecks2_0 :
    compactCertificate554.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (851 / 2) 2 (IntervalRat.scale (851 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-31939577672 / 1000000000000) (-31939489664 / 1000000000000), orderedInterval (21855699403 / 1000000000000) (21855787411 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1253685496663751 / 4000000000000) 2 (IntervalRat.scale (851 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (2122320029 / 1000000000000) (2122320030 / 1000000000000), orderedInterval (45015419615 / 1000000000000) (45015419617 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (405416131026983 / 800000000000) 2 (IntervalRat.scale (851 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-34818139827 / 1000000000000) (-34818135081 / 1000000000000), orderedInterval (6662058490 / 1000000000000) (6662063237 / 1000000000000)))) (orderedInterval (15524976991 / 1000000000000) (15525012391 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (365822301190357 / 4000000000000) 2 (IntervalRat.scale (851 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-75578049559 / 1000000000000) (-75578049558 / 1000000000000), orderedInterval (-34926094499 / 1000000000000) (-34926094498 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (982650158160529 / 4000000000000) 2 (IntervalRat.scale (851 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (50192885926 / 1000000000000) (50192885934 / 1000000000000), orderedInterval (8389561705 / 1000000000000) (8389561712 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2668086332084493 / 4000000000000) 2 (IntervalRat.scale (851 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30160135047 / 1000000000000) (30160149696 / 1000000000000), orderedInterval (-6714932230 / 1000000000000) (-6714917581 / 1000000000000)))) (orderedInterval (4617780406 / 1000000000000) (4617783050 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1965300316321909 / 4000000000000) 2 (IntervalRat.scale (851 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (32397315677 / 1000000000000) (32397370568 / 1000000000000), orderedInterval (-15721583588 / 1000000000000) (-15721528697 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3367575589488457 / 4000000000000) 2 (IntervalRat.scale (851 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (18385419913 / 1000000000000) (18385419914 / 1000000000000), orderedInterval (20437849249 / 1000000000000) (20437849250 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2480540937401563 / 4000000000000) 2 (IntervalRat.scale (851 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-28768187403 / 1000000000000) (-28768087380 / 1000000000000), orderedInterval (14129034994 / 1000000000000) (14129135017 / 1000000000000)))) (orderedInterval (3698611092 / 1000000000000) (3698616310 / 1000000000000))) = true
  rfl'

theorem compactCertificate554_chunkChecks2_1 :
    compactCertificate554.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3805787697704149 / 4000000000000) 2 (IntervalRat.scale (851 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-8372684622 / 1000000000000) (-8372684621 / 1000000000000), orderedInterval (-24470182742 / 1000000000000) (-24470182741 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2197272551747821 / 4000000000000) 2 (IntervalRat.scale (851 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-10857140026 / 1000000000000) (-10857140025 / 1000000000000), orderedInterval (-32255426667 / 1000000000000) (-32255426666 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3899098701526289 / 4000000000000) 2 (IntervalRat.scale (851 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (25439428201 / 1000000000000) (25439448309 / 1000000000000), orderedInterval (-2448048090 / 1000000000000) (-2448027982 / 1000000000000)))) (orderedInterval (-25091017092 / 1000000000000) (-25091001325 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3643043784746741 / 4000000000000) 2 (IntervalRat.scale (851 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (12310381748 / 1000000000000) (12310381749 / 1000000000000), orderedInterval (23390938672 / 1000000000000) (23390938673 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2599847944270853 / 4000000000000) 2 (IntervalRat.scale (851 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-13259949272 / 1000000000000) (-13259949271 / 1000000000000), orderedInterval (-28338454584 / 1000000000000) (-28338454583 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2947950474481587 / 4000000000000) 2 (IntervalRat.scale (851 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (14127428609 / 1000000000000) (14127428708 / 1000000000000), orderedInterval (-25782230105 / 1000000000000) (-25782230006 / 1000000000000)))) (orderedInterval (4169654906 / 1000000000000) (4169655044 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2457693766336003 / 4000000000000) 2 (IntervalRat.scale (851 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-16646655444 / 1000000000000) (-16646655045 / 1000000000000), orderedInterval (27563763971 / 1000000000000) (27563764370 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2171446976932063 / 4000000000000) 2 (IntervalRat.scale (851 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-5164313505 / 1000000000000) (-5164313504 / 1000000000000), orderedInterval (-33848471262 / 1000000000000) (-33848471261 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (629369970126237 / 800000000000) 2 (IntervalRat.scale (851 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (24562071822 / 1000000000000) (24562104662 / 1000000000000), orderedInterval (-14365506063 / 1000000000000) (-14365473224 / 1000000000000)))) (orderedInterval (-2235349282 / 1000000000000) (-2235346307 / 1000000000000))) = true
  rfl'

theorem compactCertificate554_chunkChecks2_2 :
    compactCertificate554.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1740870459296039 / 4000000000000) 2 (IntervalRat.scale (851 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (24008773869 / 1000000000000) (24008779266 / 1000000000000), orderedInterval (-29799061567 / 1000000000000) (-29799056170 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1475755167957679 / 4000000000000) 2 (IntervalRat.scale (851 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-34592768221 / 1000000000000) (-34592665182 / 1000000000000), orderedInterval (23044356232 / 1000000000000) (23044459271 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (923459062598437 / 4000000000000) 2 (IntervalRat.scale (851 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-38687827519 / 1000000000000) (-38687767543 / 1000000000000), orderedInterval (35591471832 / 1000000000000) (35591531808 / 1000000000000)))) (orderedInterval (2904658481 / 1000000000000) (2904664454 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (496639355151579 / 4000000000000) 2 (IntervalRat.scale (851 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-47187513888 / 1000000000000) (-47187477066 / 1000000000000), orderedInterval (54048771149 / 1000000000000) (54048807971 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1348472459351737 / 4000000000000) 2 (IntervalRat.scale (851 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-42738706655 / 1000000000000) (-42738704928 / 1000000000000), orderedInterval (7925871462 / 1000000000000) (7925873190 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1841223858788249 / 4000000000000) 2 (IntervalRat.scale (851 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (24606542099 / 1000000000000) (24606549584 / 1000000000000), orderedInterval (-27911389376 / 1000000000000) (-27911381891 / 1000000000000)))) (orderedInterval (1519707149 / 1000000000000) (1519707950 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (778540937401563 / 4000000000000) 2 (IntervalRat.scale (851 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (34211397637 / 1000000000000) (34211397638 / 1000000000000), orderedInterval (45742437833 / 1000000000000) (45742437834 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3164725687236923 / 4000000000000) 2 (IntervalRat.scale (851 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (7983911124 / 1000000000000) (7983911125 / 1000000000000), orderedInterval (27214465626 / 1000000000000) (27214465627 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2113890092825557 / 4000000000000) 2 (IntervalRat.scale (851 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (34532183700 / 1000000000000) (34532183872 / 1000000000000), orderedInterval (3455730527 / 1000000000000) (3455730699 / 1000000000000)))) (orderedInterval (12209688245 / 1000000000000) (12209688539 / 1000000000000))) = true
  rfl'

theorem compactCertificate554_chunkChecks2 :
    compactCertificate554.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate554.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate554_chunkChecks2_0
    compactCertificate554_chunkChecks2_1 compactCertificate554_chunkChecks2_2

theorem compactCertificate554_chunkChecks3_0 :
    compactCertificate554.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (851 / 2) 3 (IntervalRat.scale (851 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-31939577672 / 1000000000000) (-31939489664 / 1000000000000), orderedInterval (21855699403 / 1000000000000) (21855787411 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1253685496663751 / 4000000000000) 3 (IntervalRat.scale (851 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (2122320029 / 1000000000000) (2122320030 / 1000000000000), orderedInterval (45015419615 / 1000000000000) (45015419617 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (405416131026983 / 800000000000) 3 (IntervalRat.scale (851 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-34818139827 / 1000000000000) (-34818135081 / 1000000000000), orderedInterval (6662058490 / 1000000000000) (6662063237 / 1000000000000)))) (orderedInterval (-9527394694 / 1000000000000) (-9527359213 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (365822301190357 / 4000000000000) 3 (IntervalRat.scale (851 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-75578049559 / 1000000000000) (-75578049558 / 1000000000000), orderedInterval (-34926094499 / 1000000000000) (-34926094498 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (982650158160529 / 4000000000000) 3 (IntervalRat.scale (851 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (50192885926 / 1000000000000) (50192885934 / 1000000000000), orderedInterval (8389561705 / 1000000000000) (8389561712 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2668086332084493 / 4000000000000) 3 (IntervalRat.scale (851 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30160135047 / 1000000000000) (30160149696 / 1000000000000), orderedInterval (-6714932230 / 1000000000000) (-6714917581 / 1000000000000)))) (orderedInterval (-1912506271 / 1000000000000) (-1912502133 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1965300316321909 / 4000000000000) 3 (IntervalRat.scale (851 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (32397315677 / 1000000000000) (32397370568 / 1000000000000), orderedInterval (-15721583588 / 1000000000000) (-15721528697 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3367575589488457 / 4000000000000) 3 (IntervalRat.scale (851 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (18385419913 / 1000000000000) (18385419914 / 1000000000000), orderedInterval (20437849249 / 1000000000000) (20437849250 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2480540937401563 / 4000000000000) 3 (IntervalRat.scale (851 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-28768187403 / 1000000000000) (-28768087380 / 1000000000000), orderedInterval (14129034994 / 1000000000000) (14129135017 / 1000000000000)))) (orderedInterval (3817116827 / 1000000000000) (3817124457 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate554_chunkChecks3_1 :
    compactCertificate554.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3805787697704149 / 4000000000000) 3 (IntervalRat.scale (851 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-8372684622 / 1000000000000) (-8372684621 / 1000000000000), orderedInterval (-24470182742 / 1000000000000) (-24470182741 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2197272551747821 / 4000000000000) 3 (IntervalRat.scale (851 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-10857140026 / 1000000000000) (-10857140025 / 1000000000000), orderedInterval (-32255426667 / 1000000000000) (-32255426666 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3899098701526289 / 4000000000000) 3 (IntervalRat.scale (851 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (25439428201 / 1000000000000) (25439448309 / 1000000000000), orderedInterval (-2448048090 / 1000000000000) (-2448027982 / 1000000000000)))) (orderedInterval (-39227546276 / 1000000000000) (-39227510229 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3643043784746741 / 4000000000000) 3 (IntervalRat.scale (851 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (12310381748 / 1000000000000) (12310381749 / 1000000000000), orderedInterval (23390938672 / 1000000000000) (23390938673 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2599847944270853 / 4000000000000) 3 (IntervalRat.scale (851 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-13259949272 / 1000000000000) (-13259949271 / 1000000000000), orderedInterval (-28338454584 / 1000000000000) (-28338454583 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2947950474481587 / 4000000000000) 3 (IntervalRat.scale (851 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (14127428609 / 1000000000000) (14127428708 / 1000000000000), orderedInterval (-25782230105 / 1000000000000) (-25782230006 / 1000000000000)))) (orderedInterval (13004585298 / 1000000000000) (13004585532 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2457693766336003 / 4000000000000) 3 (IntervalRat.scale (851 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-16646655444 / 1000000000000) (-16646655045 / 1000000000000), orderedInterval (27563763971 / 1000000000000) (27563764370 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2171446976932063 / 4000000000000) 3 (IntervalRat.scale (851 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-5164313505 / 1000000000000) (-5164313504 / 1000000000000), orderedInterval (-33848471262 / 1000000000000) (-33848471261 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (629369970126237 / 800000000000) 3 (IntervalRat.scale (851 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (24562071822 / 1000000000000) (24562104662 / 1000000000000), orderedInterval (-14365506063 / 1000000000000) (-14365473224 / 1000000000000)))) (orderedInterval (-2650961210 / 1000000000000) (-2650955740 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate554_chunkChecks3_2 :
    compactCertificate554.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1740870459296039 / 4000000000000) 3 (IntervalRat.scale (851 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (24008773869 / 1000000000000) (24008779266 / 1000000000000), orderedInterval (-29799061567 / 1000000000000) (-29799056170 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1475755167957679 / 4000000000000) 3 (IntervalRat.scale (851 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-34592768221 / 1000000000000) (-34592665182 / 1000000000000), orderedInterval (23044356232 / 1000000000000) (23044459271 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (923459062598437 / 4000000000000) 3 (IntervalRat.scale (851 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-38687827519 / 1000000000000) (-38687767543 / 1000000000000), orderedInterval (35591471832 / 1000000000000) (35591531808 / 1000000000000)))) (orderedInterval (-4440231662 / 1000000000000) (-4440226520 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (496639355151579 / 4000000000000) 3 (IntervalRat.scale (851 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-47187513888 / 1000000000000) (-47187477066 / 1000000000000), orderedInterval (54048771149 / 1000000000000) (54048807971 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1348472459351737 / 4000000000000) 3 (IntervalRat.scale (851 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-42738706655 / 1000000000000) (-42738704928 / 1000000000000), orderedInterval (7925871462 / 1000000000000) (7925873190 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1841223858788249 / 4000000000000) 3 (IntervalRat.scale (851 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (24606542099 / 1000000000000) (24606549584 / 1000000000000), orderedInterval (-27911389376 / 1000000000000) (-27911381891 / 1000000000000)))) (orderedInterval (-2597481520 / 1000000000000) (-2597480709 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (778540937401563 / 4000000000000) 3 (IntervalRat.scale (851 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (34211397637 / 1000000000000) (34211397638 / 1000000000000), orderedInterval (45742437833 / 1000000000000) (45742437834 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3164725687236923 / 4000000000000) 3 (IntervalRat.scale (851 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (7983911124 / 1000000000000) (7983911125 / 1000000000000), orderedInterval (27214465626 / 1000000000000) (27214465627 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2113890092825557 / 4000000000000) 3 (IntervalRat.scale (851 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (34532183700 / 1000000000000) (34532183872 / 1000000000000), orderedInterval (3455730527 / 1000000000000) (3455730699 / 1000000000000)))) (orderedInterval (15428863959 / 1000000000000) (15428864398 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate554_chunkChecks3 :
    compactCertificate554.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate554.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate554_chunkChecks3_0
    compactCertificate554_chunkChecks3_1 compactCertificate554_chunkChecks3_2

theorem compactCertificate554_chunkChecks4_0 :
    compactCertificate554.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (851 / 2) 4 (IntervalRat.scale (851 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-31939577672 / 1000000000000) (-31939489664 / 1000000000000), orderedInterval (21855699403 / 1000000000000) (21855787411 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1253685496663751 / 4000000000000) 4 (IntervalRat.scale (851 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (2122320029 / 1000000000000) (2122320030 / 1000000000000), orderedInterval (45015419615 / 1000000000000) (45015419617 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (405416131026983 / 800000000000) 4 (IntervalRat.scale (851 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-34818139827 / 1000000000000) (-34818135081 / 1000000000000), orderedInterval (6662058490 / 1000000000000) (6662063237 / 1000000000000)))) (orderedInterval (-16720065087 / 1000000000000) (-16720029425 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (365822301190357 / 4000000000000) 4 (IntervalRat.scale (851 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-75578049559 / 1000000000000) (-75578049558 / 1000000000000), orderedInterval (-34926094499 / 1000000000000) (-34926094498 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (982650158160529 / 4000000000000) 4 (IntervalRat.scale (851 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (50192885926 / 1000000000000) (50192885934 / 1000000000000), orderedInterval (8389561705 / 1000000000000) (8389561712 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2668086332084493 / 4000000000000) 4 (IntervalRat.scale (851 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30160135047 / 1000000000000) (30160149696 / 1000000000000), orderedInterval (-6714932230 / 1000000000000) (-6714917581 / 1000000000000)))) (orderedInterval (-12733562282 / 1000000000000) (-12733555789 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1965300316321909 / 4000000000000) 4 (IntervalRat.scale (851 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (32397315677 / 1000000000000) (32397370568 / 1000000000000), orderedInterval (-15721583588 / 1000000000000) (-15721528697 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3367575589488457 / 4000000000000) 4 (IntervalRat.scale (851 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (18385419913 / 1000000000000) (18385419914 / 1000000000000), orderedInterval (20437849249 / 1000000000000) (20437849250 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2480540937401563 / 4000000000000) 4 (IntervalRat.scale (851 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-28768187403 / 1000000000000) (-28768087380 / 1000000000000), orderedInterval (14129034994 / 1000000000000) (14129135017 / 1000000000000)))) (orderedInterval (-11845938437 / 1000000000000) (-11845927246 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate554_chunkChecks4_1 :
    compactCertificate554.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3805787697704149 / 4000000000000) 4 (IntervalRat.scale (851 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-8372684622 / 1000000000000) (-8372684621 / 1000000000000), orderedInterval (-24470182742 / 1000000000000) (-24470182741 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2197272551747821 / 4000000000000) 4 (IntervalRat.scale (851 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-10857140026 / 1000000000000) (-10857140025 / 1000000000000), orderedInterval (-32255426667 / 1000000000000) (-32255426666 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3899098701526289 / 4000000000000) 4 (IntervalRat.scale (851 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (25439428201 / 1000000000000) (25439448309 / 1000000000000), orderedInterval (-2448048090 / 1000000000000) (-2448027982 / 1000000000000)))) (orderedInterval (134750092935 / 1000000000000) (134750175478 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3643043784746741 / 4000000000000) 4 (IntervalRat.scale (851 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (12310381748 / 1000000000000) (12310381749 / 1000000000000), orderedInterval (23390938672 / 1000000000000) (23390938673 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2599847944270853 / 4000000000000) 4 (IntervalRat.scale (851 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-13259949272 / 1000000000000) (-13259949271 / 1000000000000), orderedInterval (-28338454584 / 1000000000000) (-28338454583 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2947950474481587 / 4000000000000) 4 (IntervalRat.scale (851 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (14127428609 / 1000000000000) (14127428708 / 1000000000000), orderedInterval (-25782230105 / 1000000000000) (-25782230006 / 1000000000000)))) (orderedInterval (-12196221696 / 1000000000000) (-12196221290 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2457693766336003 / 4000000000000) 4 (IntervalRat.scale (851 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-16646655444 / 1000000000000) (-16646655045 / 1000000000000), orderedInterval (27563763971 / 1000000000000) (27563764370 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2171446976932063 / 4000000000000) 4 (IntervalRat.scale (851 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-5164313505 / 1000000000000) (-5164313504 / 1000000000000), orderedInterval (-33848471262 / 1000000000000) (-33848471261 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (629369970126237 / 800000000000) 4 (IntervalRat.scale (851 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (24562071822 / 1000000000000) (24562104662 / 1000000000000), orderedInterval (-14365506063 / 1000000000000) (-14365473224 / 1000000000000)))) (orderedInterval (7308840338 / 1000000000000) (7308850423 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate554_chunkChecks4_2 :
    compactCertificate554.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1740870459296039 / 4000000000000) 4 (IntervalRat.scale (851 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (24008773869 / 1000000000000) (24008779266 / 1000000000000), orderedInterval (-29799061567 / 1000000000000) (-29799056170 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1475755167957679 / 4000000000000) 4 (IntervalRat.scale (851 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-34592768221 / 1000000000000) (-34592665182 / 1000000000000), orderedInterval (23044356232 / 1000000000000) (23044459271 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (923459062598437 / 4000000000000) 4 (IntervalRat.scale (851 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-38687827519 / 1000000000000) (-38687767543 / 1000000000000), orderedInterval (35591471832 / 1000000000000) (35591531808 / 1000000000000)))) (orderedInterval (-3183297489 / 1000000000000) (-3183292965 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (496639355151579 / 4000000000000) 4 (IntervalRat.scale (851 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-47187513888 / 1000000000000) (-47187477066 / 1000000000000), orderedInterval (54048771149 / 1000000000000) (54048807971 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1348472459351737 / 4000000000000) 4 (IntervalRat.scale (851 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-42738706655 / 1000000000000) (-42738704928 / 1000000000000), orderedInterval (7925871462 / 1000000000000) (7925873190 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1841223858788249 / 4000000000000) 4 (IntervalRat.scale (851 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (24606542099 / 1000000000000) (24606549584 / 1000000000000), orderedInterval (-27911389376 / 1000000000000) (-27911381891 / 1000000000000)))) (orderedInterval (-2182193935 / 1000000000000) (-2182193076 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (778540937401563 / 4000000000000) 4 (IntervalRat.scale (851 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (34211397637 / 1000000000000) (34211397638 / 1000000000000), orderedInterval (45742437833 / 1000000000000) (45742437834 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3164725687236923 / 4000000000000) 4 (IntervalRat.scale (851 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (7983911124 / 1000000000000) (7983911125 / 1000000000000), orderedInterval (27214465626 / 1000000000000) (27214465627 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2113890092825557 / 4000000000000) 4 (IntervalRat.scale (851 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (34532183700 / 1000000000000) (34532183872 / 1000000000000), orderedInterval (3455730527 / 1000000000000) (3455730699 / 1000000000000)))) (orderedInterval (-23249603039 / 1000000000000) (-23249602356 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate554_chunkChecks4 :
    compactCertificate554.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate554.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate554_chunkChecks4_0
    compactCertificate554_chunkChecks4_1 compactCertificate554_chunkChecks4_2

theorem compactCertificate554_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate554.chunkCheck r b = true :=
  compactCertificate554.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate554_chunkChecks0
    · exact compactCertificate554_chunkChecks1
    · exact compactCertificate554_chunkChecks2
    · exact compactCertificate554_chunkChecks3
    · exact compactCertificate554_chunkChecks4)

theorem compactCertificate554_coefficient0 :
    compactCertificate554.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate554_coefficient1 :
    compactCertificate554.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate554_coefficient2 :
    compactCertificate554.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate554_coefficient3 :
    compactCertificate554.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate554_coefficient4 :
    compactCertificate554.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate554_coefficients : ∀ r : Fin 5,
    compactCertificate554.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate554_coefficient0
  · exact compactCertificate554_coefficient1
  · exact compactCertificate554_coefficient2
  · exact compactCertificate554_coefficient3
  · exact compactCertificate554_coefficient4

theorem compactCertificate554_lower : (1 : ℚ) ≤ compactCertificate554.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate554, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate554_proves {t : ℝ} (ht : t ∈ compactCertificate554.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate554.proves compactCertificate554_states compactCertificate554_chunks
    compactCertificate554_coefficients compactCertificate554_lower ht

end Erdos232
