/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate327 : CompactCertificate where
  left := 199
  right := 200
  center := 399 / 2
  grid := fun i =>
    match i.val with
    | 0 => 64
    | 1 => 47
    | 2 => 76
    | 3 => 14
    | 4 => 37
    | 5 => 100
    | 6 => 73
    | 7 => 126
    | 8 => 93
    | 9 => 142
    | 10 => 82
    | 11 => 146
    | 12 => 136
    | 13 => 97
    | 14 => 110
    | 15 => 92
    | 16 => 81
    | 17 => 117
    | 18 => 65
    | 19 => 55
    | 20 => 34
    | 21 => 19
    | 22 => 50
    | 23 => 69
    | 24 => 29
    | 25 => 118
    | _ => 79
  point := fun i =>
    match i.val with
    | 0 => 399 / 2
    | 1 => 587803188212499 / 4000000000000
    | 2 => 190083473889267 / 800000000000
    | 3 => 171519504318393 / 4000000000000
    | 4 => 460725514813221 / 4000000000000
    | 5 => 1250959396594257 / 4000000000000
    | 6 => 921451029626841 / 4000000000000
    | 7 => 1578922044895293 / 4000000000000
    | 8 => 1163026831989687 / 4000000000000
    | 9 => 1784382246044601 / 4000000000000
    | 10 => 1030213570090929 / 4000000000000
    | 11 => 1828132058647461 / 4000000000000
    | 12 => 1708078108242009 / 4000000000000
    | 13 => 1218965134857897 / 4000000000000
    | 14 => 1382176544439663 / 4000000000000
    | 15 => 1152314703605247 / 4000000000000
    | 16 => 1018104986834187 / 4000000000000
    | 17 => 295086507732513 / 800000000000
    | 18 => 816224809940211 / 4000000000000
    | 19 => 691922810828571 / 4000000000000
    | 20 => 432973168010313 / 4000000000000
    | 21 => 232854409759671 / 4000000000000
    | 22 => 632245019132013 / 4000000000000
    | 23 => 863276521335501 / 4000000000000
    | 24 => 365026831989687 / 4000000000000
    | 25 => 1483813806354327 / 4000000000000
    | _ => 991118856683193 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-39613658321 / 1000000000000) (-39613614332 / 1000000000000), orderedInterval (40371289657 / 1000000000000) (40371333646 / 1000000000000))
    | 1 => (orderedInterval (-5292064693 / 1000000000000) (-5292064691 / 1000000000000), orderedInterval (-65588514977 / 1000000000000) (-65588514975 / 1000000000000))
    | 2 => (orderedInterval (-18806145617 / 1000000000000) (-18806145110 / 1000000000000), orderedInterval (48264675839 / 1000000000000) (48264676346 / 1000000000000))
    | 3 => (orderedInterval (-38320291530 / 1000000000000) (-38320290655 / 1000000000000), orderedInterval (116114184624 / 1000000000000) (116114185500 / 1000000000000))
    | 4 => (orderedInterval (20061720058 / 1000000000000) (20061720374 / 1000000000000), orderedInterval (-71673946481 / 1000000000000) (-71673946164 / 1000000000000))
    | 5 => (orderedInterval (-26741729397 / 1000000000000) (-26741722906 / 1000000000000), orderedInterval (36381459173 / 1000000000000) (36381465664 / 1000000000000))
    | 6 => (orderedInterval (-51055784964 / 1000000000000) (-51055783142 / 1000000000000), orderedInterval (12634971300 / 1000000000000) (12634973121 / 1000000000000))
    | 7 => (orderedInterval (-12826424688 / 1000000000000) (-12826424594 / 1000000000000), orderedInterval (38072518710 / 1000000000000) (38072518805 / 1000000000000))
    | 8 => (orderedInterval (27432708954 / 1000000000000) (27432715659 / 1000000000000), orderedInterval (-37954626657 / 1000000000000) (-37954619953 / 1000000000000))
    | 9 => (orderedInterval (26420197519 / 1000000000000) (26420197520 / 1000000000000), orderedInterval (26971609547 / 1000000000000) (26971609548 / 1000000000000))
    | 10 => (orderedInterval (33069831827 / 1000000000000) (33069831828 / 1000000000000), orderedInterval (37059701329 / 1000000000000) (37059701330 / 1000000000000))
    | 11 => (orderedInterval (-28147197492 / 1000000000000) (-28147170294 / 1000000000000), orderedInterval (24539478938 / 1000000000000) (24539506136 / 1000000000000))
    | 12 => (orderedInterval (20116875773 / 1000000000000) (20116875774 / 1000000000000), orderedInterval (32933332258 / 1000000000000) (32933332259 / 1000000000000))
    | 13 => (orderedInterval (-32524823708 / 1000000000000) (-32524823707 / 1000000000000), orderedInterval (-32058717114 / 1000000000000) (-32058717113 / 1000000000000))
    | 14 => (orderedInterval (29382630036 / 1000000000000) (29382630037 / 1000000000000), orderedInterval (31246939999 / 1000000000000) (31246940000 / 1000000000000))
    | 15 => (orderedInterval (-7623254830 / 1000000000000) (-7623254811 / 1000000000000), orderedInterval (46400414342 / 1000000000000) (46400414361 / 1000000000000))
    | 16 => (orderedInterval (-37312661526 / 1000000000000) (-37312661525 / 1000000000000), orderedInterval (-33227749011 / 1000000000000) (-33227749010 / 1000000000000))
    | 17 => (orderedInterval (-36337161530 / 1000000000000) (-36337109884 / 1000000000000), orderedInterval (20187055998 / 1000000000000) (20187107645 / 1000000000000))
    | 18 => (orderedInterval (-33242888206 / 1000000000000) (-33242888205 / 1000000000000), orderedInterval (-44804386613 / 1000000000000) (-44804386612 / 1000000000000))
    | 19 => (orderedInterval (-50307305563 / 1000000000000) (-50307305562 / 1000000000000), orderedInterval (-33758317046 / 1000000000000) (-33758317045 / 1000000000000))
    | 20 => (orderedInterval (61393711819 / 1000000000000) (61393765858 / 1000000000000), orderedInterval (-46241956218 / 1000000000000) (-46241902180 / 1000000000000))
    | 21 => (orderedInterval (66838993099 / 1000000000000) (66839032049 / 1000000000000), orderedInterval (-81001344519 / 1000000000000) (-81001305570 / 1000000000000))
    | 22 => (orderedInterval (62255707901 / 1000000000000) (62255708597 / 1000000000000), orderedInterval (-12521126995 / 1000000000000) (-12521126298 / 1000000000000))
    | 23 => (orderedInterval (8971404582 / 1000000000000) (8971404616 / 1000000000000), orderedInterval (-53586680075 / 1000000000000) (-53586680040 / 1000000000000))
    | 24 => (orderedInterval (-67179919730 / 1000000000000) (-67179919729 / 1000000000000), orderedInterval (-49260245718 / 1000000000000) (-49260245717 / 1000000000000))
    | 25 => (orderedInterval (35527409630 / 1000000000000) (35527409631 / 1000000000000), orderedInterval (21258779428 / 1000000000000) (21258779429 / 1000000000000))
    | _ => (orderedInterval (-18744230708 / 1000000000000) (-18744230707 / 1000000000000), orderedInterval (-47057345408 / 1000000000000) (-47057345407 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-16854345251 / 1000000000000) (-16854327770 / 1000000000000)
      | 1 => orderedInterval (3049295880 / 1000000000000) (3049296387 / 1000000000000)
      | 2 => orderedInterval (1058612698 / 1000000000000) (1058612875 / 1000000000000)
      | 3 => orderedInterval (-6245637702 / 1000000000000) (-6245633755 / 1000000000000)
      | 4 => orderedInterval (-3587505279 / 1000000000000) (-3587505254 / 1000000000000)
      | 5 => orderedInterval (1116873921 / 1000000000000) (1116875264 / 1000000000000)
      | 6 => orderedInterval (10161366756 / 1000000000000) (10161368566 / 1000000000000)
      | 7 => orderedInterval (-3334135541 / 1000000000000) (-3334134779 / 1000000000000)
      | _ => orderedInterval (219938014 / 1000000000000) (219938070 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (18924769092 / 1000000000000) (18924786579 / 1000000000000)
      | 1 => orderedInterval (-5836061768 / 1000000000000) (-5836061008 / 1000000000000)
      | 2 => orderedInterval (-3660367347 / 1000000000000) (-3660367085 / 1000000000000)
      | 3 => orderedInterval (820036361 / 1000000000000) (820045383 / 1000000000000)
      | 4 => orderedInterval (-6177275797 / 1000000000000) (-6177275758 / 1000000000000)
      | 5 => orderedInterval (4155356358 / 1000000000000) (4155358832 / 1000000000000)
      | 6 => orderedInterval (8167422149 / 1000000000000) (8167423151 / 1000000000000)
      | 7 => orderedInterval (5104263480 / 1000000000000) (5104263727 / 1000000000000)
      | _ => orderedInterval (7612346092 / 1000000000000) (7612346171 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (17198729480 / 1000000000000) (17198747064 / 1000000000000)
      | 1 => orderedInterval (-4905832270 / 1000000000000) (-4905831090 / 1000000000000)
      | 2 => orderedInterval (-2938702839 / 1000000000000) (-2938702447 / 1000000000000)
      | 3 => orderedInterval (40384469043 / 1000000000000) (40384489732 / 1000000000000)
      | 4 => orderedInterval (9317416134 / 1000000000000) (9317416199 / 1000000000000)
      | 5 => orderedInterval (-132443770 / 1000000000000) (-132439195 / 1000000000000)
      | 6 => orderedInterval (-8330870041 / 1000000000000) (-8330869473 / 1000000000000)
      | 7 => orderedInterval (1770725942 / 1000000000000) (1770726040 / 1000000000000)
      | _ => orderedInterval (4620343000 / 1000000000000) (4620343116 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-20628048112 / 1000000000000) (-20628030517 / 1000000000000)
      | 1 => orderedInterval (10503979589 / 1000000000000) (10503981432 / 1000000000000)
      | 2 => orderedInterval (11950408632 / 1000000000000) (11950409222 / 1000000000000)
      | 3 => orderedInterval (5530065398 / 1000000000000) (5530112757 / 1000000000000)
      | 4 => orderedInterval (17410418063 / 1000000000000) (17410418172 / 1000000000000)
      | 5 => orderedInterval (-8828242905 / 1000000000000) (-8828234460 / 1000000000000)
      | 6 => orderedInterval (-8629138727 / 1000000000000) (-8629138400 / 1000000000000)
      | 7 => orderedInterval (-5386509877 / 1000000000000) (-5386509824 / 1000000000000)
      | _ => orderedInterval (-5785210599 / 1000000000000) (-5785210421 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-17729223562 / 1000000000000) (-17729205868 / 1000000000000)
      | 1 => orderedInterval (11457248598 / 1000000000000) (11457251491 / 1000000000000)
      | 2 => orderedInterval (8934682721 / 1000000000000) (8934683619 / 1000000000000)
      | 3 => orderedInterval (-220821481106 / 1000000000000) (-220821372434 / 1000000000000)
      | 4 => orderedInterval (-25880792011 / 1000000000000) (-25880791821 / 1000000000000)
      | 5 => orderedInterval (-5509248613 / 1000000000000) (-5509232975 / 1000000000000)
      | 6 => orderedInterval (7686656897 / 1000000000000) (7686657096 / 1000000000000)
      | 7 => orderedInterval (-1453095200 / 1000000000000) (-1453095161 / 1000000000000)
      | _ => orderedInterval (-26161337593 / 1000000000000) (-26161337307 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-14415536504 / 1000000000000) (-14415510396 / 1000000000000)
    | 1 => orderedInterval (29110488620 / 1000000000000) (29110519992 / 1000000000000)
    | 2 => orderedInterval (56983834679 / 1000000000000) (56983879946 / 1000000000000)
    | 3 => orderedInterval (-3862278538 / 1000000000000) (-3862202039 / 1000000000000)
    | _ => orderedInterval (-269476589869 / 1000000000000) (-269476443360 / 1000000000000)

theorem compactCertificate327_stateChecks0 :
    compactCertificate327.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (399 / 2)) (orderedInterval (-39613658321 / 1000000000000) (-39613614332 / 1000000000000), orderedInterval (40371289657 / 1000000000000) (40371333646 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 47 12 (587803188212499 / 4000000000000)) (orderedInterval (-5292064693 / 1000000000000) (-5292064691 / 1000000000000), orderedInterval (-65588514977 / 1000000000000) (-65588514975 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 76 12 (190083473889267 / 800000000000)) (orderedInterval (-18806145617 / 1000000000000) (-18806145110 / 1000000000000), orderedInterval (48264675839 / 1000000000000) (48264676346 / 1000000000000))) = true
  rfl'

theorem compactCertificate327_stateChecks1 :
    compactCertificate327.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 14 12 (171519504318393 / 4000000000000)) (orderedInterval (-38320291530 / 1000000000000) (-38320290655 / 1000000000000), orderedInterval (116114184624 / 1000000000000) (116114185500 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 37 12 (460725514813221 / 4000000000000)) (orderedInterval (20061720058 / 1000000000000) (20061720374 / 1000000000000), orderedInterval (-71673946481 / 1000000000000) (-71673946164 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 100 12 (1250959396594257 / 4000000000000)) (orderedInterval (-26741729397 / 1000000000000) (-26741722906 / 1000000000000), orderedInterval (36381459173 / 1000000000000) (36381465664 / 1000000000000))) = true
  rfl'

theorem compactCertificate327_stateChecks2 :
    compactCertificate327.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 73 12 (921451029626841 / 4000000000000)) (orderedInterval (-51055784964 / 1000000000000) (-51055783142 / 1000000000000), orderedInterval (12634971300 / 1000000000000) (12634973121 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 126 12 (1578922044895293 / 4000000000000)) (orderedInterval (-12826424688 / 1000000000000) (-12826424594 / 1000000000000), orderedInterval (38072518710 / 1000000000000) (38072518805 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 93 12 (1163026831989687 / 4000000000000)) (orderedInterval (27432708954 / 1000000000000) (27432715659 / 1000000000000), orderedInterval (-37954626657 / 1000000000000) (-37954619953 / 1000000000000))) = true
  rfl'

theorem compactCertificate327_stateChecks3 :
    compactCertificate327.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 142 12 (1784382246044601 / 4000000000000)) (orderedInterval (26420197519 / 1000000000000) (26420197520 / 1000000000000), orderedInterval (26971609547 / 1000000000000) (26971609548 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 82 12 (1030213570090929 / 4000000000000)) (orderedInterval (33069831827 / 1000000000000) (33069831828 / 1000000000000), orderedInterval (37059701329 / 1000000000000) (37059701330 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 146 12 (1828132058647461 / 4000000000000)) (orderedInterval (-28147197492 / 1000000000000) (-28147170294 / 1000000000000), orderedInterval (24539478938 / 1000000000000) (24539506136 / 1000000000000))) = true
  rfl'

theorem compactCertificate327_stateChecks4 :
    compactCertificate327.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 136 12 (1708078108242009 / 4000000000000)) (orderedInterval (20116875773 / 1000000000000) (20116875774 / 1000000000000), orderedInterval (32933332258 / 1000000000000) (32933332259 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 97 12 (1218965134857897 / 4000000000000)) (orderedInterval (-32524823708 / 1000000000000) (-32524823707 / 1000000000000), orderedInterval (-32058717114 / 1000000000000) (-32058717113 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 110 12 (1382176544439663 / 4000000000000)) (orderedInterval (29382630036 / 1000000000000) (29382630037 / 1000000000000), orderedInterval (31246939999 / 1000000000000) (31246940000 / 1000000000000))) = true
  rfl'

theorem compactCertificate327_stateChecks5 :
    compactCertificate327.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 92 12 (1152314703605247 / 4000000000000)) (orderedInterval (-7623254830 / 1000000000000) (-7623254811 / 1000000000000), orderedInterval (46400414342 / 1000000000000) (46400414361 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 81 12 (1018104986834187 / 4000000000000)) (orderedInterval (-37312661526 / 1000000000000) (-37312661525 / 1000000000000), orderedInterval (-33227749011 / 1000000000000) (-33227749010 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 117 12 (295086507732513 / 800000000000)) (orderedInterval (-36337161530 / 1000000000000) (-36337109884 / 1000000000000), orderedInterval (20187055998 / 1000000000000) (20187107645 / 1000000000000))) = true
  rfl'

theorem compactCertificate327_stateChecks6 :
    compactCertificate327.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 65 12 (816224809940211 / 4000000000000)) (orderedInterval (-33242888206 / 1000000000000) (-33242888205 / 1000000000000), orderedInterval (-44804386613 / 1000000000000) (-44804386612 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (691922810828571 / 4000000000000)) (orderedInterval (-50307305563 / 1000000000000) (-50307305562 / 1000000000000), orderedInterval (-33758317046 / 1000000000000) (-33758317045 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (432973168010313 / 4000000000000)) (orderedInterval (61393711819 / 1000000000000) (61393765858 / 1000000000000), orderedInterval (-46241956218 / 1000000000000) (-46241902180 / 1000000000000))) = true
  rfl'

theorem compactCertificate327_stateChecks7 :
    compactCertificate327.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 19 12 (232854409759671 / 4000000000000)) (orderedInterval (66838993099 / 1000000000000) (66839032049 / 1000000000000), orderedInterval (-81001344519 / 1000000000000) (-81001305570 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 50 12 (632245019132013 / 4000000000000)) (orderedInterval (62255707901 / 1000000000000) (62255708597 / 1000000000000), orderedInterval (-12521126995 / 1000000000000) (-12521126298 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (863276521335501 / 4000000000000)) (orderedInterval (8971404582 / 1000000000000) (8971404616 / 1000000000000), orderedInterval (-53586680075 / 1000000000000) (-53586680040 / 1000000000000))) = true
  rfl'

theorem compactCertificate327_stateChecks8 :
    compactCertificate327.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 29 12 (365026831989687 / 4000000000000)) (orderedInterval (-67179919730 / 1000000000000) (-67179919729 / 1000000000000), orderedInterval (-49260245718 / 1000000000000) (-49260245717 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 118 12 (1483813806354327 / 4000000000000)) (orderedInterval (35527409630 / 1000000000000) (35527409631 / 1000000000000), orderedInterval (21258779428 / 1000000000000) (21258779429 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 79 12 (991118856683193 / 4000000000000)) (orderedInterval (-18744230708 / 1000000000000) (-18744230707 / 1000000000000), orderedInterval (-47057345408 / 1000000000000) (-47057345407 / 1000000000000))) = true
  rfl'

theorem compactCertificate327_states : ∀ j,
    BesselStateValid (compactCertificate327.point j) (compactCertificate327.state j) :=
  compactCertificate327.statesValid_of_checks3 compactCertificate327_stateChecks0
    compactCertificate327_stateChecks1 compactCertificate327_stateChecks2
    compactCertificate327_stateChecks3 compactCertificate327_stateChecks4
    compactCertificate327_stateChecks5 compactCertificate327_stateChecks6
    compactCertificate327_stateChecks7 compactCertificate327_stateChecks8

theorem compactCertificate327_chunkChecks0_0 :
    compactCertificate327.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (399 / 2) 0 (IntervalRat.scale (399 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-39613658321 / 1000000000000) (-39613614332 / 1000000000000), orderedInterval (40371289657 / 1000000000000) (40371333646 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (587803188212499 / 4000000000000) 0 (IntervalRat.scale (399 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-5292064693 / 1000000000000) (-5292064691 / 1000000000000), orderedInterval (-65588514977 / 1000000000000) (-65588514975 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (190083473889267 / 800000000000) 0 (IntervalRat.scale (399 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-18806145617 / 1000000000000) (-18806145110 / 1000000000000), orderedInterval (48264675839 / 1000000000000) (48264676346 / 1000000000000)))) (orderedInterval (-16854345251 / 1000000000000) (-16854327770 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (171519504318393 / 4000000000000) 0 (IntervalRat.scale (399 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-38320291530 / 1000000000000) (-38320290655 / 1000000000000), orderedInterval (116114184624 / 1000000000000) (116114185500 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (460725514813221 / 4000000000000) 0 (IntervalRat.scale (399 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (20061720058 / 1000000000000) (20061720374 / 1000000000000), orderedInterval (-71673946481 / 1000000000000) (-71673946164 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1250959396594257 / 4000000000000) 0 (IntervalRat.scale (399 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-26741729397 / 1000000000000) (-26741722906 / 1000000000000), orderedInterval (36381459173 / 1000000000000) (36381465664 / 1000000000000)))) (orderedInterval (3049295880 / 1000000000000) (3049296387 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (921451029626841 / 4000000000000) 0 (IntervalRat.scale (399 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-51055784964 / 1000000000000) (-51055783142 / 1000000000000), orderedInterval (12634971300 / 1000000000000) (12634973121 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1578922044895293 / 4000000000000) 0 (IntervalRat.scale (399 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-12826424688 / 1000000000000) (-12826424594 / 1000000000000), orderedInterval (38072518710 / 1000000000000) (38072518805 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1163026831989687 / 4000000000000) 0 (IntervalRat.scale (399 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (27432708954 / 1000000000000) (27432715659 / 1000000000000), orderedInterval (-37954626657 / 1000000000000) (-37954619953 / 1000000000000)))) (orderedInterval (1058612698 / 1000000000000) (1058612875 / 1000000000000))) = true
  rfl'

theorem compactCertificate327_chunkChecks0_1 :
    compactCertificate327.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1784382246044601 / 4000000000000) 0 (IntervalRat.scale (399 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (26420197519 / 1000000000000) (26420197520 / 1000000000000), orderedInterval (26971609547 / 1000000000000) (26971609548 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1030213570090929 / 4000000000000) 0 (IntervalRat.scale (399 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (33069831827 / 1000000000000) (33069831828 / 1000000000000), orderedInterval (37059701329 / 1000000000000) (37059701330 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1828132058647461 / 4000000000000) 0 (IntervalRat.scale (399 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-28147197492 / 1000000000000) (-28147170294 / 1000000000000), orderedInterval (24539478938 / 1000000000000) (24539506136 / 1000000000000)))) (orderedInterval (-6245637702 / 1000000000000) (-6245633755 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1708078108242009 / 4000000000000) 0 (IntervalRat.scale (399 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (20116875773 / 1000000000000) (20116875774 / 1000000000000), orderedInterval (32933332258 / 1000000000000) (32933332259 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1218965134857897 / 4000000000000) 0 (IntervalRat.scale (399 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-32524823708 / 1000000000000) (-32524823707 / 1000000000000), orderedInterval (-32058717114 / 1000000000000) (-32058717113 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1382176544439663 / 4000000000000) 0 (IntervalRat.scale (399 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (29382630036 / 1000000000000) (29382630037 / 1000000000000), orderedInterval (31246939999 / 1000000000000) (31246940000 / 1000000000000)))) (orderedInterval (-3587505279 / 1000000000000) (-3587505254 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1152314703605247 / 4000000000000) 0 (IntervalRat.scale (399 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-7623254830 / 1000000000000) (-7623254811 / 1000000000000), orderedInterval (46400414342 / 1000000000000) (46400414361 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1018104986834187 / 4000000000000) 0 (IntervalRat.scale (399 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-37312661526 / 1000000000000) (-37312661525 / 1000000000000), orderedInterval (-33227749011 / 1000000000000) (-33227749010 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (295086507732513 / 800000000000) 0 (IntervalRat.scale (399 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-36337161530 / 1000000000000) (-36337109884 / 1000000000000), orderedInterval (20187055998 / 1000000000000) (20187107645 / 1000000000000)))) (orderedInterval (1116873921 / 1000000000000) (1116875264 / 1000000000000))) = true
  rfl'

theorem compactCertificate327_chunkChecks0_2 :
    compactCertificate327.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (816224809940211 / 4000000000000) 0 (IntervalRat.scale (399 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-33242888206 / 1000000000000) (-33242888205 / 1000000000000), orderedInterval (-44804386613 / 1000000000000) (-44804386612 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (691922810828571 / 4000000000000) 0 (IntervalRat.scale (399 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-50307305563 / 1000000000000) (-50307305562 / 1000000000000), orderedInterval (-33758317046 / 1000000000000) (-33758317045 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (432973168010313 / 4000000000000) 0 (IntervalRat.scale (399 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (61393711819 / 1000000000000) (61393765858 / 1000000000000), orderedInterval (-46241956218 / 1000000000000) (-46241902180 / 1000000000000)))) (orderedInterval (10161366756 / 1000000000000) (10161368566 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (232854409759671 / 4000000000000) 0 (IntervalRat.scale (399 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (66838993099 / 1000000000000) (66839032049 / 1000000000000), orderedInterval (-81001344519 / 1000000000000) (-81001305570 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (632245019132013 / 4000000000000) 0 (IntervalRat.scale (399 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (62255707901 / 1000000000000) (62255708597 / 1000000000000), orderedInterval (-12521126995 / 1000000000000) (-12521126298 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (863276521335501 / 4000000000000) 0 (IntervalRat.scale (399 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (8971404582 / 1000000000000) (8971404616 / 1000000000000), orderedInterval (-53586680075 / 1000000000000) (-53586680040 / 1000000000000)))) (orderedInterval (-3334135541 / 1000000000000) (-3334134779 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (365026831989687 / 4000000000000) 0 (IntervalRat.scale (399 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-67179919730 / 1000000000000) (-67179919729 / 1000000000000), orderedInterval (-49260245718 / 1000000000000) (-49260245717 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1483813806354327 / 4000000000000) 0 (IntervalRat.scale (399 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (35527409630 / 1000000000000) (35527409631 / 1000000000000), orderedInterval (21258779428 / 1000000000000) (21258779429 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (991118856683193 / 4000000000000) 0 (IntervalRat.scale (399 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-18744230708 / 1000000000000) (-18744230707 / 1000000000000), orderedInterval (-47057345408 / 1000000000000) (-47057345407 / 1000000000000)))) (orderedInterval (219938014 / 1000000000000) (219938070 / 1000000000000))) = true
  rfl'

theorem compactCertificate327_chunkChecks0 :
    compactCertificate327.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate327.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate327_chunkChecks0_0
    compactCertificate327_chunkChecks0_1 compactCertificate327_chunkChecks0_2

theorem compactCertificate327_chunkChecks1_0 :
    compactCertificate327.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (399 / 2) 1 (IntervalRat.scale (399 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-39613658321 / 1000000000000) (-39613614332 / 1000000000000), orderedInterval (40371289657 / 1000000000000) (40371333646 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (587803188212499 / 4000000000000) 1 (IntervalRat.scale (399 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-5292064693 / 1000000000000) (-5292064691 / 1000000000000), orderedInterval (-65588514977 / 1000000000000) (-65588514975 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (190083473889267 / 800000000000) 1 (IntervalRat.scale (399 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-18806145617 / 1000000000000) (-18806145110 / 1000000000000), orderedInterval (48264675839 / 1000000000000) (48264676346 / 1000000000000)))) (orderedInterval (18924769092 / 1000000000000) (18924786579 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (171519504318393 / 4000000000000) 1 (IntervalRat.scale (399 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-38320291530 / 1000000000000) (-38320290655 / 1000000000000), orderedInterval (116114184624 / 1000000000000) (116114185500 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (460725514813221 / 4000000000000) 1 (IntervalRat.scale (399 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (20061720058 / 1000000000000) (20061720374 / 1000000000000), orderedInterval (-71673946481 / 1000000000000) (-71673946164 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1250959396594257 / 4000000000000) 1 (IntervalRat.scale (399 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-26741729397 / 1000000000000) (-26741722906 / 1000000000000), orderedInterval (36381459173 / 1000000000000) (36381465664 / 1000000000000)))) (orderedInterval (-5836061768 / 1000000000000) (-5836061008 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (921451029626841 / 4000000000000) 1 (IntervalRat.scale (399 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-51055784964 / 1000000000000) (-51055783142 / 1000000000000), orderedInterval (12634971300 / 1000000000000) (12634973121 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1578922044895293 / 4000000000000) 1 (IntervalRat.scale (399 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-12826424688 / 1000000000000) (-12826424594 / 1000000000000), orderedInterval (38072518710 / 1000000000000) (38072518805 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1163026831989687 / 4000000000000) 1 (IntervalRat.scale (399 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (27432708954 / 1000000000000) (27432715659 / 1000000000000), orderedInterval (-37954626657 / 1000000000000) (-37954619953 / 1000000000000)))) (orderedInterval (-3660367347 / 1000000000000) (-3660367085 / 1000000000000))) = true
  rfl'

theorem compactCertificate327_chunkChecks1_1 :
    compactCertificate327.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1784382246044601 / 4000000000000) 1 (IntervalRat.scale (399 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (26420197519 / 1000000000000) (26420197520 / 1000000000000), orderedInterval (26971609547 / 1000000000000) (26971609548 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1030213570090929 / 4000000000000) 1 (IntervalRat.scale (399 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (33069831827 / 1000000000000) (33069831828 / 1000000000000), orderedInterval (37059701329 / 1000000000000) (37059701330 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1828132058647461 / 4000000000000) 1 (IntervalRat.scale (399 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-28147197492 / 1000000000000) (-28147170294 / 1000000000000), orderedInterval (24539478938 / 1000000000000) (24539506136 / 1000000000000)))) (orderedInterval (820036361 / 1000000000000) (820045383 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1708078108242009 / 4000000000000) 1 (IntervalRat.scale (399 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (20116875773 / 1000000000000) (20116875774 / 1000000000000), orderedInterval (32933332258 / 1000000000000) (32933332259 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1218965134857897 / 4000000000000) 1 (IntervalRat.scale (399 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-32524823708 / 1000000000000) (-32524823707 / 1000000000000), orderedInterval (-32058717114 / 1000000000000) (-32058717113 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1382176544439663 / 4000000000000) 1 (IntervalRat.scale (399 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (29382630036 / 1000000000000) (29382630037 / 1000000000000), orderedInterval (31246939999 / 1000000000000) (31246940000 / 1000000000000)))) (orderedInterval (-6177275797 / 1000000000000) (-6177275758 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1152314703605247 / 4000000000000) 1 (IntervalRat.scale (399 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-7623254830 / 1000000000000) (-7623254811 / 1000000000000), orderedInterval (46400414342 / 1000000000000) (46400414361 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1018104986834187 / 4000000000000) 1 (IntervalRat.scale (399 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-37312661526 / 1000000000000) (-37312661525 / 1000000000000), orderedInterval (-33227749011 / 1000000000000) (-33227749010 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (295086507732513 / 800000000000) 1 (IntervalRat.scale (399 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-36337161530 / 1000000000000) (-36337109884 / 1000000000000), orderedInterval (20187055998 / 1000000000000) (20187107645 / 1000000000000)))) (orderedInterval (4155356358 / 1000000000000) (4155358832 / 1000000000000))) = true
  rfl'

theorem compactCertificate327_chunkChecks1_2 :
    compactCertificate327.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (816224809940211 / 4000000000000) 1 (IntervalRat.scale (399 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-33242888206 / 1000000000000) (-33242888205 / 1000000000000), orderedInterval (-44804386613 / 1000000000000) (-44804386612 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (691922810828571 / 4000000000000) 1 (IntervalRat.scale (399 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-50307305563 / 1000000000000) (-50307305562 / 1000000000000), orderedInterval (-33758317046 / 1000000000000) (-33758317045 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (432973168010313 / 4000000000000) 1 (IntervalRat.scale (399 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (61393711819 / 1000000000000) (61393765858 / 1000000000000), orderedInterval (-46241956218 / 1000000000000) (-46241902180 / 1000000000000)))) (orderedInterval (8167422149 / 1000000000000) (8167423151 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (232854409759671 / 4000000000000) 1 (IntervalRat.scale (399 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (66838993099 / 1000000000000) (66839032049 / 1000000000000), orderedInterval (-81001344519 / 1000000000000) (-81001305570 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (632245019132013 / 4000000000000) 1 (IntervalRat.scale (399 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (62255707901 / 1000000000000) (62255708597 / 1000000000000), orderedInterval (-12521126995 / 1000000000000) (-12521126298 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (863276521335501 / 4000000000000) 1 (IntervalRat.scale (399 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (8971404582 / 1000000000000) (8971404616 / 1000000000000), orderedInterval (-53586680075 / 1000000000000) (-53586680040 / 1000000000000)))) (orderedInterval (5104263480 / 1000000000000) (5104263727 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (365026831989687 / 4000000000000) 1 (IntervalRat.scale (399 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-67179919730 / 1000000000000) (-67179919729 / 1000000000000), orderedInterval (-49260245718 / 1000000000000) (-49260245717 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1483813806354327 / 4000000000000) 1 (IntervalRat.scale (399 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (35527409630 / 1000000000000) (35527409631 / 1000000000000), orderedInterval (21258779428 / 1000000000000) (21258779429 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (991118856683193 / 4000000000000) 1 (IntervalRat.scale (399 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-18744230708 / 1000000000000) (-18744230707 / 1000000000000), orderedInterval (-47057345408 / 1000000000000) (-47057345407 / 1000000000000)))) (orderedInterval (7612346092 / 1000000000000) (7612346171 / 1000000000000))) = true
  rfl'

theorem compactCertificate327_chunkChecks1 :
    compactCertificate327.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate327.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate327_chunkChecks1_0
    compactCertificate327_chunkChecks1_1 compactCertificate327_chunkChecks1_2

theorem compactCertificate327_chunkChecks2_0 :
    compactCertificate327.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (399 / 2) 2 (IntervalRat.scale (399 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-39613658321 / 1000000000000) (-39613614332 / 1000000000000), orderedInterval (40371289657 / 1000000000000) (40371333646 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (587803188212499 / 4000000000000) 2 (IntervalRat.scale (399 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-5292064693 / 1000000000000) (-5292064691 / 1000000000000), orderedInterval (-65588514977 / 1000000000000) (-65588514975 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (190083473889267 / 800000000000) 2 (IntervalRat.scale (399 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-18806145617 / 1000000000000) (-18806145110 / 1000000000000), orderedInterval (48264675839 / 1000000000000) (48264676346 / 1000000000000)))) (orderedInterval (17198729480 / 1000000000000) (17198747064 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (171519504318393 / 4000000000000) 2 (IntervalRat.scale (399 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-38320291530 / 1000000000000) (-38320290655 / 1000000000000), orderedInterval (116114184624 / 1000000000000) (116114185500 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (460725514813221 / 4000000000000) 2 (IntervalRat.scale (399 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (20061720058 / 1000000000000) (20061720374 / 1000000000000), orderedInterval (-71673946481 / 1000000000000) (-71673946164 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1250959396594257 / 4000000000000) 2 (IntervalRat.scale (399 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-26741729397 / 1000000000000) (-26741722906 / 1000000000000), orderedInterval (36381459173 / 1000000000000) (36381465664 / 1000000000000)))) (orderedInterval (-4905832270 / 1000000000000) (-4905831090 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (921451029626841 / 4000000000000) 2 (IntervalRat.scale (399 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-51055784964 / 1000000000000) (-51055783142 / 1000000000000), orderedInterval (12634971300 / 1000000000000) (12634973121 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1578922044895293 / 4000000000000) 2 (IntervalRat.scale (399 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-12826424688 / 1000000000000) (-12826424594 / 1000000000000), orderedInterval (38072518710 / 1000000000000) (38072518805 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1163026831989687 / 4000000000000) 2 (IntervalRat.scale (399 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (27432708954 / 1000000000000) (27432715659 / 1000000000000), orderedInterval (-37954626657 / 1000000000000) (-37954619953 / 1000000000000)))) (orderedInterval (-2938702839 / 1000000000000) (-2938702447 / 1000000000000))) = true
  rfl'

theorem compactCertificate327_chunkChecks2_1 :
    compactCertificate327.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1784382246044601 / 4000000000000) 2 (IntervalRat.scale (399 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (26420197519 / 1000000000000) (26420197520 / 1000000000000), orderedInterval (26971609547 / 1000000000000) (26971609548 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1030213570090929 / 4000000000000) 2 (IntervalRat.scale (399 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (33069831827 / 1000000000000) (33069831828 / 1000000000000), orderedInterval (37059701329 / 1000000000000) (37059701330 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1828132058647461 / 4000000000000) 2 (IntervalRat.scale (399 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-28147197492 / 1000000000000) (-28147170294 / 1000000000000), orderedInterval (24539478938 / 1000000000000) (24539506136 / 1000000000000)))) (orderedInterval (40384469043 / 1000000000000) (40384489732 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1708078108242009 / 4000000000000) 2 (IntervalRat.scale (399 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (20116875773 / 1000000000000) (20116875774 / 1000000000000), orderedInterval (32933332258 / 1000000000000) (32933332259 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1218965134857897 / 4000000000000) 2 (IntervalRat.scale (399 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-32524823708 / 1000000000000) (-32524823707 / 1000000000000), orderedInterval (-32058717114 / 1000000000000) (-32058717113 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1382176544439663 / 4000000000000) 2 (IntervalRat.scale (399 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (29382630036 / 1000000000000) (29382630037 / 1000000000000), orderedInterval (31246939999 / 1000000000000) (31246940000 / 1000000000000)))) (orderedInterval (9317416134 / 1000000000000) (9317416199 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1152314703605247 / 4000000000000) 2 (IntervalRat.scale (399 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-7623254830 / 1000000000000) (-7623254811 / 1000000000000), orderedInterval (46400414342 / 1000000000000) (46400414361 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1018104986834187 / 4000000000000) 2 (IntervalRat.scale (399 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-37312661526 / 1000000000000) (-37312661525 / 1000000000000), orderedInterval (-33227749011 / 1000000000000) (-33227749010 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (295086507732513 / 800000000000) 2 (IntervalRat.scale (399 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-36337161530 / 1000000000000) (-36337109884 / 1000000000000), orderedInterval (20187055998 / 1000000000000) (20187107645 / 1000000000000)))) (orderedInterval (-132443770 / 1000000000000) (-132439195 / 1000000000000))) = true
  rfl'

theorem compactCertificate327_chunkChecks2_2 :
    compactCertificate327.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (816224809940211 / 4000000000000) 2 (IntervalRat.scale (399 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-33242888206 / 1000000000000) (-33242888205 / 1000000000000), orderedInterval (-44804386613 / 1000000000000) (-44804386612 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (691922810828571 / 4000000000000) 2 (IntervalRat.scale (399 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-50307305563 / 1000000000000) (-50307305562 / 1000000000000), orderedInterval (-33758317046 / 1000000000000) (-33758317045 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (432973168010313 / 4000000000000) 2 (IntervalRat.scale (399 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (61393711819 / 1000000000000) (61393765858 / 1000000000000), orderedInterval (-46241956218 / 1000000000000) (-46241902180 / 1000000000000)))) (orderedInterval (-8330870041 / 1000000000000) (-8330869473 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (232854409759671 / 4000000000000) 2 (IntervalRat.scale (399 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (66838993099 / 1000000000000) (66839032049 / 1000000000000), orderedInterval (-81001344519 / 1000000000000) (-81001305570 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (632245019132013 / 4000000000000) 2 (IntervalRat.scale (399 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (62255707901 / 1000000000000) (62255708597 / 1000000000000), orderedInterval (-12521126995 / 1000000000000) (-12521126298 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (863276521335501 / 4000000000000) 2 (IntervalRat.scale (399 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (8971404582 / 1000000000000) (8971404616 / 1000000000000), orderedInterval (-53586680075 / 1000000000000) (-53586680040 / 1000000000000)))) (orderedInterval (1770725942 / 1000000000000) (1770726040 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (365026831989687 / 4000000000000) 2 (IntervalRat.scale (399 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-67179919730 / 1000000000000) (-67179919729 / 1000000000000), orderedInterval (-49260245718 / 1000000000000) (-49260245717 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1483813806354327 / 4000000000000) 2 (IntervalRat.scale (399 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (35527409630 / 1000000000000) (35527409631 / 1000000000000), orderedInterval (21258779428 / 1000000000000) (21258779429 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (991118856683193 / 4000000000000) 2 (IntervalRat.scale (399 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-18744230708 / 1000000000000) (-18744230707 / 1000000000000), orderedInterval (-47057345408 / 1000000000000) (-47057345407 / 1000000000000)))) (orderedInterval (4620343000 / 1000000000000) (4620343116 / 1000000000000))) = true
  rfl'

theorem compactCertificate327_chunkChecks2 :
    compactCertificate327.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate327.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate327_chunkChecks2_0
    compactCertificate327_chunkChecks2_1 compactCertificate327_chunkChecks2_2

theorem compactCertificate327_chunkChecks3_0 :
    compactCertificate327.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (399 / 2) 3 (IntervalRat.scale (399 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-39613658321 / 1000000000000) (-39613614332 / 1000000000000), orderedInterval (40371289657 / 1000000000000) (40371333646 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (587803188212499 / 4000000000000) 3 (IntervalRat.scale (399 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-5292064693 / 1000000000000) (-5292064691 / 1000000000000), orderedInterval (-65588514977 / 1000000000000) (-65588514975 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (190083473889267 / 800000000000) 3 (IntervalRat.scale (399 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-18806145617 / 1000000000000) (-18806145110 / 1000000000000), orderedInterval (48264675839 / 1000000000000) (48264676346 / 1000000000000)))) (orderedInterval (-20628048112 / 1000000000000) (-20628030517 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (171519504318393 / 4000000000000) 3 (IntervalRat.scale (399 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-38320291530 / 1000000000000) (-38320290655 / 1000000000000), orderedInterval (116114184624 / 1000000000000) (116114185500 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (460725514813221 / 4000000000000) 3 (IntervalRat.scale (399 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (20061720058 / 1000000000000) (20061720374 / 1000000000000), orderedInterval (-71673946481 / 1000000000000) (-71673946164 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1250959396594257 / 4000000000000) 3 (IntervalRat.scale (399 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-26741729397 / 1000000000000) (-26741722906 / 1000000000000), orderedInterval (36381459173 / 1000000000000) (36381465664 / 1000000000000)))) (orderedInterval (10503979589 / 1000000000000) (10503981432 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (921451029626841 / 4000000000000) 3 (IntervalRat.scale (399 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-51055784964 / 1000000000000) (-51055783142 / 1000000000000), orderedInterval (12634971300 / 1000000000000) (12634973121 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1578922044895293 / 4000000000000) 3 (IntervalRat.scale (399 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-12826424688 / 1000000000000) (-12826424594 / 1000000000000), orderedInterval (38072518710 / 1000000000000) (38072518805 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1163026831989687 / 4000000000000) 3 (IntervalRat.scale (399 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (27432708954 / 1000000000000) (27432715659 / 1000000000000), orderedInterval (-37954626657 / 1000000000000) (-37954619953 / 1000000000000)))) (orderedInterval (11950408632 / 1000000000000) (11950409222 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate327_chunkChecks3_1 :
    compactCertificate327.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1784382246044601 / 4000000000000) 3 (IntervalRat.scale (399 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (26420197519 / 1000000000000) (26420197520 / 1000000000000), orderedInterval (26971609547 / 1000000000000) (26971609548 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1030213570090929 / 4000000000000) 3 (IntervalRat.scale (399 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (33069831827 / 1000000000000) (33069831828 / 1000000000000), orderedInterval (37059701329 / 1000000000000) (37059701330 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1828132058647461 / 4000000000000) 3 (IntervalRat.scale (399 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-28147197492 / 1000000000000) (-28147170294 / 1000000000000), orderedInterval (24539478938 / 1000000000000) (24539506136 / 1000000000000)))) (orderedInterval (5530065398 / 1000000000000) (5530112757 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1708078108242009 / 4000000000000) 3 (IntervalRat.scale (399 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (20116875773 / 1000000000000) (20116875774 / 1000000000000), orderedInterval (32933332258 / 1000000000000) (32933332259 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1218965134857897 / 4000000000000) 3 (IntervalRat.scale (399 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-32524823708 / 1000000000000) (-32524823707 / 1000000000000), orderedInterval (-32058717114 / 1000000000000) (-32058717113 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1382176544439663 / 4000000000000) 3 (IntervalRat.scale (399 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (29382630036 / 1000000000000) (29382630037 / 1000000000000), orderedInterval (31246939999 / 1000000000000) (31246940000 / 1000000000000)))) (orderedInterval (17410418063 / 1000000000000) (17410418172 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1152314703605247 / 4000000000000) 3 (IntervalRat.scale (399 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-7623254830 / 1000000000000) (-7623254811 / 1000000000000), orderedInterval (46400414342 / 1000000000000) (46400414361 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1018104986834187 / 4000000000000) 3 (IntervalRat.scale (399 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-37312661526 / 1000000000000) (-37312661525 / 1000000000000), orderedInterval (-33227749011 / 1000000000000) (-33227749010 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (295086507732513 / 800000000000) 3 (IntervalRat.scale (399 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-36337161530 / 1000000000000) (-36337109884 / 1000000000000), orderedInterval (20187055998 / 1000000000000) (20187107645 / 1000000000000)))) (orderedInterval (-8828242905 / 1000000000000) (-8828234460 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate327_chunkChecks3_2 :
    compactCertificate327.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (816224809940211 / 4000000000000) 3 (IntervalRat.scale (399 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-33242888206 / 1000000000000) (-33242888205 / 1000000000000), orderedInterval (-44804386613 / 1000000000000) (-44804386612 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (691922810828571 / 4000000000000) 3 (IntervalRat.scale (399 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-50307305563 / 1000000000000) (-50307305562 / 1000000000000), orderedInterval (-33758317046 / 1000000000000) (-33758317045 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (432973168010313 / 4000000000000) 3 (IntervalRat.scale (399 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (61393711819 / 1000000000000) (61393765858 / 1000000000000), orderedInterval (-46241956218 / 1000000000000) (-46241902180 / 1000000000000)))) (orderedInterval (-8629138727 / 1000000000000) (-8629138400 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (232854409759671 / 4000000000000) 3 (IntervalRat.scale (399 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (66838993099 / 1000000000000) (66839032049 / 1000000000000), orderedInterval (-81001344519 / 1000000000000) (-81001305570 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (632245019132013 / 4000000000000) 3 (IntervalRat.scale (399 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (62255707901 / 1000000000000) (62255708597 / 1000000000000), orderedInterval (-12521126995 / 1000000000000) (-12521126298 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (863276521335501 / 4000000000000) 3 (IntervalRat.scale (399 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (8971404582 / 1000000000000) (8971404616 / 1000000000000), orderedInterval (-53586680075 / 1000000000000) (-53586680040 / 1000000000000)))) (orderedInterval (-5386509877 / 1000000000000) (-5386509824 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (365026831989687 / 4000000000000) 3 (IntervalRat.scale (399 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-67179919730 / 1000000000000) (-67179919729 / 1000000000000), orderedInterval (-49260245718 / 1000000000000) (-49260245717 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1483813806354327 / 4000000000000) 3 (IntervalRat.scale (399 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (35527409630 / 1000000000000) (35527409631 / 1000000000000), orderedInterval (21258779428 / 1000000000000) (21258779429 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (991118856683193 / 4000000000000) 3 (IntervalRat.scale (399 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-18744230708 / 1000000000000) (-18744230707 / 1000000000000), orderedInterval (-47057345408 / 1000000000000) (-47057345407 / 1000000000000)))) (orderedInterval (-5785210599 / 1000000000000) (-5785210421 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate327_chunkChecks3 :
    compactCertificate327.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate327.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate327_chunkChecks3_0
    compactCertificate327_chunkChecks3_1 compactCertificate327_chunkChecks3_2

theorem compactCertificate327_chunkChecks4_0 :
    compactCertificate327.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (399 / 2) 4 (IntervalRat.scale (399 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-39613658321 / 1000000000000) (-39613614332 / 1000000000000), orderedInterval (40371289657 / 1000000000000) (40371333646 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (587803188212499 / 4000000000000) 4 (IntervalRat.scale (399 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-5292064693 / 1000000000000) (-5292064691 / 1000000000000), orderedInterval (-65588514977 / 1000000000000) (-65588514975 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (190083473889267 / 800000000000) 4 (IntervalRat.scale (399 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-18806145617 / 1000000000000) (-18806145110 / 1000000000000), orderedInterval (48264675839 / 1000000000000) (48264676346 / 1000000000000)))) (orderedInterval (-17729223562 / 1000000000000) (-17729205868 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (171519504318393 / 4000000000000) 4 (IntervalRat.scale (399 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-38320291530 / 1000000000000) (-38320290655 / 1000000000000), orderedInterval (116114184624 / 1000000000000) (116114185500 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (460725514813221 / 4000000000000) 4 (IntervalRat.scale (399 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (20061720058 / 1000000000000) (20061720374 / 1000000000000), orderedInterval (-71673946481 / 1000000000000) (-71673946164 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1250959396594257 / 4000000000000) 4 (IntervalRat.scale (399 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-26741729397 / 1000000000000) (-26741722906 / 1000000000000), orderedInterval (36381459173 / 1000000000000) (36381465664 / 1000000000000)))) (orderedInterval (11457248598 / 1000000000000) (11457251491 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (921451029626841 / 4000000000000) 4 (IntervalRat.scale (399 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-51055784964 / 1000000000000) (-51055783142 / 1000000000000), orderedInterval (12634971300 / 1000000000000) (12634973121 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1578922044895293 / 4000000000000) 4 (IntervalRat.scale (399 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-12826424688 / 1000000000000) (-12826424594 / 1000000000000), orderedInterval (38072518710 / 1000000000000) (38072518805 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1163026831989687 / 4000000000000) 4 (IntervalRat.scale (399 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (27432708954 / 1000000000000) (27432715659 / 1000000000000), orderedInterval (-37954626657 / 1000000000000) (-37954619953 / 1000000000000)))) (orderedInterval (8934682721 / 1000000000000) (8934683619 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate327_chunkChecks4_1 :
    compactCertificate327.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1784382246044601 / 4000000000000) 4 (IntervalRat.scale (399 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (26420197519 / 1000000000000) (26420197520 / 1000000000000), orderedInterval (26971609547 / 1000000000000) (26971609548 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1030213570090929 / 4000000000000) 4 (IntervalRat.scale (399 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (33069831827 / 1000000000000) (33069831828 / 1000000000000), orderedInterval (37059701329 / 1000000000000) (37059701330 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1828132058647461 / 4000000000000) 4 (IntervalRat.scale (399 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-28147197492 / 1000000000000) (-28147170294 / 1000000000000), orderedInterval (24539478938 / 1000000000000) (24539506136 / 1000000000000)))) (orderedInterval (-220821481106 / 1000000000000) (-220821372434 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1708078108242009 / 4000000000000) 4 (IntervalRat.scale (399 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (20116875773 / 1000000000000) (20116875774 / 1000000000000), orderedInterval (32933332258 / 1000000000000) (32933332259 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1218965134857897 / 4000000000000) 4 (IntervalRat.scale (399 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-32524823708 / 1000000000000) (-32524823707 / 1000000000000), orderedInterval (-32058717114 / 1000000000000) (-32058717113 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1382176544439663 / 4000000000000) 4 (IntervalRat.scale (399 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (29382630036 / 1000000000000) (29382630037 / 1000000000000), orderedInterval (31246939999 / 1000000000000) (31246940000 / 1000000000000)))) (orderedInterval (-25880792011 / 1000000000000) (-25880791821 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1152314703605247 / 4000000000000) 4 (IntervalRat.scale (399 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-7623254830 / 1000000000000) (-7623254811 / 1000000000000), orderedInterval (46400414342 / 1000000000000) (46400414361 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1018104986834187 / 4000000000000) 4 (IntervalRat.scale (399 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-37312661526 / 1000000000000) (-37312661525 / 1000000000000), orderedInterval (-33227749011 / 1000000000000) (-33227749010 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (295086507732513 / 800000000000) 4 (IntervalRat.scale (399 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-36337161530 / 1000000000000) (-36337109884 / 1000000000000), orderedInterval (20187055998 / 1000000000000) (20187107645 / 1000000000000)))) (orderedInterval (-5509248613 / 1000000000000) (-5509232975 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate327_chunkChecks4_2 :
    compactCertificate327.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (816224809940211 / 4000000000000) 4 (IntervalRat.scale (399 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-33242888206 / 1000000000000) (-33242888205 / 1000000000000), orderedInterval (-44804386613 / 1000000000000) (-44804386612 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (691922810828571 / 4000000000000) 4 (IntervalRat.scale (399 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-50307305563 / 1000000000000) (-50307305562 / 1000000000000), orderedInterval (-33758317046 / 1000000000000) (-33758317045 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (432973168010313 / 4000000000000) 4 (IntervalRat.scale (399 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (61393711819 / 1000000000000) (61393765858 / 1000000000000), orderedInterval (-46241956218 / 1000000000000) (-46241902180 / 1000000000000)))) (orderedInterval (7686656897 / 1000000000000) (7686657096 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (232854409759671 / 4000000000000) 4 (IntervalRat.scale (399 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (66838993099 / 1000000000000) (66839032049 / 1000000000000), orderedInterval (-81001344519 / 1000000000000) (-81001305570 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (632245019132013 / 4000000000000) 4 (IntervalRat.scale (399 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (62255707901 / 1000000000000) (62255708597 / 1000000000000), orderedInterval (-12521126995 / 1000000000000) (-12521126298 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (863276521335501 / 4000000000000) 4 (IntervalRat.scale (399 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (8971404582 / 1000000000000) (8971404616 / 1000000000000), orderedInterval (-53586680075 / 1000000000000) (-53586680040 / 1000000000000)))) (orderedInterval (-1453095200 / 1000000000000) (-1453095161 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (365026831989687 / 4000000000000) 4 (IntervalRat.scale (399 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-67179919730 / 1000000000000) (-67179919729 / 1000000000000), orderedInterval (-49260245718 / 1000000000000) (-49260245717 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1483813806354327 / 4000000000000) 4 (IntervalRat.scale (399 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (35527409630 / 1000000000000) (35527409631 / 1000000000000), orderedInterval (21258779428 / 1000000000000) (21258779429 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (991118856683193 / 4000000000000) 4 (IntervalRat.scale (399 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-18744230708 / 1000000000000) (-18744230707 / 1000000000000), orderedInterval (-47057345408 / 1000000000000) (-47057345407 / 1000000000000)))) (orderedInterval (-26161337593 / 1000000000000) (-26161337307 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate327_chunkChecks4 :
    compactCertificate327.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate327.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate327_chunkChecks4_0
    compactCertificate327_chunkChecks4_1 compactCertificate327_chunkChecks4_2

theorem compactCertificate327_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate327.chunkCheck r b = true :=
  compactCertificate327.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate327_chunkChecks0
    · exact compactCertificate327_chunkChecks1
    · exact compactCertificate327_chunkChecks2
    · exact compactCertificate327_chunkChecks3
    · exact compactCertificate327_chunkChecks4)

theorem compactCertificate327_coefficient0 :
    compactCertificate327.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate327_coefficient1 :
    compactCertificate327.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate327_coefficient2 :
    compactCertificate327.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate327_coefficient3 :
    compactCertificate327.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate327_coefficient4 :
    compactCertificate327.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate327_coefficients : ∀ r : Fin 5,
    compactCertificate327.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate327_coefficient0
  · exact compactCertificate327_coefficient1
  · exact compactCertificate327_coefficient2
  · exact compactCertificate327_coefficient3
  · exact compactCertificate327_coefficient4

theorem compactCertificate327_lower : (1 : ℚ) ≤ compactCertificate327.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate327, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate327_proves {t : ℝ} (ht : t ∈ compactCertificate327.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate327.proves compactCertificate327_states compactCertificate327_chunks
    compactCertificate327_coefficients compactCertificate327_lower ht

end Erdos232
