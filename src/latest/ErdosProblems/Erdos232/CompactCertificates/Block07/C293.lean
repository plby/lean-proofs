/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate293 : CompactCertificate where
  left := 333 / 2
  right := 167
  center := 667 / 4
  grid := fun i =>
    match i.val with
    | 0 => 53
    | 1 => 39
    | 2 => 63
    | 3 => 11
    | 4 => 31
    | 5 => 83
    | 6 => 61
    | 7 => 105
    | 8 => 77
    | 9 => 119
    | 10 => 69
    | 11 => 122
    | 12 => 114
    | 13 => 81
    | 14 => 92
    | 15 => 77
    | 16 => 68
    | 17 => 98
    | 18 => 54
    | 19 => 46
    | 20 => 29
    | 21 => 15
    | 22 => 42
    | 23 => 57
    | 24 => 24
    | 25 => 99
    | _ => 66
  point := fun i =>
    match i.val with
    | 0 => 667 / 4
    | 1 => 982618362249967 / 8000000000000
    | 2 => 317758589183311 / 1600000000000
    | 3 => 286725587419469 / 8000000000000
    | 4 => 770185259098793 / 8000000000000
    | 5 => 2091202800822981 / 8000000000000
    | 6 => 1540370518198253 / 8000000000000
    | 7 => 2639451137707169 / 8000000000000
    | 8 => 1944207761747171 / 8000000000000
    | 9 => 2982914681984333 / 8000000000000
    | 10 => 1722186594613157 / 8000000000000
    | 11 => 3056050333628713 / 8000000000000
    | 12 => 2855358642098797 / 8000000000000
    | 13 => 2037718659023101 / 8000000000000
    | 14 => 2310555777296379 / 8000000000000
    | 15 => 1926300519560651 / 8000000000000
    | 16 => 1701944927865671 / 8000000000000
    | 17 => 493289976585429 / 1600000000000
    | 18 => 1364466035664463 / 8000000000000
    | 19 => 1156672969480343 / 8000000000000
    | 20 => 723792238252829 / 8000000000000
    | 21 => 389257872956643 / 8000000000000
    | 22 => 1056910846518929 / 8000000000000
    | 23 => 1443121402834033 / 8000000000000
    | 24 => 610207761747171 / 8000000000000
    | 25 => 2480460673780291 / 8000000000000
    | _ => 1656832775457869 / 8000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-52978603506 / 1000000000000) (-52978603505 / 1000000000000), orderedInterval (-31638459838 / 1000000000000) (-31638459837 / 1000000000000))
    | 1 => (orderedInterval (-63816432193 / 1000000000000) (-63816432192 / 1000000000000), orderedInterval (-33064185778 / 1000000000000) (-33064185777 / 1000000000000))
    | 2 => (orderedInterval (-56292213502 / 1000000000000) (-56292213488 / 1000000000000), orderedInterval (-5918692796 / 1000000000000) (-5918692783 / 1000000000000))
    | 3 => (orderedInterval (-117317596167 / 1000000000000) (-117317586370 / 1000000000000), orderedInterval (64866986260 / 1000000000000) (64866996056 / 1000000000000))
    | 4 => (orderedInterval (26513049051 / 1000000000000) (26513049797 / 1000000000000), orderedInterval (-77012714567 / 1000000000000) (-77012713822 / 1000000000000))
    | 5 => (orderedInterval (-48882692482 / 1000000000000) (-48882692468 / 1000000000000), orderedInterval (-6681348808 / 1000000000000) (-6681348794 / 1000000000000))
    | 6 => (orderedInterval (-57065283637 / 1000000000000) (-57065283288 / 1000000000000), orderedInterval (7209546024 / 1000000000000) (7209546373 / 1000000000000))
    | 7 => (orderedInterval (-32977524598 / 1000000000000) (-32977524597 / 1000000000000), orderedInterval (-28967855767 / 1000000000000) (-28967855766 / 1000000000000))
    | 8 => (orderedInterval (-48295446739 / 1000000000000) (-48295441136 / 1000000000000), orderedInterval (17043392272 / 1000000000000) (17043397875 / 1000000000000))
    | 9 => (orderedInterval (8214262427 / 1000000000000) (8214262445 / 1000000000000), orderedInterval (-40506739813 / 1000000000000) (-40506739795 / 1000000000000))
    | 10 => (orderedInterval (35519298048 / 1000000000000) (35519320562 / 1000000000000), orderedInterval (-41260688556 / 1000000000000) (-41260666043 / 1000000000000))
    | 11 => (orderedInterval (-18957613164 / 1000000000000) (-18957612354 / 1000000000000), orderedInterval (36179012911 / 1000000000000) (36179013721 / 1000000000000))
    | 12 => (orderedInterval (-17862014912 / 1000000000000) (-17862014375 / 1000000000000), orderedInterval (38295098736 / 1000000000000) (38295099273 / 1000000000000))
    | 13 => (orderedInterval (-42878178565 / 1000000000000) (-42878178564 / 1000000000000), orderedInterval (-25621914031 / 1000000000000) (-25621914030 / 1000000000000))
    | 14 => (orderedInterval (25647186012 / 1000000000000) (25647186013 / 1000000000000), orderedInterval (39280358923 / 1000000000000) (39280358924 / 1000000000000))
    | 15 => (orderedInterval (16671186476 / 1000000000000) (16671186768 / 1000000000000), orderedInterval (-48675983038 / 1000000000000) (-48675982746 / 1000000000000))
    | 16 => (orderedInterval (-5481542832 / 1000000000000) (-5481542819 / 1000000000000), orderedInterval (54440770720 / 1000000000000) (54440770733 / 1000000000000))
    | 17 => (orderedInterval (42597418275 / 1000000000000) (42597418277 / 1000000000000), orderedInterval (15753437506 / 1000000000000) (15753437507 / 1000000000000))
    | 18 => (orderedInterval (60609339884 / 1000000000000) (60609340199 / 1000000000000), orderedInterval (-7862557635 / 1000000000000) (-7862557320 / 1000000000000))
    | 19 => (orderedInterval (50087205927 / 1000000000000) (50087205928 / 1000000000000), orderedInterval (43351243767 / 1000000000000) (43351243768 / 1000000000000))
    | 20 => (orderedInterval (-12689547397 / 1000000000000) (-12689547395 / 1000000000000), orderedInterval (-82848929389 / 1000000000000) (-82848929388 / 1000000000000))
    | 21 => (orderedInterval (-84051034333 / 1000000000000) (-84050932625 / 1000000000000), orderedInterval (78446678473 / 1000000000000) (78446780181 / 1000000000000))
    | 22 => (orderedInterval (56521802312 / 1000000000000) (56521802313 / 1000000000000), orderedInterval (40084915127 / 1000000000000) (40084915128 / 1000000000000))
    | 23 => (orderedInterval (-51156747630 / 1000000000000) (-51156719620 / 1000000000000), orderedInterval (30342915253 / 1000000000000) (30342943264 / 1000000000000))
    | 24 => (orderedInterval (90981339865 / 1000000000000) (90981339969 / 1000000000000), orderedInterval (-8872151117 / 1000000000000) (-8872151013 / 1000000000000))
    | 25 => (orderedInterval (7893455995 / 1000000000000) (7893456014 / 1000000000000), orderedInterval (-44632529864 / 1000000000000) (-44632529845 / 1000000000000))
    | _ => (orderedInterval (28684512837 / 1000000000000) (28684512838 / 1000000000000), orderedInterval (47376664520 / 1000000000000) (47376664521 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-24896800420 / 1000000000000) (-24896800406 / 1000000000000)
      | 1 => orderedInterval (5715903395 / 1000000000000) (5715903550 / 1000000000000)
      | 2 => orderedInterval (-150046864 / 1000000000000) (-150046719 / 1000000000000)
      | 3 => orderedInterval (-1522824003 / 1000000000000) (-1522822150 / 1000000000000)
      | 4 => orderedInterval (-3862008517 / 1000000000000) (-3862008486 / 1000000000000)
      | 5 => orderedInterval (1596866000 / 1000000000000) (1596866020 / 1000000000000)
      | 6 => orderedInterval (-12939020740 / 1000000000000) (-12939020647 / 1000000000000)
      | 7 => orderedInterval (4190301150 / 1000000000000) (4190305195 / 1000000000000)
      | _ => orderedInterval (-5476051534 / 1000000000000) (-5476051484 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-13180971268 / 1000000000000) (-13180971253 / 1000000000000)
      | 1 => orderedInterval (-1030118204 / 1000000000000) (-1030118140 / 1000000000000)
      | 2 => orderedInterval (2368169473 / 1000000000000) (2368169688 / 1000000000000)
      | 3 => orderedInterval (23929756364 / 1000000000000) (23929758925 / 1000000000000)
      | 4 => orderedInterval (-5525099987 / 1000000000000) (-5525099933 / 1000000000000)
      | 5 => orderedInterval (-4040680707 / 1000000000000) (-4040680678 / 1000000000000)
      | 6 => orderedInterval (-2305050200 / 1000000000000) (-2305050109 / 1000000000000)
      | 7 => orderedInterval (-3658854641 / 1000000000000) (-3658851752 / 1000000000000)
      | _ => orderedInterval (-4309214260 / 1000000000000) (-4309214191 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (26086198221 / 1000000000000) (26086198239 / 1000000000000)
      | 1 => orderedInterval (-8914992374 / 1000000000000) (-8914992325 / 1000000000000)
      | 2 => orderedInterval (-1516976365 / 1000000000000) (-1516976046 / 1000000000000)
      | 3 => orderedInterval (16911751488 / 1000000000000) (16911755197 / 1000000000000)
      | 4 => orderedInterval (8406052866 / 1000000000000) (8406052965 / 1000000000000)
      | 5 => orderedInterval (-4616192177 / 1000000000000) (-4616192133 / 1000000000000)
      | 6 => orderedInterval (12405452855 / 1000000000000) (12405452946 / 1000000000000)
      | 7 => orderedInterval (-3893519705 / 1000000000000) (-3893516997 / 1000000000000)
      | _ => orderedInterval (10434711076 / 1000000000000) (10434711179 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (13093354411 / 1000000000000) (13093354431 / 1000000000000)
      | 1 => orderedInterval (-1228190051 / 1000000000000) (-1228189993 / 1000000000000)
      | 2 => orderedInterval (-8186823802 / 1000000000000) (-8186823327 / 1000000000000)
      | 3 => orderedInterval (-135829107993 / 1000000000000) (-135829102320 / 1000000000000)
      | 4 => orderedInterval (16397663620 / 1000000000000) (16397663807 / 1000000000000)
      | 5 => orderedInterval (5640430842 / 1000000000000) (5640430907 / 1000000000000)
      | 6 => orderedInterval (610540413 / 1000000000000) (610540504 / 1000000000000)
      | 7 => orderedInterval (3455548161 / 1000000000000) (3455550961 / 1000000000000)
      | _ => orderedInterval (-6384004115 / 1000000000000) (-6384003956 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-27976515633 / 1000000000000) (-27976515610 / 1000000000000)
      | 1 => orderedInterval (21110351393 / 1000000000000) (21110351476 / 1000000000000)
      | 2 => orderedInterval (10421029847 / 1000000000000) (10421030562 / 1000000000000)
      | 3 => orderedInterval (-101777307844 / 1000000000000) (-101777298470 / 1000000000000)
      | 4 => orderedInterval (-16671337769 / 1000000000000) (-16671337406 / 1000000000000)
      | 5 => orderedInterval (14345789836 / 1000000000000) (14345789938 / 1000000000000)
      | 6 => orderedInterval (-12252105965 / 1000000000000) (-12252105873 / 1000000000000)
      | 7 => orderedInterval (4833975356 / 1000000000000) (4833978363 / 1000000000000)
      | _ => orderedInterval (-20386432131 / 1000000000000) (-20386431874 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-37343681533 / 1000000000000) (-37343675127 / 1000000000000)
    | 1 => orderedInterval (-7752063430 / 1000000000000) (-7752057443 / 1000000000000)
    | 2 => orderedInterval (55302485885 / 1000000000000) (55302493025 / 1000000000000)
    | 3 => orderedInterval (-112430588514 / 1000000000000) (-112430578986 / 1000000000000)
    | _ => orderedInterval (-128352552910 / 1000000000000) (-128352538894 / 1000000000000)

theorem compactCertificate293_stateChecks0 :
    compactCertificate293.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 53 12 (667 / 4)) (orderedInterval (-52978603506 / 1000000000000) (-52978603505 / 1000000000000), orderedInterval (-31638459838 / 1000000000000) (-31638459837 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 39 12 (982618362249967 / 8000000000000)) (orderedInterval (-63816432193 / 1000000000000) (-63816432192 / 1000000000000), orderedInterval (-33064185778 / 1000000000000) (-33064185777 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (317758589183311 / 1600000000000)) (orderedInterval (-56292213502 / 1000000000000) (-56292213488 / 1000000000000), orderedInterval (-5918692796 / 1000000000000) (-5918692783 / 1000000000000))) = true
  rfl'

theorem compactCertificate293_stateChecks1 :
    compactCertificate293.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 11 12 (286725587419469 / 8000000000000)) (orderedInterval (-117317596167 / 1000000000000) (-117317586370 / 1000000000000), orderedInterval (64866986260 / 1000000000000) (64866996056 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 31 12 (770185259098793 / 8000000000000)) (orderedInterval (26513049051 / 1000000000000) (26513049797 / 1000000000000), orderedInterval (-77012714567 / 1000000000000) (-77012713822 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 83 12 (2091202800822981 / 8000000000000)) (orderedInterval (-48882692482 / 1000000000000) (-48882692468 / 1000000000000), orderedInterval (-6681348808 / 1000000000000) (-6681348794 / 1000000000000))) = true
  rfl'

theorem compactCertificate293_stateChecks2 :
    compactCertificate293.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 61 12 (1540370518198253 / 8000000000000)) (orderedInterval (-57065283637 / 1000000000000) (-57065283288 / 1000000000000), orderedInterval (7209546024 / 1000000000000) (7209546373 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 105 12 (2639451137707169 / 8000000000000)) (orderedInterval (-32977524598 / 1000000000000) (-32977524597 / 1000000000000), orderedInterval (-28967855767 / 1000000000000) (-28967855766 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 77 12 (1944207761747171 / 8000000000000)) (orderedInterval (-48295446739 / 1000000000000) (-48295441136 / 1000000000000), orderedInterval (17043392272 / 1000000000000) (17043397875 / 1000000000000))) = true
  rfl'

theorem compactCertificate293_stateChecks3 :
    compactCertificate293.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 119 12 (2982914681984333 / 8000000000000)) (orderedInterval (8214262427 / 1000000000000) (8214262445 / 1000000000000), orderedInterval (-40506739813 / 1000000000000) (-40506739795 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (1722186594613157 / 8000000000000)) (orderedInterval (35519298048 / 1000000000000) (35519320562 / 1000000000000), orderedInterval (-41260688556 / 1000000000000) (-41260666043 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 122 12 (3056050333628713 / 8000000000000)) (orderedInterval (-18957613164 / 1000000000000) (-18957612354 / 1000000000000), orderedInterval (36179012911 / 1000000000000) (36179013721 / 1000000000000))) = true
  rfl'

theorem compactCertificate293_stateChecks4 :
    compactCertificate293.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 114 12 (2855358642098797 / 8000000000000)) (orderedInterval (-17862014912 / 1000000000000) (-17862014375 / 1000000000000), orderedInterval (38295098736 / 1000000000000) (38295099273 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 81 12 (2037718659023101 / 8000000000000)) (orderedInterval (-42878178565 / 1000000000000) (-42878178564 / 1000000000000), orderedInterval (-25621914031 / 1000000000000) (-25621914030 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 92 12 (2310555777296379 / 8000000000000)) (orderedInterval (25647186012 / 1000000000000) (25647186013 / 1000000000000), orderedInterval (39280358923 / 1000000000000) (39280358924 / 1000000000000))) = true
  rfl'

theorem compactCertificate293_stateChecks5 :
    compactCertificate293.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 77 12 (1926300519560651 / 8000000000000)) (orderedInterval (16671186476 / 1000000000000) (16671186768 / 1000000000000), orderedInterval (-48675983038 / 1000000000000) (-48675982746 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (1701944927865671 / 8000000000000)) (orderedInterval (-5481542832 / 1000000000000) (-5481542819 / 1000000000000), orderedInterval (54440770720 / 1000000000000) (54440770733 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 98 12 (493289976585429 / 1600000000000)) (orderedInterval (42597418275 / 1000000000000) (42597418277 / 1000000000000), orderedInterval (15753437506 / 1000000000000) (15753437507 / 1000000000000))) = true
  rfl'

theorem compactCertificate293_stateChecks6 :
    compactCertificate293.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (1364466035664463 / 8000000000000)) (orderedInterval (60609339884 / 1000000000000) (60609340199 / 1000000000000), orderedInterval (-7862557635 / 1000000000000) (-7862557320 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 46 12 (1156672969480343 / 8000000000000)) (orderedInterval (50087205927 / 1000000000000) (50087205928 / 1000000000000), orderedInterval (43351243767 / 1000000000000) (43351243768 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 29 12 (723792238252829 / 8000000000000)) (orderedInterval (-12689547397 / 1000000000000) (-12689547395 / 1000000000000), orderedInterval (-82848929389 / 1000000000000) (-82848929388 / 1000000000000))) = true
  rfl'

theorem compactCertificate293_stateChecks7 :
    compactCertificate293.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 15 12 (389257872956643 / 8000000000000)) (orderedInterval (-84051034333 / 1000000000000) (-84050932625 / 1000000000000), orderedInterval (78446678473 / 1000000000000) (78446780181 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 42 12 (1056910846518929 / 8000000000000)) (orderedInterval (56521802312 / 1000000000000) (56521802313 / 1000000000000), orderedInterval (40084915127 / 1000000000000) (40084915128 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 57 12 (1443121402834033 / 8000000000000)) (orderedInterval (-51156747630 / 1000000000000) (-51156719620 / 1000000000000), orderedInterval (30342915253 / 1000000000000) (30342943264 / 1000000000000))) = true
  rfl'

theorem compactCertificate293_stateChecks8 :
    compactCertificate293.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 24 12 (610207761747171 / 8000000000000)) (orderedInterval (90981339865 / 1000000000000) (90981339969 / 1000000000000), orderedInterval (-8872151117 / 1000000000000) (-8872151013 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 99 12 (2480460673780291 / 8000000000000)) (orderedInterval (7893455995 / 1000000000000) (7893456014 / 1000000000000), orderedInterval (-44632529864 / 1000000000000) (-44632529845 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (1656832775457869 / 8000000000000)) (orderedInterval (28684512837 / 1000000000000) (28684512838 / 1000000000000), orderedInterval (47376664520 / 1000000000000) (47376664521 / 1000000000000))) = true
  rfl'

theorem compactCertificate293_states : ∀ j,
    BesselStateValid (compactCertificate293.point j) (compactCertificate293.state j) :=
  compactCertificate293.statesValid_of_checks3 compactCertificate293_stateChecks0
    compactCertificate293_stateChecks1 compactCertificate293_stateChecks2
    compactCertificate293_stateChecks3 compactCertificate293_stateChecks4
    compactCertificate293_stateChecks5 compactCertificate293_stateChecks6
    compactCertificate293_stateChecks7 compactCertificate293_stateChecks8

theorem compactCertificate293_chunkChecks0_0 :
    compactCertificate293.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (667 / 4) 0 (IntervalRat.scale (667 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-52978603506 / 1000000000000) (-52978603505 / 1000000000000), orderedInterval (-31638459838 / 1000000000000) (-31638459837 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (982618362249967 / 8000000000000) 0 (IntervalRat.scale (667 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-63816432193 / 1000000000000) (-63816432192 / 1000000000000), orderedInterval (-33064185778 / 1000000000000) (-33064185777 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (317758589183311 / 1600000000000) 0 (IntervalRat.scale (667 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-56292213502 / 1000000000000) (-56292213488 / 1000000000000), orderedInterval (-5918692796 / 1000000000000) (-5918692783 / 1000000000000)))) (orderedInterval (-24896800420 / 1000000000000) (-24896800406 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (286725587419469 / 8000000000000) 0 (IntervalRat.scale (667 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-117317596167 / 1000000000000) (-117317586370 / 1000000000000), orderedInterval (64866986260 / 1000000000000) (64866996056 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (770185259098793 / 8000000000000) 0 (IntervalRat.scale (667 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (26513049051 / 1000000000000) (26513049797 / 1000000000000), orderedInterval (-77012714567 / 1000000000000) (-77012713822 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2091202800822981 / 8000000000000) 0 (IntervalRat.scale (667 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-48882692482 / 1000000000000) (-48882692468 / 1000000000000), orderedInterval (-6681348808 / 1000000000000) (-6681348794 / 1000000000000)))) (orderedInterval (5715903395 / 1000000000000) (5715903550 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1540370518198253 / 8000000000000) 0 (IntervalRat.scale (667 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-57065283637 / 1000000000000) (-57065283288 / 1000000000000), orderedInterval (7209546024 / 1000000000000) (7209546373 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2639451137707169 / 8000000000000) 0 (IntervalRat.scale (667 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-32977524598 / 1000000000000) (-32977524597 / 1000000000000), orderedInterval (-28967855767 / 1000000000000) (-28967855766 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1944207761747171 / 8000000000000) 0 (IntervalRat.scale (667 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-48295446739 / 1000000000000) (-48295441136 / 1000000000000), orderedInterval (17043392272 / 1000000000000) (17043397875 / 1000000000000)))) (orderedInterval (-150046864 / 1000000000000) (-150046719 / 1000000000000))) = true
  rfl'

theorem compactCertificate293_chunkChecks0_1 :
    compactCertificate293.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2982914681984333 / 8000000000000) 0 (IntervalRat.scale (667 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (8214262427 / 1000000000000) (8214262445 / 1000000000000), orderedInterval (-40506739813 / 1000000000000) (-40506739795 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1722186594613157 / 8000000000000) 0 (IntervalRat.scale (667 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (35519298048 / 1000000000000) (35519320562 / 1000000000000), orderedInterval (-41260688556 / 1000000000000) (-41260666043 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3056050333628713 / 8000000000000) 0 (IntervalRat.scale (667 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-18957613164 / 1000000000000) (-18957612354 / 1000000000000), orderedInterval (36179012911 / 1000000000000) (36179013721 / 1000000000000)))) (orderedInterval (-1522824003 / 1000000000000) (-1522822150 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2855358642098797 / 8000000000000) 0 (IntervalRat.scale (667 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-17862014912 / 1000000000000) (-17862014375 / 1000000000000), orderedInterval (38295098736 / 1000000000000) (38295099273 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2037718659023101 / 8000000000000) 0 (IntervalRat.scale (667 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-42878178565 / 1000000000000) (-42878178564 / 1000000000000), orderedInterval (-25621914031 / 1000000000000) (-25621914030 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2310555777296379 / 8000000000000) 0 (IntervalRat.scale (667 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (25647186012 / 1000000000000) (25647186013 / 1000000000000), orderedInterval (39280358923 / 1000000000000) (39280358924 / 1000000000000)))) (orderedInterval (-3862008517 / 1000000000000) (-3862008486 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1926300519560651 / 8000000000000) 0 (IntervalRat.scale (667 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (16671186476 / 1000000000000) (16671186768 / 1000000000000), orderedInterval (-48675983038 / 1000000000000) (-48675982746 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1701944927865671 / 8000000000000) 0 (IntervalRat.scale (667 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-5481542832 / 1000000000000) (-5481542819 / 1000000000000), orderedInterval (54440770720 / 1000000000000) (54440770733 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (493289976585429 / 1600000000000) 0 (IntervalRat.scale (667 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (42597418275 / 1000000000000) (42597418277 / 1000000000000), orderedInterval (15753437506 / 1000000000000) (15753437507 / 1000000000000)))) (orderedInterval (1596866000 / 1000000000000) (1596866020 / 1000000000000))) = true
  rfl'

theorem compactCertificate293_chunkChecks0_2 :
    compactCertificate293.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1364466035664463 / 8000000000000) 0 (IntervalRat.scale (667 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (60609339884 / 1000000000000) (60609340199 / 1000000000000), orderedInterval (-7862557635 / 1000000000000) (-7862557320 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1156672969480343 / 8000000000000) 0 (IntervalRat.scale (667 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (50087205927 / 1000000000000) (50087205928 / 1000000000000), orderedInterval (43351243767 / 1000000000000) (43351243768 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (723792238252829 / 8000000000000) 0 (IntervalRat.scale (667 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-12689547397 / 1000000000000) (-12689547395 / 1000000000000), orderedInterval (-82848929389 / 1000000000000) (-82848929388 / 1000000000000)))) (orderedInterval (-12939020740 / 1000000000000) (-12939020647 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (389257872956643 / 8000000000000) 0 (IntervalRat.scale (667 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-84051034333 / 1000000000000) (-84050932625 / 1000000000000), orderedInterval (78446678473 / 1000000000000) (78446780181 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1056910846518929 / 8000000000000) 0 (IntervalRat.scale (667 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (56521802312 / 1000000000000) (56521802313 / 1000000000000), orderedInterval (40084915127 / 1000000000000) (40084915128 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1443121402834033 / 8000000000000) 0 (IntervalRat.scale (667 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-51156747630 / 1000000000000) (-51156719620 / 1000000000000), orderedInterval (30342915253 / 1000000000000) (30342943264 / 1000000000000)))) (orderedInterval (4190301150 / 1000000000000) (4190305195 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (610207761747171 / 8000000000000) 0 (IntervalRat.scale (667 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (90981339865 / 1000000000000) (90981339969 / 1000000000000), orderedInterval (-8872151117 / 1000000000000) (-8872151013 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2480460673780291 / 8000000000000) 0 (IntervalRat.scale (667 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (7893455995 / 1000000000000) (7893456014 / 1000000000000), orderedInterval (-44632529864 / 1000000000000) (-44632529845 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1656832775457869 / 8000000000000) 0 (IntervalRat.scale (667 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (28684512837 / 1000000000000) (28684512838 / 1000000000000), orderedInterval (47376664520 / 1000000000000) (47376664521 / 1000000000000)))) (orderedInterval (-5476051534 / 1000000000000) (-5476051484 / 1000000000000))) = true
  rfl'

theorem compactCertificate293_chunkChecks0 :
    compactCertificate293.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate293.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate293_chunkChecks0_0
    compactCertificate293_chunkChecks0_1 compactCertificate293_chunkChecks0_2

theorem compactCertificate293_chunkChecks1_0 :
    compactCertificate293.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (667 / 4) 1 (IntervalRat.scale (667 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-52978603506 / 1000000000000) (-52978603505 / 1000000000000), orderedInterval (-31638459838 / 1000000000000) (-31638459837 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (982618362249967 / 8000000000000) 1 (IntervalRat.scale (667 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-63816432193 / 1000000000000) (-63816432192 / 1000000000000), orderedInterval (-33064185778 / 1000000000000) (-33064185777 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (317758589183311 / 1600000000000) 1 (IntervalRat.scale (667 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-56292213502 / 1000000000000) (-56292213488 / 1000000000000), orderedInterval (-5918692796 / 1000000000000) (-5918692783 / 1000000000000)))) (orderedInterval (-13180971268 / 1000000000000) (-13180971253 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (286725587419469 / 8000000000000) 1 (IntervalRat.scale (667 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-117317596167 / 1000000000000) (-117317586370 / 1000000000000), orderedInterval (64866986260 / 1000000000000) (64866996056 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (770185259098793 / 8000000000000) 1 (IntervalRat.scale (667 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (26513049051 / 1000000000000) (26513049797 / 1000000000000), orderedInterval (-77012714567 / 1000000000000) (-77012713822 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2091202800822981 / 8000000000000) 1 (IntervalRat.scale (667 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-48882692482 / 1000000000000) (-48882692468 / 1000000000000), orderedInterval (-6681348808 / 1000000000000) (-6681348794 / 1000000000000)))) (orderedInterval (-1030118204 / 1000000000000) (-1030118140 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1540370518198253 / 8000000000000) 1 (IntervalRat.scale (667 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-57065283637 / 1000000000000) (-57065283288 / 1000000000000), orderedInterval (7209546024 / 1000000000000) (7209546373 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2639451137707169 / 8000000000000) 1 (IntervalRat.scale (667 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-32977524598 / 1000000000000) (-32977524597 / 1000000000000), orderedInterval (-28967855767 / 1000000000000) (-28967855766 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1944207761747171 / 8000000000000) 1 (IntervalRat.scale (667 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-48295446739 / 1000000000000) (-48295441136 / 1000000000000), orderedInterval (17043392272 / 1000000000000) (17043397875 / 1000000000000)))) (orderedInterval (2368169473 / 1000000000000) (2368169688 / 1000000000000))) = true
  rfl'

theorem compactCertificate293_chunkChecks1_1 :
    compactCertificate293.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2982914681984333 / 8000000000000) 1 (IntervalRat.scale (667 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (8214262427 / 1000000000000) (8214262445 / 1000000000000), orderedInterval (-40506739813 / 1000000000000) (-40506739795 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1722186594613157 / 8000000000000) 1 (IntervalRat.scale (667 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (35519298048 / 1000000000000) (35519320562 / 1000000000000), orderedInterval (-41260688556 / 1000000000000) (-41260666043 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3056050333628713 / 8000000000000) 1 (IntervalRat.scale (667 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-18957613164 / 1000000000000) (-18957612354 / 1000000000000), orderedInterval (36179012911 / 1000000000000) (36179013721 / 1000000000000)))) (orderedInterval (23929756364 / 1000000000000) (23929758925 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2855358642098797 / 8000000000000) 1 (IntervalRat.scale (667 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-17862014912 / 1000000000000) (-17862014375 / 1000000000000), orderedInterval (38295098736 / 1000000000000) (38295099273 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2037718659023101 / 8000000000000) 1 (IntervalRat.scale (667 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-42878178565 / 1000000000000) (-42878178564 / 1000000000000), orderedInterval (-25621914031 / 1000000000000) (-25621914030 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2310555777296379 / 8000000000000) 1 (IntervalRat.scale (667 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (25647186012 / 1000000000000) (25647186013 / 1000000000000), orderedInterval (39280358923 / 1000000000000) (39280358924 / 1000000000000)))) (orderedInterval (-5525099987 / 1000000000000) (-5525099933 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1926300519560651 / 8000000000000) 1 (IntervalRat.scale (667 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (16671186476 / 1000000000000) (16671186768 / 1000000000000), orderedInterval (-48675983038 / 1000000000000) (-48675982746 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1701944927865671 / 8000000000000) 1 (IntervalRat.scale (667 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-5481542832 / 1000000000000) (-5481542819 / 1000000000000), orderedInterval (54440770720 / 1000000000000) (54440770733 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (493289976585429 / 1600000000000) 1 (IntervalRat.scale (667 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (42597418275 / 1000000000000) (42597418277 / 1000000000000), orderedInterval (15753437506 / 1000000000000) (15753437507 / 1000000000000)))) (orderedInterval (-4040680707 / 1000000000000) (-4040680678 / 1000000000000))) = true
  rfl'

theorem compactCertificate293_chunkChecks1_2 :
    compactCertificate293.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1364466035664463 / 8000000000000) 1 (IntervalRat.scale (667 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (60609339884 / 1000000000000) (60609340199 / 1000000000000), orderedInterval (-7862557635 / 1000000000000) (-7862557320 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1156672969480343 / 8000000000000) 1 (IntervalRat.scale (667 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (50087205927 / 1000000000000) (50087205928 / 1000000000000), orderedInterval (43351243767 / 1000000000000) (43351243768 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (723792238252829 / 8000000000000) 1 (IntervalRat.scale (667 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-12689547397 / 1000000000000) (-12689547395 / 1000000000000), orderedInterval (-82848929389 / 1000000000000) (-82848929388 / 1000000000000)))) (orderedInterval (-2305050200 / 1000000000000) (-2305050109 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (389257872956643 / 8000000000000) 1 (IntervalRat.scale (667 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-84051034333 / 1000000000000) (-84050932625 / 1000000000000), orderedInterval (78446678473 / 1000000000000) (78446780181 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1056910846518929 / 8000000000000) 1 (IntervalRat.scale (667 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (56521802312 / 1000000000000) (56521802313 / 1000000000000), orderedInterval (40084915127 / 1000000000000) (40084915128 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1443121402834033 / 8000000000000) 1 (IntervalRat.scale (667 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-51156747630 / 1000000000000) (-51156719620 / 1000000000000), orderedInterval (30342915253 / 1000000000000) (30342943264 / 1000000000000)))) (orderedInterval (-3658854641 / 1000000000000) (-3658851752 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (610207761747171 / 8000000000000) 1 (IntervalRat.scale (667 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (90981339865 / 1000000000000) (90981339969 / 1000000000000), orderedInterval (-8872151117 / 1000000000000) (-8872151013 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2480460673780291 / 8000000000000) 1 (IntervalRat.scale (667 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (7893455995 / 1000000000000) (7893456014 / 1000000000000), orderedInterval (-44632529864 / 1000000000000) (-44632529845 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1656832775457869 / 8000000000000) 1 (IntervalRat.scale (667 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (28684512837 / 1000000000000) (28684512838 / 1000000000000), orderedInterval (47376664520 / 1000000000000) (47376664521 / 1000000000000)))) (orderedInterval (-4309214260 / 1000000000000) (-4309214191 / 1000000000000))) = true
  rfl'

theorem compactCertificate293_chunkChecks1 :
    compactCertificate293.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate293.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate293_chunkChecks1_0
    compactCertificate293_chunkChecks1_1 compactCertificate293_chunkChecks1_2

theorem compactCertificate293_chunkChecks2_0 :
    compactCertificate293.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (667 / 4) 2 (IntervalRat.scale (667 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-52978603506 / 1000000000000) (-52978603505 / 1000000000000), orderedInterval (-31638459838 / 1000000000000) (-31638459837 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (982618362249967 / 8000000000000) 2 (IntervalRat.scale (667 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-63816432193 / 1000000000000) (-63816432192 / 1000000000000), orderedInterval (-33064185778 / 1000000000000) (-33064185777 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (317758589183311 / 1600000000000) 2 (IntervalRat.scale (667 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-56292213502 / 1000000000000) (-56292213488 / 1000000000000), orderedInterval (-5918692796 / 1000000000000) (-5918692783 / 1000000000000)))) (orderedInterval (26086198221 / 1000000000000) (26086198239 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (286725587419469 / 8000000000000) 2 (IntervalRat.scale (667 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-117317596167 / 1000000000000) (-117317586370 / 1000000000000), orderedInterval (64866986260 / 1000000000000) (64866996056 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (770185259098793 / 8000000000000) 2 (IntervalRat.scale (667 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (26513049051 / 1000000000000) (26513049797 / 1000000000000), orderedInterval (-77012714567 / 1000000000000) (-77012713822 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2091202800822981 / 8000000000000) 2 (IntervalRat.scale (667 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-48882692482 / 1000000000000) (-48882692468 / 1000000000000), orderedInterval (-6681348808 / 1000000000000) (-6681348794 / 1000000000000)))) (orderedInterval (-8914992374 / 1000000000000) (-8914992325 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1540370518198253 / 8000000000000) 2 (IntervalRat.scale (667 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-57065283637 / 1000000000000) (-57065283288 / 1000000000000), orderedInterval (7209546024 / 1000000000000) (7209546373 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2639451137707169 / 8000000000000) 2 (IntervalRat.scale (667 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-32977524598 / 1000000000000) (-32977524597 / 1000000000000), orderedInterval (-28967855767 / 1000000000000) (-28967855766 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1944207761747171 / 8000000000000) 2 (IntervalRat.scale (667 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-48295446739 / 1000000000000) (-48295441136 / 1000000000000), orderedInterval (17043392272 / 1000000000000) (17043397875 / 1000000000000)))) (orderedInterval (-1516976365 / 1000000000000) (-1516976046 / 1000000000000))) = true
  rfl'

theorem compactCertificate293_chunkChecks2_1 :
    compactCertificate293.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2982914681984333 / 8000000000000) 2 (IntervalRat.scale (667 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (8214262427 / 1000000000000) (8214262445 / 1000000000000), orderedInterval (-40506739813 / 1000000000000) (-40506739795 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1722186594613157 / 8000000000000) 2 (IntervalRat.scale (667 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (35519298048 / 1000000000000) (35519320562 / 1000000000000), orderedInterval (-41260688556 / 1000000000000) (-41260666043 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3056050333628713 / 8000000000000) 2 (IntervalRat.scale (667 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-18957613164 / 1000000000000) (-18957612354 / 1000000000000), orderedInterval (36179012911 / 1000000000000) (36179013721 / 1000000000000)))) (orderedInterval (16911751488 / 1000000000000) (16911755197 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2855358642098797 / 8000000000000) 2 (IntervalRat.scale (667 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-17862014912 / 1000000000000) (-17862014375 / 1000000000000), orderedInterval (38295098736 / 1000000000000) (38295099273 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2037718659023101 / 8000000000000) 2 (IntervalRat.scale (667 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-42878178565 / 1000000000000) (-42878178564 / 1000000000000), orderedInterval (-25621914031 / 1000000000000) (-25621914030 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2310555777296379 / 8000000000000) 2 (IntervalRat.scale (667 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (25647186012 / 1000000000000) (25647186013 / 1000000000000), orderedInterval (39280358923 / 1000000000000) (39280358924 / 1000000000000)))) (orderedInterval (8406052866 / 1000000000000) (8406052965 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1926300519560651 / 8000000000000) 2 (IntervalRat.scale (667 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (16671186476 / 1000000000000) (16671186768 / 1000000000000), orderedInterval (-48675983038 / 1000000000000) (-48675982746 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1701944927865671 / 8000000000000) 2 (IntervalRat.scale (667 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-5481542832 / 1000000000000) (-5481542819 / 1000000000000), orderedInterval (54440770720 / 1000000000000) (54440770733 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (493289976585429 / 1600000000000) 2 (IntervalRat.scale (667 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (42597418275 / 1000000000000) (42597418277 / 1000000000000), orderedInterval (15753437506 / 1000000000000) (15753437507 / 1000000000000)))) (orderedInterval (-4616192177 / 1000000000000) (-4616192133 / 1000000000000))) = true
  rfl'

theorem compactCertificate293_chunkChecks2_2 :
    compactCertificate293.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1364466035664463 / 8000000000000) 2 (IntervalRat.scale (667 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (60609339884 / 1000000000000) (60609340199 / 1000000000000), orderedInterval (-7862557635 / 1000000000000) (-7862557320 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1156672969480343 / 8000000000000) 2 (IntervalRat.scale (667 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (50087205927 / 1000000000000) (50087205928 / 1000000000000), orderedInterval (43351243767 / 1000000000000) (43351243768 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (723792238252829 / 8000000000000) 2 (IntervalRat.scale (667 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-12689547397 / 1000000000000) (-12689547395 / 1000000000000), orderedInterval (-82848929389 / 1000000000000) (-82848929388 / 1000000000000)))) (orderedInterval (12405452855 / 1000000000000) (12405452946 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (389257872956643 / 8000000000000) 2 (IntervalRat.scale (667 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-84051034333 / 1000000000000) (-84050932625 / 1000000000000), orderedInterval (78446678473 / 1000000000000) (78446780181 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1056910846518929 / 8000000000000) 2 (IntervalRat.scale (667 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (56521802312 / 1000000000000) (56521802313 / 1000000000000), orderedInterval (40084915127 / 1000000000000) (40084915128 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1443121402834033 / 8000000000000) 2 (IntervalRat.scale (667 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-51156747630 / 1000000000000) (-51156719620 / 1000000000000), orderedInterval (30342915253 / 1000000000000) (30342943264 / 1000000000000)))) (orderedInterval (-3893519705 / 1000000000000) (-3893516997 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (610207761747171 / 8000000000000) 2 (IntervalRat.scale (667 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (90981339865 / 1000000000000) (90981339969 / 1000000000000), orderedInterval (-8872151117 / 1000000000000) (-8872151013 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2480460673780291 / 8000000000000) 2 (IntervalRat.scale (667 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (7893455995 / 1000000000000) (7893456014 / 1000000000000), orderedInterval (-44632529864 / 1000000000000) (-44632529845 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1656832775457869 / 8000000000000) 2 (IntervalRat.scale (667 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (28684512837 / 1000000000000) (28684512838 / 1000000000000), orderedInterval (47376664520 / 1000000000000) (47376664521 / 1000000000000)))) (orderedInterval (10434711076 / 1000000000000) (10434711179 / 1000000000000))) = true
  rfl'

theorem compactCertificate293_chunkChecks2 :
    compactCertificate293.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate293.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate293_chunkChecks2_0
    compactCertificate293_chunkChecks2_1 compactCertificate293_chunkChecks2_2

theorem compactCertificate293_chunkChecks3_0 :
    compactCertificate293.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (667 / 4) 3 (IntervalRat.scale (667 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-52978603506 / 1000000000000) (-52978603505 / 1000000000000), orderedInterval (-31638459838 / 1000000000000) (-31638459837 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (982618362249967 / 8000000000000) 3 (IntervalRat.scale (667 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-63816432193 / 1000000000000) (-63816432192 / 1000000000000), orderedInterval (-33064185778 / 1000000000000) (-33064185777 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (317758589183311 / 1600000000000) 3 (IntervalRat.scale (667 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-56292213502 / 1000000000000) (-56292213488 / 1000000000000), orderedInterval (-5918692796 / 1000000000000) (-5918692783 / 1000000000000)))) (orderedInterval (13093354411 / 1000000000000) (13093354431 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (286725587419469 / 8000000000000) 3 (IntervalRat.scale (667 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-117317596167 / 1000000000000) (-117317586370 / 1000000000000), orderedInterval (64866986260 / 1000000000000) (64866996056 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (770185259098793 / 8000000000000) 3 (IntervalRat.scale (667 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (26513049051 / 1000000000000) (26513049797 / 1000000000000), orderedInterval (-77012714567 / 1000000000000) (-77012713822 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2091202800822981 / 8000000000000) 3 (IntervalRat.scale (667 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-48882692482 / 1000000000000) (-48882692468 / 1000000000000), orderedInterval (-6681348808 / 1000000000000) (-6681348794 / 1000000000000)))) (orderedInterval (-1228190051 / 1000000000000) (-1228189993 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1540370518198253 / 8000000000000) 3 (IntervalRat.scale (667 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-57065283637 / 1000000000000) (-57065283288 / 1000000000000), orderedInterval (7209546024 / 1000000000000) (7209546373 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2639451137707169 / 8000000000000) 3 (IntervalRat.scale (667 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-32977524598 / 1000000000000) (-32977524597 / 1000000000000), orderedInterval (-28967855767 / 1000000000000) (-28967855766 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1944207761747171 / 8000000000000) 3 (IntervalRat.scale (667 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-48295446739 / 1000000000000) (-48295441136 / 1000000000000), orderedInterval (17043392272 / 1000000000000) (17043397875 / 1000000000000)))) (orderedInterval (-8186823802 / 1000000000000) (-8186823327 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate293_chunkChecks3_1 :
    compactCertificate293.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2982914681984333 / 8000000000000) 3 (IntervalRat.scale (667 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (8214262427 / 1000000000000) (8214262445 / 1000000000000), orderedInterval (-40506739813 / 1000000000000) (-40506739795 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1722186594613157 / 8000000000000) 3 (IntervalRat.scale (667 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (35519298048 / 1000000000000) (35519320562 / 1000000000000), orderedInterval (-41260688556 / 1000000000000) (-41260666043 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3056050333628713 / 8000000000000) 3 (IntervalRat.scale (667 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-18957613164 / 1000000000000) (-18957612354 / 1000000000000), orderedInterval (36179012911 / 1000000000000) (36179013721 / 1000000000000)))) (orderedInterval (-135829107993 / 1000000000000) (-135829102320 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2855358642098797 / 8000000000000) 3 (IntervalRat.scale (667 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-17862014912 / 1000000000000) (-17862014375 / 1000000000000), orderedInterval (38295098736 / 1000000000000) (38295099273 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2037718659023101 / 8000000000000) 3 (IntervalRat.scale (667 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-42878178565 / 1000000000000) (-42878178564 / 1000000000000), orderedInterval (-25621914031 / 1000000000000) (-25621914030 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2310555777296379 / 8000000000000) 3 (IntervalRat.scale (667 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (25647186012 / 1000000000000) (25647186013 / 1000000000000), orderedInterval (39280358923 / 1000000000000) (39280358924 / 1000000000000)))) (orderedInterval (16397663620 / 1000000000000) (16397663807 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1926300519560651 / 8000000000000) 3 (IntervalRat.scale (667 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (16671186476 / 1000000000000) (16671186768 / 1000000000000), orderedInterval (-48675983038 / 1000000000000) (-48675982746 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1701944927865671 / 8000000000000) 3 (IntervalRat.scale (667 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-5481542832 / 1000000000000) (-5481542819 / 1000000000000), orderedInterval (54440770720 / 1000000000000) (54440770733 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (493289976585429 / 1600000000000) 3 (IntervalRat.scale (667 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (42597418275 / 1000000000000) (42597418277 / 1000000000000), orderedInterval (15753437506 / 1000000000000) (15753437507 / 1000000000000)))) (orderedInterval (5640430842 / 1000000000000) (5640430907 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate293_chunkChecks3_2 :
    compactCertificate293.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1364466035664463 / 8000000000000) 3 (IntervalRat.scale (667 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (60609339884 / 1000000000000) (60609340199 / 1000000000000), orderedInterval (-7862557635 / 1000000000000) (-7862557320 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1156672969480343 / 8000000000000) 3 (IntervalRat.scale (667 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (50087205927 / 1000000000000) (50087205928 / 1000000000000), orderedInterval (43351243767 / 1000000000000) (43351243768 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (723792238252829 / 8000000000000) 3 (IntervalRat.scale (667 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-12689547397 / 1000000000000) (-12689547395 / 1000000000000), orderedInterval (-82848929389 / 1000000000000) (-82848929388 / 1000000000000)))) (orderedInterval (610540413 / 1000000000000) (610540504 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (389257872956643 / 8000000000000) 3 (IntervalRat.scale (667 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-84051034333 / 1000000000000) (-84050932625 / 1000000000000), orderedInterval (78446678473 / 1000000000000) (78446780181 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1056910846518929 / 8000000000000) 3 (IntervalRat.scale (667 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (56521802312 / 1000000000000) (56521802313 / 1000000000000), orderedInterval (40084915127 / 1000000000000) (40084915128 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1443121402834033 / 8000000000000) 3 (IntervalRat.scale (667 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-51156747630 / 1000000000000) (-51156719620 / 1000000000000), orderedInterval (30342915253 / 1000000000000) (30342943264 / 1000000000000)))) (orderedInterval (3455548161 / 1000000000000) (3455550961 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (610207761747171 / 8000000000000) 3 (IntervalRat.scale (667 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (90981339865 / 1000000000000) (90981339969 / 1000000000000), orderedInterval (-8872151117 / 1000000000000) (-8872151013 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2480460673780291 / 8000000000000) 3 (IntervalRat.scale (667 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (7893455995 / 1000000000000) (7893456014 / 1000000000000), orderedInterval (-44632529864 / 1000000000000) (-44632529845 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1656832775457869 / 8000000000000) 3 (IntervalRat.scale (667 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (28684512837 / 1000000000000) (28684512838 / 1000000000000), orderedInterval (47376664520 / 1000000000000) (47376664521 / 1000000000000)))) (orderedInterval (-6384004115 / 1000000000000) (-6384003956 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate293_chunkChecks3 :
    compactCertificate293.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate293.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate293_chunkChecks3_0
    compactCertificate293_chunkChecks3_1 compactCertificate293_chunkChecks3_2

theorem compactCertificate293_chunkChecks4_0 :
    compactCertificate293.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (667 / 4) 4 (IntervalRat.scale (667 / 4) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-52978603506 / 1000000000000) (-52978603505 / 1000000000000), orderedInterval (-31638459838 / 1000000000000) (-31638459837 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (982618362249967 / 8000000000000) 4 (IntervalRat.scale (667 / 4) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-63816432193 / 1000000000000) (-63816432192 / 1000000000000), orderedInterval (-33064185778 / 1000000000000) (-33064185777 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (317758589183311 / 1600000000000) 4 (IntervalRat.scale (667 / 4) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-56292213502 / 1000000000000) (-56292213488 / 1000000000000), orderedInterval (-5918692796 / 1000000000000) (-5918692783 / 1000000000000)))) (orderedInterval (-27976515633 / 1000000000000) (-27976515610 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (286725587419469 / 8000000000000) 4 (IntervalRat.scale (667 / 4) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-117317596167 / 1000000000000) (-117317586370 / 1000000000000), orderedInterval (64866986260 / 1000000000000) (64866996056 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (770185259098793 / 8000000000000) 4 (IntervalRat.scale (667 / 4) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (26513049051 / 1000000000000) (26513049797 / 1000000000000), orderedInterval (-77012714567 / 1000000000000) (-77012713822 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2091202800822981 / 8000000000000) 4 (IntervalRat.scale (667 / 4) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-48882692482 / 1000000000000) (-48882692468 / 1000000000000), orderedInterval (-6681348808 / 1000000000000) (-6681348794 / 1000000000000)))) (orderedInterval (21110351393 / 1000000000000) (21110351476 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1540370518198253 / 8000000000000) 4 (IntervalRat.scale (667 / 4) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-57065283637 / 1000000000000) (-57065283288 / 1000000000000), orderedInterval (7209546024 / 1000000000000) (7209546373 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2639451137707169 / 8000000000000) 4 (IntervalRat.scale (667 / 4) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-32977524598 / 1000000000000) (-32977524597 / 1000000000000), orderedInterval (-28967855767 / 1000000000000) (-28967855766 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1944207761747171 / 8000000000000) 4 (IntervalRat.scale (667 / 4) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-48295446739 / 1000000000000) (-48295441136 / 1000000000000), orderedInterval (17043392272 / 1000000000000) (17043397875 / 1000000000000)))) (orderedInterval (10421029847 / 1000000000000) (10421030562 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate293_chunkChecks4_1 :
    compactCertificate293.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2982914681984333 / 8000000000000) 4 (IntervalRat.scale (667 / 4) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (8214262427 / 1000000000000) (8214262445 / 1000000000000), orderedInterval (-40506739813 / 1000000000000) (-40506739795 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1722186594613157 / 8000000000000) 4 (IntervalRat.scale (667 / 4) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (35519298048 / 1000000000000) (35519320562 / 1000000000000), orderedInterval (-41260688556 / 1000000000000) (-41260666043 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3056050333628713 / 8000000000000) 4 (IntervalRat.scale (667 / 4) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-18957613164 / 1000000000000) (-18957612354 / 1000000000000), orderedInterval (36179012911 / 1000000000000) (36179013721 / 1000000000000)))) (orderedInterval (-101777307844 / 1000000000000) (-101777298470 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2855358642098797 / 8000000000000) 4 (IntervalRat.scale (667 / 4) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-17862014912 / 1000000000000) (-17862014375 / 1000000000000), orderedInterval (38295098736 / 1000000000000) (38295099273 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2037718659023101 / 8000000000000) 4 (IntervalRat.scale (667 / 4) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-42878178565 / 1000000000000) (-42878178564 / 1000000000000), orderedInterval (-25621914031 / 1000000000000) (-25621914030 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2310555777296379 / 8000000000000) 4 (IntervalRat.scale (667 / 4) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (25647186012 / 1000000000000) (25647186013 / 1000000000000), orderedInterval (39280358923 / 1000000000000) (39280358924 / 1000000000000)))) (orderedInterval (-16671337769 / 1000000000000) (-16671337406 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1926300519560651 / 8000000000000) 4 (IntervalRat.scale (667 / 4) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (16671186476 / 1000000000000) (16671186768 / 1000000000000), orderedInterval (-48675983038 / 1000000000000) (-48675982746 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1701944927865671 / 8000000000000) 4 (IntervalRat.scale (667 / 4) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-5481542832 / 1000000000000) (-5481542819 / 1000000000000), orderedInterval (54440770720 / 1000000000000) (54440770733 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (493289976585429 / 1600000000000) 4 (IntervalRat.scale (667 / 4) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (42597418275 / 1000000000000) (42597418277 / 1000000000000), orderedInterval (15753437506 / 1000000000000) (15753437507 / 1000000000000)))) (orderedInterval (14345789836 / 1000000000000) (14345789938 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate293_chunkChecks4_2 :
    compactCertificate293.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1364466035664463 / 8000000000000) 4 (IntervalRat.scale (667 / 4) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (60609339884 / 1000000000000) (60609340199 / 1000000000000), orderedInterval (-7862557635 / 1000000000000) (-7862557320 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1156672969480343 / 8000000000000) 4 (IntervalRat.scale (667 / 4) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (50087205927 / 1000000000000) (50087205928 / 1000000000000), orderedInterval (43351243767 / 1000000000000) (43351243768 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (723792238252829 / 8000000000000) 4 (IntervalRat.scale (667 / 4) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-12689547397 / 1000000000000) (-12689547395 / 1000000000000), orderedInterval (-82848929389 / 1000000000000) (-82848929388 / 1000000000000)))) (orderedInterval (-12252105965 / 1000000000000) (-12252105873 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (389257872956643 / 8000000000000) 4 (IntervalRat.scale (667 / 4) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-84051034333 / 1000000000000) (-84050932625 / 1000000000000), orderedInterval (78446678473 / 1000000000000) (78446780181 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1056910846518929 / 8000000000000) 4 (IntervalRat.scale (667 / 4) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (56521802312 / 1000000000000) (56521802313 / 1000000000000), orderedInterval (40084915127 / 1000000000000) (40084915128 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1443121402834033 / 8000000000000) 4 (IntervalRat.scale (667 / 4) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-51156747630 / 1000000000000) (-51156719620 / 1000000000000), orderedInterval (30342915253 / 1000000000000) (30342943264 / 1000000000000)))) (orderedInterval (4833975356 / 1000000000000) (4833978363 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (610207761747171 / 8000000000000) 4 (IntervalRat.scale (667 / 4) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (90981339865 / 1000000000000) (90981339969 / 1000000000000), orderedInterval (-8872151117 / 1000000000000) (-8872151013 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2480460673780291 / 8000000000000) 4 (IntervalRat.scale (667 / 4) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (7893455995 / 1000000000000) (7893456014 / 1000000000000), orderedInterval (-44632529864 / 1000000000000) (-44632529845 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1656832775457869 / 8000000000000) 4 (IntervalRat.scale (667 / 4) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (28684512837 / 1000000000000) (28684512838 / 1000000000000), orderedInterval (47376664520 / 1000000000000) (47376664521 / 1000000000000)))) (orderedInterval (-20386432131 / 1000000000000) (-20386431874 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate293_chunkChecks4 :
    compactCertificate293.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate293.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate293_chunkChecks4_0
    compactCertificate293_chunkChecks4_1 compactCertificate293_chunkChecks4_2

theorem compactCertificate293_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate293.chunkCheck r b = true :=
  compactCertificate293.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate293_chunkChecks0
    · exact compactCertificate293_chunkChecks1
    · exact compactCertificate293_chunkChecks2
    · exact compactCertificate293_chunkChecks3
    · exact compactCertificate293_chunkChecks4)

theorem compactCertificate293_coefficient0 :
    compactCertificate293.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate293_coefficient1 :
    compactCertificate293.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate293_coefficient2 :
    compactCertificate293.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate293_coefficient3 :
    compactCertificate293.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate293_coefficient4 :
    compactCertificate293.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate293_coefficients : ∀ r : Fin 5,
    compactCertificate293.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate293_coefficient0
  · exact compactCertificate293_coefficient1
  · exact compactCertificate293_coefficient2
  · exact compactCertificate293_coefficient3
  · exact compactCertificate293_coefficient4

theorem compactCertificate293_lower : (1 : ℚ) ≤ compactCertificate293.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate293, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate293_proves {t : ℝ} (ht : t ∈ compactCertificate293.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate293.proves compactCertificate293_states compactCertificate293_chunks
    compactCertificate293_coefficients compactCertificate293_lower ht

end Erdos232
