/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate481 : CompactCertificate where
  left := 352
  right := 353
  center := 705 / 2
  grid := fun i =>
    match i.val with
    | 0 => 112
    | 1 => 83
    | 2 => 134
    | 3 => 24
    | 4 => 65
    | 5 => 176
    | 6 => 130
    | 7 => 222
    | 8 => 164
    | 9 => 251
    | 10 => 145
    | 11 => 257
    | 12 => 240
    | 13 => 171
    | 14 => 194
    | 15 => 162
    | 16 => 143
    | 17 => 208
    | 18 => 115
    | 19 => 97
    | 20 => 61
    | 21 => 33
    | 22 => 89
    | 23 => 121
    | 24 => 51
    | 25 => 209
    | _ => 139
  point := fun i =>
    match i.val with
    | 0 => 705 / 2
    | 1 => 207719923654041 / 800000000000
    | 2 => 67172355434553 / 160000000000
    | 3 => 60612155661387 / 800000000000
    | 4 => 162812775911439 / 800000000000
    | 5 => 442068358194963 / 800000000000
    | 6 => 325625551823019 / 800000000000
    | 7 => 557964933158487 / 800000000000
    | 8 => 410994444387333 / 800000000000
    | 9 => 630571169654859 / 800000000000
    | 10 => 364060434543411 / 800000000000
    | 11 => 646031629747599 / 800000000000
    | 12 => 603606549529131 / 800000000000
    | 13 => 430762115325723 / 800000000000
    | 14 => 488438327734317 / 800000000000
    | 15 => 407208955409373 / 800000000000
    | 16 => 359781461512833 / 800000000000
    | 17 => 104278690702467 / 160000000000
    | 18 => 288440346369849 / 800000000000
    | 19 => 244514076007089 / 800000000000
    | 20 => 153005555612667 / 800000000000
    | 21 => 82286896681989 / 800000000000
    | 22 => 223424931572967 / 800000000000
    | 23 => 305067642877959 / 800000000000
    | 24 => 128994444387333 / 800000000000
    | 25 => 524355254877093 / 800000000000
    | _ => 350245009504587 / 800000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (42056553540 / 1000000000000) (42056553565 / 1000000000000), orderedInterval (6044286775 / 1000000000000) (6044286801 / 1000000000000))
    | 1 => (orderedInterval (15452358264 / 1000000000000) (15452358482 / 1000000000000), orderedInterval (-47073005594 / 1000000000000) (-47073005377 / 1000000000000))
    | 2 => (orderedInterval (-13757683248 / 1000000000000) (-13757683117 / 1000000000000), orderedInterval (36445935072 / 1000000000000) (36445935203 / 1000000000000))
    | 3 => (orderedInterval (83694827457 / 1000000000000) (83694827458 / 1000000000000), orderedInterval (36832045451 / 1000000000000) (36832045452 / 1000000000000))
    | 4 => (orderedInterval (-5429527915 / 1000000000000) (-5429527914 / 1000000000000), orderedInterval (-55652060223 / 1000000000000) (-55652060222 / 1000000000000))
    | 5 => (orderedInterval (14773251432 / 1000000000000) (14773251433 / 1000000000000), orderedInterval (30545201643 / 1000000000000) (30545201644 / 1000000000000))
    | 6 => (orderedInterval (-22003488186 / 1000000000000) (-22003485765 / 1000000000000), orderedInterval (32888869200 / 1000000000000) (32888871621 / 1000000000000))
    | 7 => (orderedInterval (21836726982 / 1000000000000) (21836726983 / 1000000000000), orderedInterval (20863311567 / 1000000000000) (20863311568 / 1000000000000))
    | 8 => (orderedInterval (-22488302170 / 1000000000000) (-22488298046 / 1000000000000), orderedInterval (27104273486 / 1000000000000) (27104277610 / 1000000000000))
    | 9 => (orderedInterval (-12602707356 / 1000000000000) (-12602707355 / 1000000000000), orderedInterval (-25464454847 / 1000000000000) (-25464454846 / 1000000000000))
    | 10 => (orderedInterval (-12110463850 / 1000000000000) (-12110463849 / 1000000000000), orderedInterval (-35374112753 / 1000000000000) (-35374112752 / 1000000000000))
    | 11 => (orderedInterval (-22598924506 / 1000000000000) (-22598924504 / 1000000000000), orderedInterval (-16648347909 / 1000000000000) (-16648347907 / 1000000000000))
    | 12 => (orderedInterval (28074047978 / 1000000000000) (28074048071 / 1000000000000), orderedInterval (7438090180 / 1000000000000) (7438090273 / 1000000000000))
    | 13 => (orderedInterval (-30891522574 / 1000000000000) (-30891452858 / 1000000000000), orderedInterval (15129279180 / 1000000000000) (15129348896 / 1000000000000))
    | 14 => (orderedInterval (30911604945 / 1000000000000) (30911627720 / 1000000000000), orderedInterval (-9362031253 / 1000000000000) (-9362008478 / 1000000000000))
    | 15 => (orderedInterval (26762855267 / 1000000000000) (26762855268 / 1000000000000), orderedInterval (23091852156 / 1000000000000) (23091852157 / 1000000000000))
    | 16 => (orderedInterval (-35869476221 / 1000000000000) (-35869476216 / 1000000000000), orderedInterval (-11315731344 / 1000000000000) (-11315731339 / 1000000000000))
    | 17 => (orderedInterval (-24945768858 / 1000000000000) (-24945748073 / 1000000000000), orderedInterval (18847471116 / 1000000000000) (18847491901 / 1000000000000))
    | 18 => (orderedInterval (-2197876621 / 1000000000000) (-2197876620 / 1000000000000), orderedInterval (-41959549456 / 1000000000000) (-41959549455 / 1000000000000))
    | 19 => (orderedInterval (-45297762068 / 1000000000000) (-45297761360 / 1000000000000), orderedInterval (5641834465 / 1000000000000) (5641835173 / 1000000000000))
    | 20 => (orderedInterval (-22707981022 / 1000000000000) (-22707981021 / 1000000000000), orderedInterval (-52978031703 / 1000000000000) (-52978031702 / 1000000000000))
    | 21 => (orderedInterval (2340425496 / 1000000000000) (2340425506 / 1000000000000), orderedInterval (-78648933543 / 1000000000000) (-78648933533 / 1000000000000))
    | 22 => (orderedInterval (-21382565769 / 1000000000000) (-21382565768 / 1000000000000), orderedInterval (-42649915998 / 1000000000000) (-42649915997 / 1000000000000))
    | 23 => (orderedInterval (-37372251388 / 1000000000000) (-37372227154 / 1000000000000), orderedInterval (16564643792 / 1000000000000) (16564668026 / 1000000000000))
    | 24 => (orderedInterval (-61097879187 / 1000000000000) (-61097878037 / 1000000000000), orderedInterval (14860242010 / 1000000000000) (14860243160 / 1000000000000))
    | 25 => (orderedInterval (11083352448 / 1000000000000) (11083352472 / 1000000000000), orderedInterval (-29136441339 / 1000000000000) (-29136441315 / 1000000000000))
    | _ => (orderedInterval (-35960072518 / 1000000000000) (-35960057191 / 1000000000000), orderedInterval (12729085264 / 1000000000000) (12729100591 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (16006415002 / 1000000000000) (16006415046 / 1000000000000)
      | 1 => orderedInterval (-2156496245 / 1000000000000) (-2156496202 / 1000000000000)
      | 2 => orderedInterval (-1217029933 / 1000000000000) (-1217029813 / 1000000000000)
      | 3 => orderedInterval (-1870507124 / 1000000000000) (-1870506983 / 1000000000000)
      | 4 => orderedInterval (-3584444776 / 1000000000000) (-3584438025 / 1000000000000)
      | 5 => orderedInterval (1723029315 / 1000000000000) (1723029882 / 1000000000000)
      | 6 => orderedInterval (2176010639 / 1000000000000) (2176010768 / 1000000000000)
      | 7 => orderedInterval (3306052325 / 1000000000000) (3306054225 / 1000000000000)
      | _ => orderedInterval (5476537950 / 1000000000000) (5476540933 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (4619828399 / 1000000000000) (4619828448 / 1000000000000)
      | 1 => orderedInterval (-4663038895 / 1000000000000) (-4663038846 / 1000000000000)
      | 2 => orderedInterval (-318546786 / 1000000000000) (-318546606 / 1000000000000)
      | 3 => orderedInterval (1312223320 / 1000000000000) (1312223611 / 1000000000000)
      | 4 => orderedInterval (1980020580 / 1000000000000) (1980030922 / 1000000000000)
      | 5 => orderedInterval (2103455779 / 1000000000000) (2103456813 / 1000000000000)
      | 6 => orderedInterval (5649573047 / 1000000000000) (5649573164 / 1000000000000)
      | 7 => orderedInterval (-182965027 / 1000000000000) (-182962979 / 1000000000000)
      | _ => orderedInterval (1484763648 / 1000000000000) (1484767363 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-15615812736 / 1000000000000) (-15615812682 / 1000000000000)
      | 1 => orderedInterval (2702109652 / 1000000000000) (2702109720 / 1000000000000)
      | 2 => orderedInterval (3792123631 / 1000000000000) (3792123905 / 1000000000000)
      | 3 => orderedInterval (7155179896 / 1000000000000) (7155180520 / 1000000000000)
      | 4 => orderedInterval (9601792239 / 1000000000000) (9601808117 / 1000000000000)
      | 5 => orderedInterval (-1808166358 / 1000000000000) (-1808164462 / 1000000000000)
      | 6 => orderedInterval (-2093592798 / 1000000000000) (-2093592689 / 1000000000000)
      | 7 => orderedInterval (-3652220336 / 1000000000000) (-3652218119 / 1000000000000)
      | _ => orderedInterval (-7215676198 / 1000000000000) (-7215671541 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-5789222585 / 1000000000000) (-5789222524 / 1000000000000)
      | 1 => orderedInterval (8752398034 / 1000000000000) (8752398134 / 1000000000000)
      | 2 => orderedInterval (2945938052 / 1000000000000) (2945938473 / 1000000000000)
      | 3 => orderedInterval (-16514481076 / 1000000000000) (-16514479711 / 1000000000000)
      | 4 => orderedInterval (-4055826797 / 1000000000000) (-4055802448 / 1000000000000)
      | 5 => orderedInterval (-5192594351 / 1000000000000) (-5192590870 / 1000000000000)
      | 6 => orderedInterval (-6689629013 / 1000000000000) (-6689628911 / 1000000000000)
      | 7 => orderedInterval (1100270176 / 1000000000000) (1100272573 / 1000000000000)
      | _ => orderedInterval (-10659912284 / 1000000000000) (-10659906436 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (15120465884 / 1000000000000) (15120465953 / 1000000000000)
      | 1 => orderedInterval (-6415857011 / 1000000000000) (-6415856857 / 1000000000000)
      | 2 => orderedInterval (-12791432120 / 1000000000000) (-12791431462 / 1000000000000)
      | 3 => orderedInterval (-34900322875 / 1000000000000) (-34900319842 / 1000000000000)
      | 4 => orderedInterval (-27927436812 / 1000000000000) (-27927399378 / 1000000000000)
      | 5 => orderedInterval (-652289569 / 1000000000000) (-652283152 / 1000000000000)
      | 6 => orderedInterval (1807660605 / 1000000000000) (1807660703 / 1000000000000)
      | 7 => orderedInterval (4107270423 / 1000000000000) (4107273021 / 1000000000000)
      | _ => orderedInterval (5314363624 / 1000000000000) (5314371024 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (19859567153 / 1000000000000) (19859579831 / 1000000000000)
    | 1 => orderedInterval (11985314065 / 1000000000000) (11985331890 / 1000000000000)
    | 2 => orderedInterval (-7134263008 / 1000000000000) (-7134237231 / 1000000000000)
    | 3 => orderedInterval (-36103059844 / 1000000000000) (-36103021720 / 1000000000000)
    | _ => orderedInterval (-56337577851 / 1000000000000) (-56337519990 / 1000000000000)

theorem compactCertificate481_stateChecks0 :
    compactCertificate481.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 112 12 (705 / 2)) (orderedInterval (42056553540 / 1000000000000) (42056553565 / 1000000000000), orderedInterval (6044286775 / 1000000000000) (6044286801 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 83 12 (207719923654041 / 800000000000)) (orderedInterval (15452358264 / 1000000000000) (15452358482 / 1000000000000), orderedInterval (-47073005594 / 1000000000000) (-47073005377 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 134 12 (67172355434553 / 160000000000)) (orderedInterval (-13757683248 / 1000000000000) (-13757683117 / 1000000000000), orderedInterval (36445935072 / 1000000000000) (36445935203 / 1000000000000))) = true
  rfl'

theorem compactCertificate481_stateChecks1 :
    compactCertificate481.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 24 12 (60612155661387 / 800000000000)) (orderedInterval (83694827457 / 1000000000000) (83694827458 / 1000000000000), orderedInterval (36832045451 / 1000000000000) (36832045452 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 65 12 (162812775911439 / 800000000000)) (orderedInterval (-5429527915 / 1000000000000) (-5429527914 / 1000000000000), orderedInterval (-55652060223 / 1000000000000) (-55652060222 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 176 12 (442068358194963 / 800000000000)) (orderedInterval (14773251432 / 1000000000000) (14773251433 / 1000000000000), orderedInterval (30545201643 / 1000000000000) (30545201644 / 1000000000000))) = true
  rfl'

theorem compactCertificate481_stateChecks2 :
    compactCertificate481.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 130 12 (325625551823019 / 800000000000)) (orderedInterval (-22003488186 / 1000000000000) (-22003485765 / 1000000000000), orderedInterval (32888869200 / 1000000000000) (32888871621 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 222 12 (557964933158487 / 800000000000)) (orderedInterval (21836726982 / 1000000000000) (21836726983 / 1000000000000), orderedInterval (20863311567 / 1000000000000) (20863311568 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 164 12 (410994444387333 / 800000000000)) (orderedInterval (-22488302170 / 1000000000000) (-22488298046 / 1000000000000), orderedInterval (27104273486 / 1000000000000) (27104277610 / 1000000000000))) = true
  rfl'

theorem compactCertificate481_stateChecks3 :
    compactCertificate481.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 251 12 (630571169654859 / 800000000000)) (orderedInterval (-12602707356 / 1000000000000) (-12602707355 / 1000000000000), orderedInterval (-25464454847 / 1000000000000) (-25464454846 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 145 12 (364060434543411 / 800000000000)) (orderedInterval (-12110463850 / 1000000000000) (-12110463849 / 1000000000000), orderedInterval (-35374112753 / 1000000000000) (-35374112752 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 257 12 (646031629747599 / 800000000000)) (orderedInterval (-22598924506 / 1000000000000) (-22598924504 / 1000000000000), orderedInterval (-16648347909 / 1000000000000) (-16648347907 / 1000000000000))) = true
  rfl'

theorem compactCertificate481_stateChecks4 :
    compactCertificate481.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 240 12 (603606549529131 / 800000000000)) (orderedInterval (28074047978 / 1000000000000) (28074048071 / 1000000000000), orderedInterval (7438090180 / 1000000000000) (7438090273 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 171 12 (430762115325723 / 800000000000)) (orderedInterval (-30891522574 / 1000000000000) (-30891452858 / 1000000000000), orderedInterval (15129279180 / 1000000000000) (15129348896 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 194 12 (488438327734317 / 800000000000)) (orderedInterval (30911604945 / 1000000000000) (30911627720 / 1000000000000), orderedInterval (-9362031253 / 1000000000000) (-9362008478 / 1000000000000))) = true
  rfl'

theorem compactCertificate481_stateChecks5 :
    compactCertificate481.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 162 12 (407208955409373 / 800000000000)) (orderedInterval (26762855267 / 1000000000000) (26762855268 / 1000000000000), orderedInterval (23091852156 / 1000000000000) (23091852157 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 143 12 (359781461512833 / 800000000000)) (orderedInterval (-35869476221 / 1000000000000) (-35869476216 / 1000000000000), orderedInterval (-11315731344 / 1000000000000) (-11315731339 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 208 12 (104278690702467 / 160000000000)) (orderedInterval (-24945768858 / 1000000000000) (-24945748073 / 1000000000000), orderedInterval (18847471116 / 1000000000000) (18847491901 / 1000000000000))) = true
  rfl'

theorem compactCertificate481_stateChecks6 :
    compactCertificate481.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 115 12 (288440346369849 / 800000000000)) (orderedInterval (-2197876621 / 1000000000000) (-2197876620 / 1000000000000), orderedInterval (-41959549456 / 1000000000000) (-41959549455 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 97 12 (244514076007089 / 800000000000)) (orderedInterval (-45297762068 / 1000000000000) (-45297761360 / 1000000000000), orderedInterval (5641834465 / 1000000000000) (5641835173 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 61 12 (153005555612667 / 800000000000)) (orderedInterval (-22707981022 / 1000000000000) (-22707981021 / 1000000000000), orderedInterval (-52978031703 / 1000000000000) (-52978031702 / 1000000000000))) = true
  rfl'

theorem compactCertificate481_stateChecks7 :
    compactCertificate481.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 33 12 (82286896681989 / 800000000000)) (orderedInterval (2340425496 / 1000000000000) (2340425506 / 1000000000000), orderedInterval (-78648933543 / 1000000000000) (-78648933533 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 89 12 (223424931572967 / 800000000000)) (orderedInterval (-21382565769 / 1000000000000) (-21382565768 / 1000000000000), orderedInterval (-42649915998 / 1000000000000) (-42649915997 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 121 12 (305067642877959 / 800000000000)) (orderedInterval (-37372251388 / 1000000000000) (-37372227154 / 1000000000000), orderedInterval (16564643792 / 1000000000000) (16564668026 / 1000000000000))) = true
  rfl'

theorem compactCertificate481_stateChecks8 :
    compactCertificate481.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (128994444387333 / 800000000000)) (orderedInterval (-61097879187 / 1000000000000) (-61097878037 / 1000000000000), orderedInterval (14860242010 / 1000000000000) (14860243160 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 209 12 (524355254877093 / 800000000000)) (orderedInterval (11083352448 / 1000000000000) (11083352472 / 1000000000000), orderedInterval (-29136441339 / 1000000000000) (-29136441315 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 139 12 (350245009504587 / 800000000000)) (orderedInterval (-35960072518 / 1000000000000) (-35960057191 / 1000000000000), orderedInterval (12729085264 / 1000000000000) (12729100591 / 1000000000000))) = true
  rfl'

theorem compactCertificate481_states : ∀ j,
    BesselStateValid (compactCertificate481.point j) (compactCertificate481.state j) :=
  compactCertificate481.statesValid_of_checks3 compactCertificate481_stateChecks0
    compactCertificate481_stateChecks1 compactCertificate481_stateChecks2
    compactCertificate481_stateChecks3 compactCertificate481_stateChecks4
    compactCertificate481_stateChecks5 compactCertificate481_stateChecks6
    compactCertificate481_stateChecks7 compactCertificate481_stateChecks8

theorem compactCertificate481_chunkChecks0_0 :
    compactCertificate481.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (705 / 2) 0 (IntervalRat.scale (705 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (42056553540 / 1000000000000) (42056553565 / 1000000000000), orderedInterval (6044286775 / 1000000000000) (6044286801 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (207719923654041 / 800000000000) 0 (IntervalRat.scale (705 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (15452358264 / 1000000000000) (15452358482 / 1000000000000), orderedInterval (-47073005594 / 1000000000000) (-47073005377 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (67172355434553 / 160000000000) 0 (IntervalRat.scale (705 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-13757683248 / 1000000000000) (-13757683117 / 1000000000000), orderedInterval (36445935072 / 1000000000000) (36445935203 / 1000000000000)))) (orderedInterval (16006415002 / 1000000000000) (16006415046 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (60612155661387 / 800000000000) 0 (IntervalRat.scale (705 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (83694827457 / 1000000000000) (83694827458 / 1000000000000), orderedInterval (36832045451 / 1000000000000) (36832045452 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (162812775911439 / 800000000000) 0 (IntervalRat.scale (705 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-5429527915 / 1000000000000) (-5429527914 / 1000000000000), orderedInterval (-55652060223 / 1000000000000) (-55652060222 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (442068358194963 / 800000000000) 0 (IntervalRat.scale (705 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (14773251432 / 1000000000000) (14773251433 / 1000000000000), orderedInterval (30545201643 / 1000000000000) (30545201644 / 1000000000000)))) (orderedInterval (-2156496245 / 1000000000000) (-2156496202 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (325625551823019 / 800000000000) 0 (IntervalRat.scale (705 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-22003488186 / 1000000000000) (-22003485765 / 1000000000000), orderedInterval (32888869200 / 1000000000000) (32888871621 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (557964933158487 / 800000000000) 0 (IntervalRat.scale (705 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (21836726982 / 1000000000000) (21836726983 / 1000000000000), orderedInterval (20863311567 / 1000000000000) (20863311568 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (410994444387333 / 800000000000) 0 (IntervalRat.scale (705 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-22488302170 / 1000000000000) (-22488298046 / 1000000000000), orderedInterval (27104273486 / 1000000000000) (27104277610 / 1000000000000)))) (orderedInterval (-1217029933 / 1000000000000) (-1217029813 / 1000000000000))) = true
  rfl'

theorem compactCertificate481_chunkChecks0_1 :
    compactCertificate481.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (630571169654859 / 800000000000) 0 (IntervalRat.scale (705 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-12602707356 / 1000000000000) (-12602707355 / 1000000000000), orderedInterval (-25464454847 / 1000000000000) (-25464454846 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (364060434543411 / 800000000000) 0 (IntervalRat.scale (705 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-12110463850 / 1000000000000) (-12110463849 / 1000000000000), orderedInterval (-35374112753 / 1000000000000) (-35374112752 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (646031629747599 / 800000000000) 0 (IntervalRat.scale (705 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-22598924506 / 1000000000000) (-22598924504 / 1000000000000), orderedInterval (-16648347909 / 1000000000000) (-16648347907 / 1000000000000)))) (orderedInterval (-1870507124 / 1000000000000) (-1870506983 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (603606549529131 / 800000000000) 0 (IntervalRat.scale (705 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (28074047978 / 1000000000000) (28074048071 / 1000000000000), orderedInterval (7438090180 / 1000000000000) (7438090273 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (430762115325723 / 800000000000) 0 (IntervalRat.scale (705 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-30891522574 / 1000000000000) (-30891452858 / 1000000000000), orderedInterval (15129279180 / 1000000000000) (15129348896 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (488438327734317 / 800000000000) 0 (IntervalRat.scale (705 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (30911604945 / 1000000000000) (30911627720 / 1000000000000), orderedInterval (-9362031253 / 1000000000000) (-9362008478 / 1000000000000)))) (orderedInterval (-3584444776 / 1000000000000) (-3584438025 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (407208955409373 / 800000000000) 0 (IntervalRat.scale (705 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (26762855267 / 1000000000000) (26762855268 / 1000000000000), orderedInterval (23091852156 / 1000000000000) (23091852157 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (359781461512833 / 800000000000) 0 (IntervalRat.scale (705 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-35869476221 / 1000000000000) (-35869476216 / 1000000000000), orderedInterval (-11315731344 / 1000000000000) (-11315731339 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (104278690702467 / 160000000000) 0 (IntervalRat.scale (705 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-24945768858 / 1000000000000) (-24945748073 / 1000000000000), orderedInterval (18847471116 / 1000000000000) (18847491901 / 1000000000000)))) (orderedInterval (1723029315 / 1000000000000) (1723029882 / 1000000000000))) = true
  rfl'

theorem compactCertificate481_chunkChecks0_2 :
    compactCertificate481.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (288440346369849 / 800000000000) 0 (IntervalRat.scale (705 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-2197876621 / 1000000000000) (-2197876620 / 1000000000000), orderedInterval (-41959549456 / 1000000000000) (-41959549455 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (244514076007089 / 800000000000) 0 (IntervalRat.scale (705 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-45297762068 / 1000000000000) (-45297761360 / 1000000000000), orderedInterval (5641834465 / 1000000000000) (5641835173 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (153005555612667 / 800000000000) 0 (IntervalRat.scale (705 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-22707981022 / 1000000000000) (-22707981021 / 1000000000000), orderedInterval (-52978031703 / 1000000000000) (-52978031702 / 1000000000000)))) (orderedInterval (2176010639 / 1000000000000) (2176010768 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (82286896681989 / 800000000000) 0 (IntervalRat.scale (705 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (2340425496 / 1000000000000) (2340425506 / 1000000000000), orderedInterval (-78648933543 / 1000000000000) (-78648933533 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (223424931572967 / 800000000000) 0 (IntervalRat.scale (705 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-21382565769 / 1000000000000) (-21382565768 / 1000000000000), orderedInterval (-42649915998 / 1000000000000) (-42649915997 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (305067642877959 / 800000000000) 0 (IntervalRat.scale (705 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-37372251388 / 1000000000000) (-37372227154 / 1000000000000), orderedInterval (16564643792 / 1000000000000) (16564668026 / 1000000000000)))) (orderedInterval (3306052325 / 1000000000000) (3306054225 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (128994444387333 / 800000000000) 0 (IntervalRat.scale (705 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-61097879187 / 1000000000000) (-61097878037 / 1000000000000), orderedInterval (14860242010 / 1000000000000) (14860243160 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (524355254877093 / 800000000000) 0 (IntervalRat.scale (705 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (11083352448 / 1000000000000) (11083352472 / 1000000000000), orderedInterval (-29136441339 / 1000000000000) (-29136441315 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (350245009504587 / 800000000000) 0 (IntervalRat.scale (705 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-35960072518 / 1000000000000) (-35960057191 / 1000000000000), orderedInterval (12729085264 / 1000000000000) (12729100591 / 1000000000000)))) (orderedInterval (5476537950 / 1000000000000) (5476540933 / 1000000000000))) = true
  rfl'

theorem compactCertificate481_chunkChecks0 :
    compactCertificate481.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate481.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate481_chunkChecks0_0
    compactCertificate481_chunkChecks0_1 compactCertificate481_chunkChecks0_2

theorem compactCertificate481_chunkChecks1_0 :
    compactCertificate481.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (705 / 2) 1 (IntervalRat.scale (705 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (42056553540 / 1000000000000) (42056553565 / 1000000000000), orderedInterval (6044286775 / 1000000000000) (6044286801 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (207719923654041 / 800000000000) 1 (IntervalRat.scale (705 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (15452358264 / 1000000000000) (15452358482 / 1000000000000), orderedInterval (-47073005594 / 1000000000000) (-47073005377 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (67172355434553 / 160000000000) 1 (IntervalRat.scale (705 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-13757683248 / 1000000000000) (-13757683117 / 1000000000000), orderedInterval (36445935072 / 1000000000000) (36445935203 / 1000000000000)))) (orderedInterval (4619828399 / 1000000000000) (4619828448 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (60612155661387 / 800000000000) 1 (IntervalRat.scale (705 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (83694827457 / 1000000000000) (83694827458 / 1000000000000), orderedInterval (36832045451 / 1000000000000) (36832045452 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (162812775911439 / 800000000000) 1 (IntervalRat.scale (705 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-5429527915 / 1000000000000) (-5429527914 / 1000000000000), orderedInterval (-55652060223 / 1000000000000) (-55652060222 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (442068358194963 / 800000000000) 1 (IntervalRat.scale (705 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (14773251432 / 1000000000000) (14773251433 / 1000000000000), orderedInterval (30545201643 / 1000000000000) (30545201644 / 1000000000000)))) (orderedInterval (-4663038895 / 1000000000000) (-4663038846 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (325625551823019 / 800000000000) 1 (IntervalRat.scale (705 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-22003488186 / 1000000000000) (-22003485765 / 1000000000000), orderedInterval (32888869200 / 1000000000000) (32888871621 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (557964933158487 / 800000000000) 1 (IntervalRat.scale (705 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (21836726982 / 1000000000000) (21836726983 / 1000000000000), orderedInterval (20863311567 / 1000000000000) (20863311568 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (410994444387333 / 800000000000) 1 (IntervalRat.scale (705 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-22488302170 / 1000000000000) (-22488298046 / 1000000000000), orderedInterval (27104273486 / 1000000000000) (27104277610 / 1000000000000)))) (orderedInterval (-318546786 / 1000000000000) (-318546606 / 1000000000000))) = true
  rfl'

theorem compactCertificate481_chunkChecks1_1 :
    compactCertificate481.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (630571169654859 / 800000000000) 1 (IntervalRat.scale (705 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-12602707356 / 1000000000000) (-12602707355 / 1000000000000), orderedInterval (-25464454847 / 1000000000000) (-25464454846 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (364060434543411 / 800000000000) 1 (IntervalRat.scale (705 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-12110463850 / 1000000000000) (-12110463849 / 1000000000000), orderedInterval (-35374112753 / 1000000000000) (-35374112752 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (646031629747599 / 800000000000) 1 (IntervalRat.scale (705 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-22598924506 / 1000000000000) (-22598924504 / 1000000000000), orderedInterval (-16648347909 / 1000000000000) (-16648347907 / 1000000000000)))) (orderedInterval (1312223320 / 1000000000000) (1312223611 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (603606549529131 / 800000000000) 1 (IntervalRat.scale (705 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (28074047978 / 1000000000000) (28074048071 / 1000000000000), orderedInterval (7438090180 / 1000000000000) (7438090273 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (430762115325723 / 800000000000) 1 (IntervalRat.scale (705 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-30891522574 / 1000000000000) (-30891452858 / 1000000000000), orderedInterval (15129279180 / 1000000000000) (15129348896 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (488438327734317 / 800000000000) 1 (IntervalRat.scale (705 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (30911604945 / 1000000000000) (30911627720 / 1000000000000), orderedInterval (-9362031253 / 1000000000000) (-9362008478 / 1000000000000)))) (orderedInterval (1980020580 / 1000000000000) (1980030922 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (407208955409373 / 800000000000) 1 (IntervalRat.scale (705 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (26762855267 / 1000000000000) (26762855268 / 1000000000000), orderedInterval (23091852156 / 1000000000000) (23091852157 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (359781461512833 / 800000000000) 1 (IntervalRat.scale (705 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-35869476221 / 1000000000000) (-35869476216 / 1000000000000), orderedInterval (-11315731344 / 1000000000000) (-11315731339 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (104278690702467 / 160000000000) 1 (IntervalRat.scale (705 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-24945768858 / 1000000000000) (-24945748073 / 1000000000000), orderedInterval (18847471116 / 1000000000000) (18847491901 / 1000000000000)))) (orderedInterval (2103455779 / 1000000000000) (2103456813 / 1000000000000))) = true
  rfl'

theorem compactCertificate481_chunkChecks1_2 :
    compactCertificate481.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (288440346369849 / 800000000000) 1 (IntervalRat.scale (705 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-2197876621 / 1000000000000) (-2197876620 / 1000000000000), orderedInterval (-41959549456 / 1000000000000) (-41959549455 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (244514076007089 / 800000000000) 1 (IntervalRat.scale (705 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-45297762068 / 1000000000000) (-45297761360 / 1000000000000), orderedInterval (5641834465 / 1000000000000) (5641835173 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (153005555612667 / 800000000000) 1 (IntervalRat.scale (705 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-22707981022 / 1000000000000) (-22707981021 / 1000000000000), orderedInterval (-52978031703 / 1000000000000) (-52978031702 / 1000000000000)))) (orderedInterval (5649573047 / 1000000000000) (5649573164 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (82286896681989 / 800000000000) 1 (IntervalRat.scale (705 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (2340425496 / 1000000000000) (2340425506 / 1000000000000), orderedInterval (-78648933543 / 1000000000000) (-78648933533 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (223424931572967 / 800000000000) 1 (IntervalRat.scale (705 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-21382565769 / 1000000000000) (-21382565768 / 1000000000000), orderedInterval (-42649915998 / 1000000000000) (-42649915997 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (305067642877959 / 800000000000) 1 (IntervalRat.scale (705 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-37372251388 / 1000000000000) (-37372227154 / 1000000000000), orderedInterval (16564643792 / 1000000000000) (16564668026 / 1000000000000)))) (orderedInterval (-182965027 / 1000000000000) (-182962979 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (128994444387333 / 800000000000) 1 (IntervalRat.scale (705 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-61097879187 / 1000000000000) (-61097878037 / 1000000000000), orderedInterval (14860242010 / 1000000000000) (14860243160 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (524355254877093 / 800000000000) 1 (IntervalRat.scale (705 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (11083352448 / 1000000000000) (11083352472 / 1000000000000), orderedInterval (-29136441339 / 1000000000000) (-29136441315 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (350245009504587 / 800000000000) 1 (IntervalRat.scale (705 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-35960072518 / 1000000000000) (-35960057191 / 1000000000000), orderedInterval (12729085264 / 1000000000000) (12729100591 / 1000000000000)))) (orderedInterval (1484763648 / 1000000000000) (1484767363 / 1000000000000))) = true
  rfl'

theorem compactCertificate481_chunkChecks1 :
    compactCertificate481.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate481.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate481_chunkChecks1_0
    compactCertificate481_chunkChecks1_1 compactCertificate481_chunkChecks1_2

theorem compactCertificate481_chunkChecks2_0 :
    compactCertificate481.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (705 / 2) 2 (IntervalRat.scale (705 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (42056553540 / 1000000000000) (42056553565 / 1000000000000), orderedInterval (6044286775 / 1000000000000) (6044286801 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (207719923654041 / 800000000000) 2 (IntervalRat.scale (705 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (15452358264 / 1000000000000) (15452358482 / 1000000000000), orderedInterval (-47073005594 / 1000000000000) (-47073005377 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (67172355434553 / 160000000000) 2 (IntervalRat.scale (705 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-13757683248 / 1000000000000) (-13757683117 / 1000000000000), orderedInterval (36445935072 / 1000000000000) (36445935203 / 1000000000000)))) (orderedInterval (-15615812736 / 1000000000000) (-15615812682 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (60612155661387 / 800000000000) 2 (IntervalRat.scale (705 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (83694827457 / 1000000000000) (83694827458 / 1000000000000), orderedInterval (36832045451 / 1000000000000) (36832045452 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (162812775911439 / 800000000000) 2 (IntervalRat.scale (705 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-5429527915 / 1000000000000) (-5429527914 / 1000000000000), orderedInterval (-55652060223 / 1000000000000) (-55652060222 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (442068358194963 / 800000000000) 2 (IntervalRat.scale (705 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (14773251432 / 1000000000000) (14773251433 / 1000000000000), orderedInterval (30545201643 / 1000000000000) (30545201644 / 1000000000000)))) (orderedInterval (2702109652 / 1000000000000) (2702109720 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (325625551823019 / 800000000000) 2 (IntervalRat.scale (705 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-22003488186 / 1000000000000) (-22003485765 / 1000000000000), orderedInterval (32888869200 / 1000000000000) (32888871621 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (557964933158487 / 800000000000) 2 (IntervalRat.scale (705 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (21836726982 / 1000000000000) (21836726983 / 1000000000000), orderedInterval (20863311567 / 1000000000000) (20863311568 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (410994444387333 / 800000000000) 2 (IntervalRat.scale (705 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-22488302170 / 1000000000000) (-22488298046 / 1000000000000), orderedInterval (27104273486 / 1000000000000) (27104277610 / 1000000000000)))) (orderedInterval (3792123631 / 1000000000000) (3792123905 / 1000000000000))) = true
  rfl'

theorem compactCertificate481_chunkChecks2_1 :
    compactCertificate481.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (630571169654859 / 800000000000) 2 (IntervalRat.scale (705 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-12602707356 / 1000000000000) (-12602707355 / 1000000000000), orderedInterval (-25464454847 / 1000000000000) (-25464454846 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (364060434543411 / 800000000000) 2 (IntervalRat.scale (705 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-12110463850 / 1000000000000) (-12110463849 / 1000000000000), orderedInterval (-35374112753 / 1000000000000) (-35374112752 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (646031629747599 / 800000000000) 2 (IntervalRat.scale (705 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-22598924506 / 1000000000000) (-22598924504 / 1000000000000), orderedInterval (-16648347909 / 1000000000000) (-16648347907 / 1000000000000)))) (orderedInterval (7155179896 / 1000000000000) (7155180520 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (603606549529131 / 800000000000) 2 (IntervalRat.scale (705 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (28074047978 / 1000000000000) (28074048071 / 1000000000000), orderedInterval (7438090180 / 1000000000000) (7438090273 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (430762115325723 / 800000000000) 2 (IntervalRat.scale (705 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-30891522574 / 1000000000000) (-30891452858 / 1000000000000), orderedInterval (15129279180 / 1000000000000) (15129348896 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (488438327734317 / 800000000000) 2 (IntervalRat.scale (705 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (30911604945 / 1000000000000) (30911627720 / 1000000000000), orderedInterval (-9362031253 / 1000000000000) (-9362008478 / 1000000000000)))) (orderedInterval (9601792239 / 1000000000000) (9601808117 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (407208955409373 / 800000000000) 2 (IntervalRat.scale (705 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (26762855267 / 1000000000000) (26762855268 / 1000000000000), orderedInterval (23091852156 / 1000000000000) (23091852157 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (359781461512833 / 800000000000) 2 (IntervalRat.scale (705 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-35869476221 / 1000000000000) (-35869476216 / 1000000000000), orderedInterval (-11315731344 / 1000000000000) (-11315731339 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (104278690702467 / 160000000000) 2 (IntervalRat.scale (705 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-24945768858 / 1000000000000) (-24945748073 / 1000000000000), orderedInterval (18847471116 / 1000000000000) (18847491901 / 1000000000000)))) (orderedInterval (-1808166358 / 1000000000000) (-1808164462 / 1000000000000))) = true
  rfl'

theorem compactCertificate481_chunkChecks2_2 :
    compactCertificate481.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (288440346369849 / 800000000000) 2 (IntervalRat.scale (705 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-2197876621 / 1000000000000) (-2197876620 / 1000000000000), orderedInterval (-41959549456 / 1000000000000) (-41959549455 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (244514076007089 / 800000000000) 2 (IntervalRat.scale (705 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-45297762068 / 1000000000000) (-45297761360 / 1000000000000), orderedInterval (5641834465 / 1000000000000) (5641835173 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (153005555612667 / 800000000000) 2 (IntervalRat.scale (705 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-22707981022 / 1000000000000) (-22707981021 / 1000000000000), orderedInterval (-52978031703 / 1000000000000) (-52978031702 / 1000000000000)))) (orderedInterval (-2093592798 / 1000000000000) (-2093592689 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (82286896681989 / 800000000000) 2 (IntervalRat.scale (705 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (2340425496 / 1000000000000) (2340425506 / 1000000000000), orderedInterval (-78648933543 / 1000000000000) (-78648933533 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (223424931572967 / 800000000000) 2 (IntervalRat.scale (705 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-21382565769 / 1000000000000) (-21382565768 / 1000000000000), orderedInterval (-42649915998 / 1000000000000) (-42649915997 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (305067642877959 / 800000000000) 2 (IntervalRat.scale (705 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-37372251388 / 1000000000000) (-37372227154 / 1000000000000), orderedInterval (16564643792 / 1000000000000) (16564668026 / 1000000000000)))) (orderedInterval (-3652220336 / 1000000000000) (-3652218119 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (128994444387333 / 800000000000) 2 (IntervalRat.scale (705 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-61097879187 / 1000000000000) (-61097878037 / 1000000000000), orderedInterval (14860242010 / 1000000000000) (14860243160 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (524355254877093 / 800000000000) 2 (IntervalRat.scale (705 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (11083352448 / 1000000000000) (11083352472 / 1000000000000), orderedInterval (-29136441339 / 1000000000000) (-29136441315 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (350245009504587 / 800000000000) 2 (IntervalRat.scale (705 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-35960072518 / 1000000000000) (-35960057191 / 1000000000000), orderedInterval (12729085264 / 1000000000000) (12729100591 / 1000000000000)))) (orderedInterval (-7215676198 / 1000000000000) (-7215671541 / 1000000000000))) = true
  rfl'

theorem compactCertificate481_chunkChecks2 :
    compactCertificate481.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate481.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate481_chunkChecks2_0
    compactCertificate481_chunkChecks2_1 compactCertificate481_chunkChecks2_2

theorem compactCertificate481_chunkChecks3_0 :
    compactCertificate481.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (705 / 2) 3 (IntervalRat.scale (705 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (42056553540 / 1000000000000) (42056553565 / 1000000000000), orderedInterval (6044286775 / 1000000000000) (6044286801 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (207719923654041 / 800000000000) 3 (IntervalRat.scale (705 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (15452358264 / 1000000000000) (15452358482 / 1000000000000), orderedInterval (-47073005594 / 1000000000000) (-47073005377 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (67172355434553 / 160000000000) 3 (IntervalRat.scale (705 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-13757683248 / 1000000000000) (-13757683117 / 1000000000000), orderedInterval (36445935072 / 1000000000000) (36445935203 / 1000000000000)))) (orderedInterval (-5789222585 / 1000000000000) (-5789222524 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (60612155661387 / 800000000000) 3 (IntervalRat.scale (705 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (83694827457 / 1000000000000) (83694827458 / 1000000000000), orderedInterval (36832045451 / 1000000000000) (36832045452 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (162812775911439 / 800000000000) 3 (IntervalRat.scale (705 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-5429527915 / 1000000000000) (-5429527914 / 1000000000000), orderedInterval (-55652060223 / 1000000000000) (-55652060222 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (442068358194963 / 800000000000) 3 (IntervalRat.scale (705 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (14773251432 / 1000000000000) (14773251433 / 1000000000000), orderedInterval (30545201643 / 1000000000000) (30545201644 / 1000000000000)))) (orderedInterval (8752398034 / 1000000000000) (8752398134 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (325625551823019 / 800000000000) 3 (IntervalRat.scale (705 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-22003488186 / 1000000000000) (-22003485765 / 1000000000000), orderedInterval (32888869200 / 1000000000000) (32888871621 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (557964933158487 / 800000000000) 3 (IntervalRat.scale (705 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (21836726982 / 1000000000000) (21836726983 / 1000000000000), orderedInterval (20863311567 / 1000000000000) (20863311568 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (410994444387333 / 800000000000) 3 (IntervalRat.scale (705 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-22488302170 / 1000000000000) (-22488298046 / 1000000000000), orderedInterval (27104273486 / 1000000000000) (27104277610 / 1000000000000)))) (orderedInterval (2945938052 / 1000000000000) (2945938473 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate481_chunkChecks3_1 :
    compactCertificate481.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (630571169654859 / 800000000000) 3 (IntervalRat.scale (705 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-12602707356 / 1000000000000) (-12602707355 / 1000000000000), orderedInterval (-25464454847 / 1000000000000) (-25464454846 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (364060434543411 / 800000000000) 3 (IntervalRat.scale (705 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-12110463850 / 1000000000000) (-12110463849 / 1000000000000), orderedInterval (-35374112753 / 1000000000000) (-35374112752 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (646031629747599 / 800000000000) 3 (IntervalRat.scale (705 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-22598924506 / 1000000000000) (-22598924504 / 1000000000000), orderedInterval (-16648347909 / 1000000000000) (-16648347907 / 1000000000000)))) (orderedInterval (-16514481076 / 1000000000000) (-16514479711 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (603606549529131 / 800000000000) 3 (IntervalRat.scale (705 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (28074047978 / 1000000000000) (28074048071 / 1000000000000), orderedInterval (7438090180 / 1000000000000) (7438090273 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (430762115325723 / 800000000000) 3 (IntervalRat.scale (705 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-30891522574 / 1000000000000) (-30891452858 / 1000000000000), orderedInterval (15129279180 / 1000000000000) (15129348896 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (488438327734317 / 800000000000) 3 (IntervalRat.scale (705 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (30911604945 / 1000000000000) (30911627720 / 1000000000000), orderedInterval (-9362031253 / 1000000000000) (-9362008478 / 1000000000000)))) (orderedInterval (-4055826797 / 1000000000000) (-4055802448 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (407208955409373 / 800000000000) 3 (IntervalRat.scale (705 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (26762855267 / 1000000000000) (26762855268 / 1000000000000), orderedInterval (23091852156 / 1000000000000) (23091852157 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (359781461512833 / 800000000000) 3 (IntervalRat.scale (705 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-35869476221 / 1000000000000) (-35869476216 / 1000000000000), orderedInterval (-11315731344 / 1000000000000) (-11315731339 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (104278690702467 / 160000000000) 3 (IntervalRat.scale (705 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-24945768858 / 1000000000000) (-24945748073 / 1000000000000), orderedInterval (18847471116 / 1000000000000) (18847491901 / 1000000000000)))) (orderedInterval (-5192594351 / 1000000000000) (-5192590870 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate481_chunkChecks3_2 :
    compactCertificate481.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (288440346369849 / 800000000000) 3 (IntervalRat.scale (705 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-2197876621 / 1000000000000) (-2197876620 / 1000000000000), orderedInterval (-41959549456 / 1000000000000) (-41959549455 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (244514076007089 / 800000000000) 3 (IntervalRat.scale (705 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-45297762068 / 1000000000000) (-45297761360 / 1000000000000), orderedInterval (5641834465 / 1000000000000) (5641835173 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (153005555612667 / 800000000000) 3 (IntervalRat.scale (705 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-22707981022 / 1000000000000) (-22707981021 / 1000000000000), orderedInterval (-52978031703 / 1000000000000) (-52978031702 / 1000000000000)))) (orderedInterval (-6689629013 / 1000000000000) (-6689628911 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (82286896681989 / 800000000000) 3 (IntervalRat.scale (705 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (2340425496 / 1000000000000) (2340425506 / 1000000000000), orderedInterval (-78648933543 / 1000000000000) (-78648933533 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (223424931572967 / 800000000000) 3 (IntervalRat.scale (705 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-21382565769 / 1000000000000) (-21382565768 / 1000000000000), orderedInterval (-42649915998 / 1000000000000) (-42649915997 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (305067642877959 / 800000000000) 3 (IntervalRat.scale (705 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-37372251388 / 1000000000000) (-37372227154 / 1000000000000), orderedInterval (16564643792 / 1000000000000) (16564668026 / 1000000000000)))) (orderedInterval (1100270176 / 1000000000000) (1100272573 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (128994444387333 / 800000000000) 3 (IntervalRat.scale (705 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-61097879187 / 1000000000000) (-61097878037 / 1000000000000), orderedInterval (14860242010 / 1000000000000) (14860243160 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (524355254877093 / 800000000000) 3 (IntervalRat.scale (705 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (11083352448 / 1000000000000) (11083352472 / 1000000000000), orderedInterval (-29136441339 / 1000000000000) (-29136441315 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (350245009504587 / 800000000000) 3 (IntervalRat.scale (705 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-35960072518 / 1000000000000) (-35960057191 / 1000000000000), orderedInterval (12729085264 / 1000000000000) (12729100591 / 1000000000000)))) (orderedInterval (-10659912284 / 1000000000000) (-10659906436 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate481_chunkChecks3 :
    compactCertificate481.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate481.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate481_chunkChecks3_0
    compactCertificate481_chunkChecks3_1 compactCertificate481_chunkChecks3_2

theorem compactCertificate481_chunkChecks4_0 :
    compactCertificate481.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (705 / 2) 4 (IntervalRat.scale (705 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (42056553540 / 1000000000000) (42056553565 / 1000000000000), orderedInterval (6044286775 / 1000000000000) (6044286801 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (207719923654041 / 800000000000) 4 (IntervalRat.scale (705 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (15452358264 / 1000000000000) (15452358482 / 1000000000000), orderedInterval (-47073005594 / 1000000000000) (-47073005377 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (67172355434553 / 160000000000) 4 (IntervalRat.scale (705 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-13757683248 / 1000000000000) (-13757683117 / 1000000000000), orderedInterval (36445935072 / 1000000000000) (36445935203 / 1000000000000)))) (orderedInterval (15120465884 / 1000000000000) (15120465953 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (60612155661387 / 800000000000) 4 (IntervalRat.scale (705 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (83694827457 / 1000000000000) (83694827458 / 1000000000000), orderedInterval (36832045451 / 1000000000000) (36832045452 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (162812775911439 / 800000000000) 4 (IntervalRat.scale (705 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-5429527915 / 1000000000000) (-5429527914 / 1000000000000), orderedInterval (-55652060223 / 1000000000000) (-55652060222 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (442068358194963 / 800000000000) 4 (IntervalRat.scale (705 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (14773251432 / 1000000000000) (14773251433 / 1000000000000), orderedInterval (30545201643 / 1000000000000) (30545201644 / 1000000000000)))) (orderedInterval (-6415857011 / 1000000000000) (-6415856857 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (325625551823019 / 800000000000) 4 (IntervalRat.scale (705 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-22003488186 / 1000000000000) (-22003485765 / 1000000000000), orderedInterval (32888869200 / 1000000000000) (32888871621 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (557964933158487 / 800000000000) 4 (IntervalRat.scale (705 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (21836726982 / 1000000000000) (21836726983 / 1000000000000), orderedInterval (20863311567 / 1000000000000) (20863311568 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (410994444387333 / 800000000000) 4 (IntervalRat.scale (705 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-22488302170 / 1000000000000) (-22488298046 / 1000000000000), orderedInterval (27104273486 / 1000000000000) (27104277610 / 1000000000000)))) (orderedInterval (-12791432120 / 1000000000000) (-12791431462 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate481_chunkChecks4_1 :
    compactCertificate481.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (630571169654859 / 800000000000) 4 (IntervalRat.scale (705 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-12602707356 / 1000000000000) (-12602707355 / 1000000000000), orderedInterval (-25464454847 / 1000000000000) (-25464454846 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (364060434543411 / 800000000000) 4 (IntervalRat.scale (705 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-12110463850 / 1000000000000) (-12110463849 / 1000000000000), orderedInterval (-35374112753 / 1000000000000) (-35374112752 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (646031629747599 / 800000000000) 4 (IntervalRat.scale (705 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-22598924506 / 1000000000000) (-22598924504 / 1000000000000), orderedInterval (-16648347909 / 1000000000000) (-16648347907 / 1000000000000)))) (orderedInterval (-34900322875 / 1000000000000) (-34900319842 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (603606549529131 / 800000000000) 4 (IntervalRat.scale (705 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (28074047978 / 1000000000000) (28074048071 / 1000000000000), orderedInterval (7438090180 / 1000000000000) (7438090273 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (430762115325723 / 800000000000) 4 (IntervalRat.scale (705 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-30891522574 / 1000000000000) (-30891452858 / 1000000000000), orderedInterval (15129279180 / 1000000000000) (15129348896 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (488438327734317 / 800000000000) 4 (IntervalRat.scale (705 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (30911604945 / 1000000000000) (30911627720 / 1000000000000), orderedInterval (-9362031253 / 1000000000000) (-9362008478 / 1000000000000)))) (orderedInterval (-27927436812 / 1000000000000) (-27927399378 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (407208955409373 / 800000000000) 4 (IntervalRat.scale (705 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (26762855267 / 1000000000000) (26762855268 / 1000000000000), orderedInterval (23091852156 / 1000000000000) (23091852157 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (359781461512833 / 800000000000) 4 (IntervalRat.scale (705 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-35869476221 / 1000000000000) (-35869476216 / 1000000000000), orderedInterval (-11315731344 / 1000000000000) (-11315731339 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (104278690702467 / 160000000000) 4 (IntervalRat.scale (705 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-24945768858 / 1000000000000) (-24945748073 / 1000000000000), orderedInterval (18847471116 / 1000000000000) (18847491901 / 1000000000000)))) (orderedInterval (-652289569 / 1000000000000) (-652283152 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate481_chunkChecks4_2 :
    compactCertificate481.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (288440346369849 / 800000000000) 4 (IntervalRat.scale (705 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-2197876621 / 1000000000000) (-2197876620 / 1000000000000), orderedInterval (-41959549456 / 1000000000000) (-41959549455 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (244514076007089 / 800000000000) 4 (IntervalRat.scale (705 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-45297762068 / 1000000000000) (-45297761360 / 1000000000000), orderedInterval (5641834465 / 1000000000000) (5641835173 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (153005555612667 / 800000000000) 4 (IntervalRat.scale (705 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-22707981022 / 1000000000000) (-22707981021 / 1000000000000), orderedInterval (-52978031703 / 1000000000000) (-52978031702 / 1000000000000)))) (orderedInterval (1807660605 / 1000000000000) (1807660703 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (82286896681989 / 800000000000) 4 (IntervalRat.scale (705 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (2340425496 / 1000000000000) (2340425506 / 1000000000000), orderedInterval (-78648933543 / 1000000000000) (-78648933533 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (223424931572967 / 800000000000) 4 (IntervalRat.scale (705 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-21382565769 / 1000000000000) (-21382565768 / 1000000000000), orderedInterval (-42649915998 / 1000000000000) (-42649915997 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (305067642877959 / 800000000000) 4 (IntervalRat.scale (705 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-37372251388 / 1000000000000) (-37372227154 / 1000000000000), orderedInterval (16564643792 / 1000000000000) (16564668026 / 1000000000000)))) (orderedInterval (4107270423 / 1000000000000) (4107273021 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (128994444387333 / 800000000000) 4 (IntervalRat.scale (705 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-61097879187 / 1000000000000) (-61097878037 / 1000000000000), orderedInterval (14860242010 / 1000000000000) (14860243160 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (524355254877093 / 800000000000) 4 (IntervalRat.scale (705 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (11083352448 / 1000000000000) (11083352472 / 1000000000000), orderedInterval (-29136441339 / 1000000000000) (-29136441315 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (350245009504587 / 800000000000) 4 (IntervalRat.scale (705 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-35960072518 / 1000000000000) (-35960057191 / 1000000000000), orderedInterval (12729085264 / 1000000000000) (12729100591 / 1000000000000)))) (orderedInterval (5314363624 / 1000000000000) (5314371024 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate481_chunkChecks4 :
    compactCertificate481.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate481.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate481_chunkChecks4_0
    compactCertificate481_chunkChecks4_1 compactCertificate481_chunkChecks4_2

theorem compactCertificate481_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate481.chunkCheck r b = true :=
  compactCertificate481.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate481_chunkChecks0
    · exact compactCertificate481_chunkChecks1
    · exact compactCertificate481_chunkChecks2
    · exact compactCertificate481_chunkChecks3
    · exact compactCertificate481_chunkChecks4)

theorem compactCertificate481_coefficient0 :
    compactCertificate481.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate481_coefficient1 :
    compactCertificate481.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate481_coefficient2 :
    compactCertificate481.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate481_coefficient3 :
    compactCertificate481.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate481_coefficient4 :
    compactCertificate481.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate481_coefficients : ∀ r : Fin 5,
    compactCertificate481.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate481_coefficient0
  · exact compactCertificate481_coefficient1
  · exact compactCertificate481_coefficient2
  · exact compactCertificate481_coefficient3
  · exact compactCertificate481_coefficient4

theorem compactCertificate481_lower : (1 : ℚ) ≤ compactCertificate481.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate481, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate481_proves {t : ℝ} (ht : t ∈ compactCertificate481.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate481.proves compactCertificate481_states compactCertificate481_chunks
    compactCertificate481_coefficients compactCertificate481_lower ht

end Erdos232
