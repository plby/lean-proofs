/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate422 : CompactCertificate where
  left := 293
  right := 294
  center := 587 / 2
  grid := fun i =>
    match i.val with
    | 0 => 93
    | 1 => 69
    | 2 => 111
    | 3 => 20
    | 4 => 54
    | 5 => 147
    | 6 => 108
    | 7 => 185
    | 8 => 136
    | 9 => 209
    | 10 => 121
    | 11 => 214
    | 12 => 200
    | 13 => 143
    | 14 => 162
    | 15 => 135
    | 16 => 119
    | 17 => 173
    | 18 => 96
    | 19 => 81
    | 20 => 51
    | 21 => 27
    | 22 => 74
    | 23 => 101
    | 24 => 43
    | 25 => 174
    | _ => 116
  point := fun i =>
    match i.val with
    | 0 => 587 / 2
    | 1 => 864763086417887 / 4000000000000
    | 2 => 279646614468671 / 800000000000
    | 3 => 252335711866909 / 4000000000000
    | 4 => 677809216028473 / 4000000000000
    | 5 => 1840383874187541 / 4000000000000
    | 6 => 1355618432057533 / 4000000000000
    | 7 => 2322875289106609 / 4000000000000
    | 8 => 1711019424506131 / 4000000000000
    | 9 => 2625143805584413 / 4000000000000
    | 10 => 1515627482815477 / 4000000000000
    | 11 => 2689507564977593 / 4000000000000
    | 12 => 2512886840947517 / 4000000000000
    | 13 => 1793314621958861 / 4000000000000
    | 14 => 2033427648085419 / 4000000000000
    | 15 => 1695259977484411 / 4000000000000
    | 16 => 1497813602184631 / 4000000000000
    | 17 => 434124762002469 / 800000000000
    | 18 => 1200811938433343 / 4000000000000
    | 19 => 1017941578838023 / 4000000000000
    | 20 => 636980575493869 / 4000000000000
    | 21 => 342570272002323 / 4000000000000
    | 22 => 930144927895969 / 4000000000000
    | 23 => 1270033378506113 / 4000000000000
    | 24 => 537019424506131 / 4000000000000
    | 25 => 2182954146190451 / 4000000000000
    | _ => 1458112202689309 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-39800409269 / 1000000000000) (-39800356769 / 1000000000000), orderedInterval (24254347405 / 1000000000000) (24254399905 / 1000000000000))
    | 1 => (orderedInterval (-11083706803 / 1000000000000) (-11083706802 / 1000000000000), orderedInterval (-53095657888 / 1000000000000) (-53095657887 / 1000000000000))
    | 2 => (orderedInterval (-42609391605 / 1000000000000) (-42609391197 / 1000000000000), orderedInterval (2437937581 / 1000000000000) (2437937988 / 1000000000000))
    | 3 => (orderedInterval (86403147991 / 1000000000000) (86403147992 / 1000000000000), orderedInterval (50559492246 / 1000000000000) (50559492247 / 1000000000000))
    | 4 => (orderedInterval (34150329873 / 1000000000000) (34150329874 / 1000000000000), orderedInterval (50798027820 / 1000000000000) (50798027821 / 1000000000000))
    | 5 => (orderedInterval (29885499299 / 1000000000000) (29885553689 / 1000000000000), orderedInterval (-22180243834 / 1000000000000) (-22180189444 / 1000000000000))
    | 6 => (orderedInterval (16783237088 / 1000000000000) (16783237089 / 1000000000000), orderedInterval (39935061381 / 1000000000000) (39935061382 / 1000000000000))
    | 7 => (orderedInterval (-10080393979 / 1000000000000) (-10080393978 / 1000000000000), orderedInterval (-31529355503 / 1000000000000) (-31529355502 / 1000000000000))
    | 8 => (orderedInterval (36995537243 / 1000000000000) (36995537248 / 1000000000000), orderedInterval (10893445949 / 1000000000000) (10893445954 / 1000000000000))
    | 9 => (orderedInterval (-14335144787 / 1000000000000) (-14335144786 / 1000000000000), orderedInterval (-27639357376 / 1000000000000) (-27639357375 / 1000000000000))
    | 10 => (orderedInterval (17487715002 / 1000000000000) (17487715493 / 1000000000000), orderedInterval (-37095022259 / 1000000000000) (-37095021767 / 1000000000000))
    | 11 => (orderedInterval (23344734375 / 1000000000000) (23344734376 / 1000000000000), orderedInterval (20028666320 / 1000000000000) (20028666321 / 1000000000000))
    | 12 => (orderedInterval (20223334261 / 1000000000000) (20223334262 / 1000000000000), orderedInterval (24568143250 / 1000000000000) (24568143251 / 1000000000000))
    | 13 => (orderedInterval (5033432346 / 1000000000000) (5033432349 / 1000000000000), orderedInterval (-37350626316 / 1000000000000) (-37350626313 / 1000000000000))
    | 14 => (orderedInterval (7171062615 / 1000000000000) (7171062616 / 1000000000000), orderedInterval (34646735869 / 1000000000000) (34646735870 / 1000000000000))
    | 15 => (orderedInterval (-18071967776 / 1000000000000) (-18071967775 / 1000000000000), orderedInterval (-34264561723 / 1000000000000) (-34264561722 / 1000000000000))
    | 16 => (orderedInterval (-40552677870 / 1000000000000) (-40552677853 / 1000000000000), orderedInterval (-7403044536 / 1000000000000) (-7403044519 / 1000000000000))
    | 17 => (orderedInterval (1862653864 / 1000000000000) (1862653865 / 1000000000000), orderedInterval (-34202395127 / 1000000000000) (-34202395126 / 1000000000000))
    | 18 => (orderedInterval (-26188940539 / 1000000000000) (-26188935437 / 1000000000000), orderedInterval (37921995263 / 1000000000000) (37922000365 / 1000000000000))
    | 19 => (orderedInterval (-35924377550 / 1000000000000) (-35924377549 / 1000000000000), orderedInterval (-34729352401 / 1000000000000) (-34729352400 / 1000000000000))
    | 20 => (orderedInterval (12032221704 / 1000000000000) (12032221781 / 1000000000000), orderedInterval (-62110141270 / 1000000000000) (-62110141194 / 1000000000000))
    | 21 => (orderedInterval (-86170608981 / 1000000000000) (-86170608933 / 1000000000000), orderedInterval (3322651255 / 1000000000000) (3322651303 / 1000000000000))
    | 22 => (orderedInterval (39074923212 / 1000000000000) (39074923213 / 1000000000000), orderedInterval (34713575660 / 1000000000000) (34713575661 / 1000000000000))
    | 23 => (orderedInterval (-37496445804 / 1000000000000) (-37496445803 / 1000000000000), orderedInterval (-24416746334 / 1000000000000) (-24416746333 / 1000000000000))
    | 24 => (orderedInterval (3383903829 / 1000000000000) (3383903840 / 1000000000000), orderedInterval (-68790921013 / 1000000000000) (-68790921002 / 1000000000000))
    | 25 => (orderedInterval (-3865367126 / 1000000000000) (-3865367124 / 1000000000000), orderedInterval (33938601590 / 1000000000000) (33938601592 / 1000000000000))
    | _ => (orderedInterval (32430747829 / 1000000000000) (32430747830 / 1000000000000), orderedInterval (26312075146 / 1000000000000) (26312075147 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-18379135271 / 1000000000000) (-18379114417 / 1000000000000)
      | 1 => orderedInterval (-1815078026 / 1000000000000) (-1815074124 / 1000000000000)
      | 2 => orderedInterval (1205028816 / 1000000000000) (1205028834 / 1000000000000)
      | 3 => orderedInterval (7161469401 / 1000000000000) (7161469555 / 1000000000000)
      | 4 => orderedInterval (74592471 / 1000000000000) (74592507 / 1000000000000)
      | 5 => orderedInterval (2159697159 / 1000000000000) (2159697189 / 1000000000000)
      | 6 => orderedInterval (6612443230 / 1000000000000) (6612444123 / 1000000000000)
      | 7 => orderedInterval (3578348203 / 1000000000000) (3578348239 / 1000000000000)
      | _ => orderedInterval (-5749821589 / 1000000000000) (-5749821507 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (9419530189 / 1000000000000) (9419551050 / 1000000000000)
      | 1 => orderedInterval (3424717382 / 1000000000000) (3424723484 / 1000000000000)
      | 2 => orderedInterval (2307872039 / 1000000000000) (2307872069 / 1000000000000)
      | 3 => orderedInterval (13956129286 / 1000000000000) (13956129575 / 1000000000000)
      | 4 => orderedInterval (-6648231716 / 1000000000000) (-6648231658 / 1000000000000)
      | 5 => orderedInterval (-1649977150 / 1000000000000) (-1649977108 / 1000000000000)
      | 6 => orderedInterval (-5594623621 / 1000000000000) (-5594622716 / 1000000000000)
      | 7 => orderedInterval (1382480097 / 1000000000000) (1382480130 / 1000000000000)
      | _ => orderedInterval (-11458207722 / 1000000000000) (-11458207606 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (19346129740 / 1000000000000) (19346150681 / 1000000000000)
      | 1 => orderedInterval (4836933754 / 1000000000000) (4836943332 / 1000000000000)
      | 2 => orderedInterval (-3124240196 / 1000000000000) (-3124240144 / 1000000000000)
      | 3 => orderedInterval (-32359545498 / 1000000000000) (-32359544919 / 1000000000000)
      | 4 => orderedInterval (693594376 / 1000000000000) (693594471 / 1000000000000)
      | 5 => orderedInterval (-3499701356 / 1000000000000) (-3499701293 / 1000000000000)
      | 6 => orderedInterval (-6005789492 / 1000000000000) (-6005788569 / 1000000000000)
      | 7 => orderedInterval (-2946774998 / 1000000000000) (-2946774966 / 1000000000000)
      | _ => orderedInterval (8333253128 / 1000000000000) (8333253298 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-9723359763 / 1000000000000) (-9723338811 / 1000000000000)
      | 1 => orderedInterval (-6442198876 / 1000000000000) (-6442183865 / 1000000000000)
      | 2 => orderedInterval (-8337193932 / 1000000000000) (-8337193839 / 1000000000000)
      | 3 => orderedInterval (-83116447800 / 1000000000000) (-83116446585 / 1000000000000)
      | 4 => orderedInterval (17846884617 / 1000000000000) (17846884777 / 1000000000000)
      | 5 => orderedInterval (5858419894 / 1000000000000) (5858419990 / 1000000000000)
      | 6 => orderedInterval (5550420138 / 1000000000000) (5550421078 / 1000000000000)
      | 7 => orderedInterval (-1965819139 / 1000000000000) (-1965819106 / 1000000000000)
      | _ => orderedInterval (27230159398 / 1000000000000) (27230159660 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-20770357932 / 1000000000000) (-20770336897 / 1000000000000)
      | 1 => orderedInterval (-12649569318 / 1000000000000) (-12649545738 / 1000000000000)
      | 2 => orderedInterval (8855975503 / 1000000000000) (8855975676 / 1000000000000)
      | 3 => orderedInterval (159250247299 / 1000000000000) (159250249924 / 1000000000000)
      | 4 => orderedInterval (-5520225961 / 1000000000000) (-5520225682 / 1000000000000)
      | 5 => orderedInterval (5758620650 / 1000000000000) (5758620801 / 1000000000000)
      | 6 => orderedInterval (5728579373 / 1000000000000) (5728580335 / 1000000000000)
      | 7 => orderedInterval (3611342266 / 1000000000000) (3611342301 / 1000000000000)
      | _ => orderedInterval (-10902461866 / 1000000000000) (-10902461446 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-5152455606 / 1000000000000) (-5152429601 / 1000000000000)
    | 1 => orderedInterval (5139688784 / 1000000000000) (5139717220 / 1000000000000)
    | 2 => orderedInterval (-14726140542 / 1000000000000) (-14726108109 / 1000000000000)
    | 3 => orderedInterval (-53099135463 / 1000000000000) (-53099096701 / 1000000000000)
    | _ => orderedInterval (133362150014 / 1000000000000) (133362199274 / 1000000000000)

theorem compactCertificate422_stateChecks0 :
    compactCertificate422.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 93 12 (587 / 2)) (orderedInterval (-39800409269 / 1000000000000) (-39800356769 / 1000000000000), orderedInterval (24254347405 / 1000000000000) (24254399905 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (864763086417887 / 4000000000000)) (orderedInterval (-11083706803 / 1000000000000) (-11083706802 / 1000000000000), orderedInterval (-53095657888 / 1000000000000) (-53095657887 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 111 12 (279646614468671 / 800000000000)) (orderedInterval (-42609391605 / 1000000000000) (-42609391197 / 1000000000000), orderedInterval (2437937581 / 1000000000000) (2437937988 / 1000000000000))) = true
  rfl'

theorem compactCertificate422_stateChecks1 :
    compactCertificate422.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 20 12 (252335711866909 / 4000000000000)) (orderedInterval (86403147991 / 1000000000000) (86403147992 / 1000000000000), orderedInterval (50559492246 / 1000000000000) (50559492247 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (677809216028473 / 4000000000000)) (orderedInterval (34150329873 / 1000000000000) (34150329874 / 1000000000000), orderedInterval (50798027820 / 1000000000000) (50798027821 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 147 12 (1840383874187541 / 4000000000000)) (orderedInterval (29885499299 / 1000000000000) (29885553689 / 1000000000000), orderedInterval (-22180243834 / 1000000000000) (-22180189444 / 1000000000000))) = true
  rfl'

theorem compactCertificate422_stateChecks2 :
    compactCertificate422.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 108 12 (1355618432057533 / 4000000000000)) (orderedInterval (16783237088 / 1000000000000) (16783237089 / 1000000000000), orderedInterval (39935061381 / 1000000000000) (39935061382 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 185 12 (2322875289106609 / 4000000000000)) (orderedInterval (-10080393979 / 1000000000000) (-10080393978 / 1000000000000), orderedInterval (-31529355503 / 1000000000000) (-31529355502 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 136 12 (1711019424506131 / 4000000000000)) (orderedInterval (36995537243 / 1000000000000) (36995537248 / 1000000000000), orderedInterval (10893445949 / 1000000000000) (10893445954 / 1000000000000))) = true
  rfl'

theorem compactCertificate422_stateChecks3 :
    compactCertificate422.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 209 12 (2625143805584413 / 4000000000000)) (orderedInterval (-14335144787 / 1000000000000) (-14335144786 / 1000000000000), orderedInterval (-27639357376 / 1000000000000) (-27639357375 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 121 12 (1515627482815477 / 4000000000000)) (orderedInterval (17487715002 / 1000000000000) (17487715493 / 1000000000000), orderedInterval (-37095022259 / 1000000000000) (-37095021767 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 214 12 (2689507564977593 / 4000000000000)) (orderedInterval (23344734375 / 1000000000000) (23344734376 / 1000000000000), orderedInterval (20028666320 / 1000000000000) (20028666321 / 1000000000000))) = true
  rfl'

theorem compactCertificate422_stateChecks4 :
    compactCertificate422.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 200 12 (2512886840947517 / 4000000000000)) (orderedInterval (20223334261 / 1000000000000) (20223334262 / 1000000000000), orderedInterval (24568143250 / 1000000000000) (24568143251 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 143 12 (1793314621958861 / 4000000000000)) (orderedInterval (5033432346 / 1000000000000) (5033432349 / 1000000000000), orderedInterval (-37350626316 / 1000000000000) (-37350626313 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 162 12 (2033427648085419 / 4000000000000)) (orderedInterval (7171062615 / 1000000000000) (7171062616 / 1000000000000), orderedInterval (34646735869 / 1000000000000) (34646735870 / 1000000000000))) = true
  rfl'

theorem compactCertificate422_stateChecks5 :
    compactCertificate422.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 135 12 (1695259977484411 / 4000000000000)) (orderedInterval (-18071967776 / 1000000000000) (-18071967775 / 1000000000000), orderedInterval (-34264561723 / 1000000000000) (-34264561722 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 119 12 (1497813602184631 / 4000000000000)) (orderedInterval (-40552677870 / 1000000000000) (-40552677853 / 1000000000000), orderedInterval (-7403044536 / 1000000000000) (-7403044519 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 173 12 (434124762002469 / 800000000000)) (orderedInterval (1862653864 / 1000000000000) (1862653865 / 1000000000000), orderedInterval (-34202395127 / 1000000000000) (-34202395126 / 1000000000000))) = true
  rfl'

theorem compactCertificate422_stateChecks6 :
    compactCertificate422.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 96 12 (1200811938433343 / 4000000000000)) (orderedInterval (-26188940539 / 1000000000000) (-26188935437 / 1000000000000), orderedInterval (37921995263 / 1000000000000) (37922000365 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 81 12 (1017941578838023 / 4000000000000)) (orderedInterval (-35924377550 / 1000000000000) (-35924377549 / 1000000000000), orderedInterval (-34729352401 / 1000000000000) (-34729352400 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (636980575493869 / 4000000000000)) (orderedInterval (12032221704 / 1000000000000) (12032221781 / 1000000000000), orderedInterval (-62110141270 / 1000000000000) (-62110141194 / 1000000000000))) = true
  rfl'

theorem compactCertificate422_stateChecks7 :
    compactCertificate422.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 27 12 (342570272002323 / 4000000000000)) (orderedInterval (-86170608981 / 1000000000000) (-86170608933 / 1000000000000), orderedInterval (3322651255 / 1000000000000) (3322651303 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 74 12 (930144927895969 / 4000000000000)) (orderedInterval (39074923212 / 1000000000000) (39074923213 / 1000000000000), orderedInterval (34713575660 / 1000000000000) (34713575661 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 101 12 (1270033378506113 / 4000000000000)) (orderedInterval (-37496445804 / 1000000000000) (-37496445803 / 1000000000000), orderedInterval (-24416746334 / 1000000000000) (-24416746333 / 1000000000000))) = true
  rfl'

theorem compactCertificate422_stateChecks8 :
    compactCertificate422.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (537019424506131 / 4000000000000)) (orderedInterval (3383903829 / 1000000000000) (3383903840 / 1000000000000), orderedInterval (-68790921013 / 1000000000000) (-68790921002 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 174 12 (2182954146190451 / 4000000000000)) (orderedInterval (-3865367126 / 1000000000000) (-3865367124 / 1000000000000), orderedInterval (33938601590 / 1000000000000) (33938601592 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 116 12 (1458112202689309 / 4000000000000)) (orderedInterval (32430747829 / 1000000000000) (32430747830 / 1000000000000), orderedInterval (26312075146 / 1000000000000) (26312075147 / 1000000000000))) = true
  rfl'

theorem compactCertificate422_states : ∀ j,
    BesselStateValid (compactCertificate422.point j) (compactCertificate422.state j) :=
  compactCertificate422.statesValid_of_checks3 compactCertificate422_stateChecks0
    compactCertificate422_stateChecks1 compactCertificate422_stateChecks2
    compactCertificate422_stateChecks3 compactCertificate422_stateChecks4
    compactCertificate422_stateChecks5 compactCertificate422_stateChecks6
    compactCertificate422_stateChecks7 compactCertificate422_stateChecks8

theorem compactCertificate422_chunkChecks0_0 :
    compactCertificate422.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (587 / 2) 0 (IntervalRat.scale (587 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-39800409269 / 1000000000000) (-39800356769 / 1000000000000), orderedInterval (24254347405 / 1000000000000) (24254399905 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (864763086417887 / 4000000000000) 0 (IntervalRat.scale (587 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-11083706803 / 1000000000000) (-11083706802 / 1000000000000), orderedInterval (-53095657888 / 1000000000000) (-53095657887 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (279646614468671 / 800000000000) 0 (IntervalRat.scale (587 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-42609391605 / 1000000000000) (-42609391197 / 1000000000000), orderedInterval (2437937581 / 1000000000000) (2437937988 / 1000000000000)))) (orderedInterval (-18379135271 / 1000000000000) (-18379114417 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (252335711866909 / 4000000000000) 0 (IntervalRat.scale (587 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (86403147991 / 1000000000000) (86403147992 / 1000000000000), orderedInterval (50559492246 / 1000000000000) (50559492247 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (677809216028473 / 4000000000000) 0 (IntervalRat.scale (587 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (34150329873 / 1000000000000) (34150329874 / 1000000000000), orderedInterval (50798027820 / 1000000000000) (50798027821 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1840383874187541 / 4000000000000) 0 (IntervalRat.scale (587 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29885499299 / 1000000000000) (29885553689 / 1000000000000), orderedInterval (-22180243834 / 1000000000000) (-22180189444 / 1000000000000)))) (orderedInterval (-1815078026 / 1000000000000) (-1815074124 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1355618432057533 / 4000000000000) 0 (IntervalRat.scale (587 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (16783237088 / 1000000000000) (16783237089 / 1000000000000), orderedInterval (39935061381 / 1000000000000) (39935061382 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2322875289106609 / 4000000000000) 0 (IntervalRat.scale (587 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-10080393979 / 1000000000000) (-10080393978 / 1000000000000), orderedInterval (-31529355503 / 1000000000000) (-31529355502 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1711019424506131 / 4000000000000) 0 (IntervalRat.scale (587 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (36995537243 / 1000000000000) (36995537248 / 1000000000000), orderedInterval (10893445949 / 1000000000000) (10893445954 / 1000000000000)))) (orderedInterval (1205028816 / 1000000000000) (1205028834 / 1000000000000))) = true
  rfl'

theorem compactCertificate422_chunkChecks0_1 :
    compactCertificate422.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2625143805584413 / 4000000000000) 0 (IntervalRat.scale (587 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-14335144787 / 1000000000000) (-14335144786 / 1000000000000), orderedInterval (-27639357376 / 1000000000000) (-27639357375 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1515627482815477 / 4000000000000) 0 (IntervalRat.scale (587 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (17487715002 / 1000000000000) (17487715493 / 1000000000000), orderedInterval (-37095022259 / 1000000000000) (-37095021767 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (2689507564977593 / 4000000000000) 0 (IntervalRat.scale (587 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (23344734375 / 1000000000000) (23344734376 / 1000000000000), orderedInterval (20028666320 / 1000000000000) (20028666321 / 1000000000000)))) (orderedInterval (7161469401 / 1000000000000) (7161469555 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2512886840947517 / 4000000000000) 0 (IntervalRat.scale (587 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (20223334261 / 1000000000000) (20223334262 / 1000000000000), orderedInterval (24568143250 / 1000000000000) (24568143251 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1793314621958861 / 4000000000000) 0 (IntervalRat.scale (587 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (5033432346 / 1000000000000) (5033432349 / 1000000000000), orderedInterval (-37350626316 / 1000000000000) (-37350626313 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2033427648085419 / 4000000000000) 0 (IntervalRat.scale (587 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (7171062615 / 1000000000000) (7171062616 / 1000000000000), orderedInterval (34646735869 / 1000000000000) (34646735870 / 1000000000000)))) (orderedInterval (74592471 / 1000000000000) (74592507 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1695259977484411 / 4000000000000) 0 (IntervalRat.scale (587 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-18071967776 / 1000000000000) (-18071967775 / 1000000000000), orderedInterval (-34264561723 / 1000000000000) (-34264561722 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1497813602184631 / 4000000000000) 0 (IntervalRat.scale (587 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-40552677870 / 1000000000000) (-40552677853 / 1000000000000), orderedInterval (-7403044536 / 1000000000000) (-7403044519 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (434124762002469 / 800000000000) 0 (IntervalRat.scale (587 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (1862653864 / 1000000000000) (1862653865 / 1000000000000), orderedInterval (-34202395127 / 1000000000000) (-34202395126 / 1000000000000)))) (orderedInterval (2159697159 / 1000000000000) (2159697189 / 1000000000000))) = true
  rfl'

theorem compactCertificate422_chunkChecks0_2 :
    compactCertificate422.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1200811938433343 / 4000000000000) 0 (IntervalRat.scale (587 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-26188940539 / 1000000000000) (-26188935437 / 1000000000000), orderedInterval (37921995263 / 1000000000000) (37922000365 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1017941578838023 / 4000000000000) 0 (IntervalRat.scale (587 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-35924377550 / 1000000000000) (-35924377549 / 1000000000000), orderedInterval (-34729352401 / 1000000000000) (-34729352400 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (636980575493869 / 4000000000000) 0 (IntervalRat.scale (587 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (12032221704 / 1000000000000) (12032221781 / 1000000000000), orderedInterval (-62110141270 / 1000000000000) (-62110141194 / 1000000000000)))) (orderedInterval (6612443230 / 1000000000000) (6612444123 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (342570272002323 / 4000000000000) 0 (IntervalRat.scale (587 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-86170608981 / 1000000000000) (-86170608933 / 1000000000000), orderedInterval (3322651255 / 1000000000000) (3322651303 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (930144927895969 / 4000000000000) 0 (IntervalRat.scale (587 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (39074923212 / 1000000000000) (39074923213 / 1000000000000), orderedInterval (34713575660 / 1000000000000) (34713575661 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1270033378506113 / 4000000000000) 0 (IntervalRat.scale (587 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-37496445804 / 1000000000000) (-37496445803 / 1000000000000), orderedInterval (-24416746334 / 1000000000000) (-24416746333 / 1000000000000)))) (orderedInterval (3578348203 / 1000000000000) (3578348239 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (537019424506131 / 4000000000000) 0 (IntervalRat.scale (587 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (3383903829 / 1000000000000) (3383903840 / 1000000000000), orderedInterval (-68790921013 / 1000000000000) (-68790921002 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2182954146190451 / 4000000000000) 0 (IntervalRat.scale (587 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-3865367126 / 1000000000000) (-3865367124 / 1000000000000), orderedInterval (33938601590 / 1000000000000) (33938601592 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1458112202689309 / 4000000000000) 0 (IntervalRat.scale (587 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (32430747829 / 1000000000000) (32430747830 / 1000000000000), orderedInterval (26312075146 / 1000000000000) (26312075147 / 1000000000000)))) (orderedInterval (-5749821589 / 1000000000000) (-5749821507 / 1000000000000))) = true
  rfl'

theorem compactCertificate422_chunkChecks0 :
    compactCertificate422.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate422.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate422_chunkChecks0_0
    compactCertificate422_chunkChecks0_1 compactCertificate422_chunkChecks0_2

theorem compactCertificate422_chunkChecks1_0 :
    compactCertificate422.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (587 / 2) 1 (IntervalRat.scale (587 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-39800409269 / 1000000000000) (-39800356769 / 1000000000000), orderedInterval (24254347405 / 1000000000000) (24254399905 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (864763086417887 / 4000000000000) 1 (IntervalRat.scale (587 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-11083706803 / 1000000000000) (-11083706802 / 1000000000000), orderedInterval (-53095657888 / 1000000000000) (-53095657887 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (279646614468671 / 800000000000) 1 (IntervalRat.scale (587 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-42609391605 / 1000000000000) (-42609391197 / 1000000000000), orderedInterval (2437937581 / 1000000000000) (2437937988 / 1000000000000)))) (orderedInterval (9419530189 / 1000000000000) (9419551050 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (252335711866909 / 4000000000000) 1 (IntervalRat.scale (587 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (86403147991 / 1000000000000) (86403147992 / 1000000000000), orderedInterval (50559492246 / 1000000000000) (50559492247 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (677809216028473 / 4000000000000) 1 (IntervalRat.scale (587 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (34150329873 / 1000000000000) (34150329874 / 1000000000000), orderedInterval (50798027820 / 1000000000000) (50798027821 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1840383874187541 / 4000000000000) 1 (IntervalRat.scale (587 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29885499299 / 1000000000000) (29885553689 / 1000000000000), orderedInterval (-22180243834 / 1000000000000) (-22180189444 / 1000000000000)))) (orderedInterval (3424717382 / 1000000000000) (3424723484 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1355618432057533 / 4000000000000) 1 (IntervalRat.scale (587 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (16783237088 / 1000000000000) (16783237089 / 1000000000000), orderedInterval (39935061381 / 1000000000000) (39935061382 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2322875289106609 / 4000000000000) 1 (IntervalRat.scale (587 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-10080393979 / 1000000000000) (-10080393978 / 1000000000000), orderedInterval (-31529355503 / 1000000000000) (-31529355502 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1711019424506131 / 4000000000000) 1 (IntervalRat.scale (587 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (36995537243 / 1000000000000) (36995537248 / 1000000000000), orderedInterval (10893445949 / 1000000000000) (10893445954 / 1000000000000)))) (orderedInterval (2307872039 / 1000000000000) (2307872069 / 1000000000000))) = true
  rfl'

theorem compactCertificate422_chunkChecks1_1 :
    compactCertificate422.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2625143805584413 / 4000000000000) 1 (IntervalRat.scale (587 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-14335144787 / 1000000000000) (-14335144786 / 1000000000000), orderedInterval (-27639357376 / 1000000000000) (-27639357375 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1515627482815477 / 4000000000000) 1 (IntervalRat.scale (587 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (17487715002 / 1000000000000) (17487715493 / 1000000000000), orderedInterval (-37095022259 / 1000000000000) (-37095021767 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (2689507564977593 / 4000000000000) 1 (IntervalRat.scale (587 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (23344734375 / 1000000000000) (23344734376 / 1000000000000), orderedInterval (20028666320 / 1000000000000) (20028666321 / 1000000000000)))) (orderedInterval (13956129286 / 1000000000000) (13956129575 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2512886840947517 / 4000000000000) 1 (IntervalRat.scale (587 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (20223334261 / 1000000000000) (20223334262 / 1000000000000), orderedInterval (24568143250 / 1000000000000) (24568143251 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1793314621958861 / 4000000000000) 1 (IntervalRat.scale (587 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (5033432346 / 1000000000000) (5033432349 / 1000000000000), orderedInterval (-37350626316 / 1000000000000) (-37350626313 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2033427648085419 / 4000000000000) 1 (IntervalRat.scale (587 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (7171062615 / 1000000000000) (7171062616 / 1000000000000), orderedInterval (34646735869 / 1000000000000) (34646735870 / 1000000000000)))) (orderedInterval (-6648231716 / 1000000000000) (-6648231658 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1695259977484411 / 4000000000000) 1 (IntervalRat.scale (587 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-18071967776 / 1000000000000) (-18071967775 / 1000000000000), orderedInterval (-34264561723 / 1000000000000) (-34264561722 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1497813602184631 / 4000000000000) 1 (IntervalRat.scale (587 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-40552677870 / 1000000000000) (-40552677853 / 1000000000000), orderedInterval (-7403044536 / 1000000000000) (-7403044519 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (434124762002469 / 800000000000) 1 (IntervalRat.scale (587 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (1862653864 / 1000000000000) (1862653865 / 1000000000000), orderedInterval (-34202395127 / 1000000000000) (-34202395126 / 1000000000000)))) (orderedInterval (-1649977150 / 1000000000000) (-1649977108 / 1000000000000))) = true
  rfl'

theorem compactCertificate422_chunkChecks1_2 :
    compactCertificate422.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1200811938433343 / 4000000000000) 1 (IntervalRat.scale (587 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-26188940539 / 1000000000000) (-26188935437 / 1000000000000), orderedInterval (37921995263 / 1000000000000) (37922000365 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1017941578838023 / 4000000000000) 1 (IntervalRat.scale (587 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-35924377550 / 1000000000000) (-35924377549 / 1000000000000), orderedInterval (-34729352401 / 1000000000000) (-34729352400 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (636980575493869 / 4000000000000) 1 (IntervalRat.scale (587 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (12032221704 / 1000000000000) (12032221781 / 1000000000000), orderedInterval (-62110141270 / 1000000000000) (-62110141194 / 1000000000000)))) (orderedInterval (-5594623621 / 1000000000000) (-5594622716 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (342570272002323 / 4000000000000) 1 (IntervalRat.scale (587 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-86170608981 / 1000000000000) (-86170608933 / 1000000000000), orderedInterval (3322651255 / 1000000000000) (3322651303 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (930144927895969 / 4000000000000) 1 (IntervalRat.scale (587 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (39074923212 / 1000000000000) (39074923213 / 1000000000000), orderedInterval (34713575660 / 1000000000000) (34713575661 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1270033378506113 / 4000000000000) 1 (IntervalRat.scale (587 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-37496445804 / 1000000000000) (-37496445803 / 1000000000000), orderedInterval (-24416746334 / 1000000000000) (-24416746333 / 1000000000000)))) (orderedInterval (1382480097 / 1000000000000) (1382480130 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (537019424506131 / 4000000000000) 1 (IntervalRat.scale (587 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (3383903829 / 1000000000000) (3383903840 / 1000000000000), orderedInterval (-68790921013 / 1000000000000) (-68790921002 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2182954146190451 / 4000000000000) 1 (IntervalRat.scale (587 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-3865367126 / 1000000000000) (-3865367124 / 1000000000000), orderedInterval (33938601590 / 1000000000000) (33938601592 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1458112202689309 / 4000000000000) 1 (IntervalRat.scale (587 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (32430747829 / 1000000000000) (32430747830 / 1000000000000), orderedInterval (26312075146 / 1000000000000) (26312075147 / 1000000000000)))) (orderedInterval (-11458207722 / 1000000000000) (-11458207606 / 1000000000000))) = true
  rfl'

theorem compactCertificate422_chunkChecks1 :
    compactCertificate422.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate422.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate422_chunkChecks1_0
    compactCertificate422_chunkChecks1_1 compactCertificate422_chunkChecks1_2

theorem compactCertificate422_chunkChecks2_0 :
    compactCertificate422.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (587 / 2) 2 (IntervalRat.scale (587 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-39800409269 / 1000000000000) (-39800356769 / 1000000000000), orderedInterval (24254347405 / 1000000000000) (24254399905 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (864763086417887 / 4000000000000) 2 (IntervalRat.scale (587 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-11083706803 / 1000000000000) (-11083706802 / 1000000000000), orderedInterval (-53095657888 / 1000000000000) (-53095657887 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (279646614468671 / 800000000000) 2 (IntervalRat.scale (587 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-42609391605 / 1000000000000) (-42609391197 / 1000000000000), orderedInterval (2437937581 / 1000000000000) (2437937988 / 1000000000000)))) (orderedInterval (19346129740 / 1000000000000) (19346150681 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (252335711866909 / 4000000000000) 2 (IntervalRat.scale (587 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (86403147991 / 1000000000000) (86403147992 / 1000000000000), orderedInterval (50559492246 / 1000000000000) (50559492247 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (677809216028473 / 4000000000000) 2 (IntervalRat.scale (587 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (34150329873 / 1000000000000) (34150329874 / 1000000000000), orderedInterval (50798027820 / 1000000000000) (50798027821 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1840383874187541 / 4000000000000) 2 (IntervalRat.scale (587 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29885499299 / 1000000000000) (29885553689 / 1000000000000), orderedInterval (-22180243834 / 1000000000000) (-22180189444 / 1000000000000)))) (orderedInterval (4836933754 / 1000000000000) (4836943332 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1355618432057533 / 4000000000000) 2 (IntervalRat.scale (587 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (16783237088 / 1000000000000) (16783237089 / 1000000000000), orderedInterval (39935061381 / 1000000000000) (39935061382 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2322875289106609 / 4000000000000) 2 (IntervalRat.scale (587 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-10080393979 / 1000000000000) (-10080393978 / 1000000000000), orderedInterval (-31529355503 / 1000000000000) (-31529355502 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1711019424506131 / 4000000000000) 2 (IntervalRat.scale (587 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (36995537243 / 1000000000000) (36995537248 / 1000000000000), orderedInterval (10893445949 / 1000000000000) (10893445954 / 1000000000000)))) (orderedInterval (-3124240196 / 1000000000000) (-3124240144 / 1000000000000))) = true
  rfl'

theorem compactCertificate422_chunkChecks2_1 :
    compactCertificate422.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2625143805584413 / 4000000000000) 2 (IntervalRat.scale (587 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-14335144787 / 1000000000000) (-14335144786 / 1000000000000), orderedInterval (-27639357376 / 1000000000000) (-27639357375 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1515627482815477 / 4000000000000) 2 (IntervalRat.scale (587 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (17487715002 / 1000000000000) (17487715493 / 1000000000000), orderedInterval (-37095022259 / 1000000000000) (-37095021767 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (2689507564977593 / 4000000000000) 2 (IntervalRat.scale (587 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (23344734375 / 1000000000000) (23344734376 / 1000000000000), orderedInterval (20028666320 / 1000000000000) (20028666321 / 1000000000000)))) (orderedInterval (-32359545498 / 1000000000000) (-32359544919 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2512886840947517 / 4000000000000) 2 (IntervalRat.scale (587 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (20223334261 / 1000000000000) (20223334262 / 1000000000000), orderedInterval (24568143250 / 1000000000000) (24568143251 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1793314621958861 / 4000000000000) 2 (IntervalRat.scale (587 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (5033432346 / 1000000000000) (5033432349 / 1000000000000), orderedInterval (-37350626316 / 1000000000000) (-37350626313 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2033427648085419 / 4000000000000) 2 (IntervalRat.scale (587 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (7171062615 / 1000000000000) (7171062616 / 1000000000000), orderedInterval (34646735869 / 1000000000000) (34646735870 / 1000000000000)))) (orderedInterval (693594376 / 1000000000000) (693594471 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1695259977484411 / 4000000000000) 2 (IntervalRat.scale (587 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-18071967776 / 1000000000000) (-18071967775 / 1000000000000), orderedInterval (-34264561723 / 1000000000000) (-34264561722 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1497813602184631 / 4000000000000) 2 (IntervalRat.scale (587 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-40552677870 / 1000000000000) (-40552677853 / 1000000000000), orderedInterval (-7403044536 / 1000000000000) (-7403044519 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (434124762002469 / 800000000000) 2 (IntervalRat.scale (587 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (1862653864 / 1000000000000) (1862653865 / 1000000000000), orderedInterval (-34202395127 / 1000000000000) (-34202395126 / 1000000000000)))) (orderedInterval (-3499701356 / 1000000000000) (-3499701293 / 1000000000000))) = true
  rfl'

theorem compactCertificate422_chunkChecks2_2 :
    compactCertificate422.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1200811938433343 / 4000000000000) 2 (IntervalRat.scale (587 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-26188940539 / 1000000000000) (-26188935437 / 1000000000000), orderedInterval (37921995263 / 1000000000000) (37922000365 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1017941578838023 / 4000000000000) 2 (IntervalRat.scale (587 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-35924377550 / 1000000000000) (-35924377549 / 1000000000000), orderedInterval (-34729352401 / 1000000000000) (-34729352400 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (636980575493869 / 4000000000000) 2 (IntervalRat.scale (587 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (12032221704 / 1000000000000) (12032221781 / 1000000000000), orderedInterval (-62110141270 / 1000000000000) (-62110141194 / 1000000000000)))) (orderedInterval (-6005789492 / 1000000000000) (-6005788569 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (342570272002323 / 4000000000000) 2 (IntervalRat.scale (587 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-86170608981 / 1000000000000) (-86170608933 / 1000000000000), orderedInterval (3322651255 / 1000000000000) (3322651303 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (930144927895969 / 4000000000000) 2 (IntervalRat.scale (587 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (39074923212 / 1000000000000) (39074923213 / 1000000000000), orderedInterval (34713575660 / 1000000000000) (34713575661 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1270033378506113 / 4000000000000) 2 (IntervalRat.scale (587 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-37496445804 / 1000000000000) (-37496445803 / 1000000000000), orderedInterval (-24416746334 / 1000000000000) (-24416746333 / 1000000000000)))) (orderedInterval (-2946774998 / 1000000000000) (-2946774966 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (537019424506131 / 4000000000000) 2 (IntervalRat.scale (587 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (3383903829 / 1000000000000) (3383903840 / 1000000000000), orderedInterval (-68790921013 / 1000000000000) (-68790921002 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2182954146190451 / 4000000000000) 2 (IntervalRat.scale (587 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-3865367126 / 1000000000000) (-3865367124 / 1000000000000), orderedInterval (33938601590 / 1000000000000) (33938601592 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1458112202689309 / 4000000000000) 2 (IntervalRat.scale (587 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (32430747829 / 1000000000000) (32430747830 / 1000000000000), orderedInterval (26312075146 / 1000000000000) (26312075147 / 1000000000000)))) (orderedInterval (8333253128 / 1000000000000) (8333253298 / 1000000000000))) = true
  rfl'

theorem compactCertificate422_chunkChecks2 :
    compactCertificate422.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate422.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate422_chunkChecks2_0
    compactCertificate422_chunkChecks2_1 compactCertificate422_chunkChecks2_2

theorem compactCertificate422_chunkChecks3_0 :
    compactCertificate422.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (587 / 2) 3 (IntervalRat.scale (587 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-39800409269 / 1000000000000) (-39800356769 / 1000000000000), orderedInterval (24254347405 / 1000000000000) (24254399905 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (864763086417887 / 4000000000000) 3 (IntervalRat.scale (587 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-11083706803 / 1000000000000) (-11083706802 / 1000000000000), orderedInterval (-53095657888 / 1000000000000) (-53095657887 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (279646614468671 / 800000000000) 3 (IntervalRat.scale (587 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-42609391605 / 1000000000000) (-42609391197 / 1000000000000), orderedInterval (2437937581 / 1000000000000) (2437937988 / 1000000000000)))) (orderedInterval (-9723359763 / 1000000000000) (-9723338811 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (252335711866909 / 4000000000000) 3 (IntervalRat.scale (587 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (86403147991 / 1000000000000) (86403147992 / 1000000000000), orderedInterval (50559492246 / 1000000000000) (50559492247 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (677809216028473 / 4000000000000) 3 (IntervalRat.scale (587 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (34150329873 / 1000000000000) (34150329874 / 1000000000000), orderedInterval (50798027820 / 1000000000000) (50798027821 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1840383874187541 / 4000000000000) 3 (IntervalRat.scale (587 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29885499299 / 1000000000000) (29885553689 / 1000000000000), orderedInterval (-22180243834 / 1000000000000) (-22180189444 / 1000000000000)))) (orderedInterval (-6442198876 / 1000000000000) (-6442183865 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1355618432057533 / 4000000000000) 3 (IntervalRat.scale (587 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (16783237088 / 1000000000000) (16783237089 / 1000000000000), orderedInterval (39935061381 / 1000000000000) (39935061382 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2322875289106609 / 4000000000000) 3 (IntervalRat.scale (587 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-10080393979 / 1000000000000) (-10080393978 / 1000000000000), orderedInterval (-31529355503 / 1000000000000) (-31529355502 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1711019424506131 / 4000000000000) 3 (IntervalRat.scale (587 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (36995537243 / 1000000000000) (36995537248 / 1000000000000), orderedInterval (10893445949 / 1000000000000) (10893445954 / 1000000000000)))) (orderedInterval (-8337193932 / 1000000000000) (-8337193839 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate422_chunkChecks3_1 :
    compactCertificate422.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2625143805584413 / 4000000000000) 3 (IntervalRat.scale (587 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-14335144787 / 1000000000000) (-14335144786 / 1000000000000), orderedInterval (-27639357376 / 1000000000000) (-27639357375 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1515627482815477 / 4000000000000) 3 (IntervalRat.scale (587 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (17487715002 / 1000000000000) (17487715493 / 1000000000000), orderedInterval (-37095022259 / 1000000000000) (-37095021767 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (2689507564977593 / 4000000000000) 3 (IntervalRat.scale (587 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (23344734375 / 1000000000000) (23344734376 / 1000000000000), orderedInterval (20028666320 / 1000000000000) (20028666321 / 1000000000000)))) (orderedInterval (-83116447800 / 1000000000000) (-83116446585 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2512886840947517 / 4000000000000) 3 (IntervalRat.scale (587 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (20223334261 / 1000000000000) (20223334262 / 1000000000000), orderedInterval (24568143250 / 1000000000000) (24568143251 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1793314621958861 / 4000000000000) 3 (IntervalRat.scale (587 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (5033432346 / 1000000000000) (5033432349 / 1000000000000), orderedInterval (-37350626316 / 1000000000000) (-37350626313 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2033427648085419 / 4000000000000) 3 (IntervalRat.scale (587 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (7171062615 / 1000000000000) (7171062616 / 1000000000000), orderedInterval (34646735869 / 1000000000000) (34646735870 / 1000000000000)))) (orderedInterval (17846884617 / 1000000000000) (17846884777 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1695259977484411 / 4000000000000) 3 (IntervalRat.scale (587 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-18071967776 / 1000000000000) (-18071967775 / 1000000000000), orderedInterval (-34264561723 / 1000000000000) (-34264561722 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1497813602184631 / 4000000000000) 3 (IntervalRat.scale (587 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-40552677870 / 1000000000000) (-40552677853 / 1000000000000), orderedInterval (-7403044536 / 1000000000000) (-7403044519 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (434124762002469 / 800000000000) 3 (IntervalRat.scale (587 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (1862653864 / 1000000000000) (1862653865 / 1000000000000), orderedInterval (-34202395127 / 1000000000000) (-34202395126 / 1000000000000)))) (orderedInterval (5858419894 / 1000000000000) (5858419990 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate422_chunkChecks3_2 :
    compactCertificate422.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1200811938433343 / 4000000000000) 3 (IntervalRat.scale (587 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-26188940539 / 1000000000000) (-26188935437 / 1000000000000), orderedInterval (37921995263 / 1000000000000) (37922000365 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1017941578838023 / 4000000000000) 3 (IntervalRat.scale (587 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-35924377550 / 1000000000000) (-35924377549 / 1000000000000), orderedInterval (-34729352401 / 1000000000000) (-34729352400 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (636980575493869 / 4000000000000) 3 (IntervalRat.scale (587 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (12032221704 / 1000000000000) (12032221781 / 1000000000000), orderedInterval (-62110141270 / 1000000000000) (-62110141194 / 1000000000000)))) (orderedInterval (5550420138 / 1000000000000) (5550421078 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (342570272002323 / 4000000000000) 3 (IntervalRat.scale (587 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-86170608981 / 1000000000000) (-86170608933 / 1000000000000), orderedInterval (3322651255 / 1000000000000) (3322651303 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (930144927895969 / 4000000000000) 3 (IntervalRat.scale (587 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (39074923212 / 1000000000000) (39074923213 / 1000000000000), orderedInterval (34713575660 / 1000000000000) (34713575661 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1270033378506113 / 4000000000000) 3 (IntervalRat.scale (587 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-37496445804 / 1000000000000) (-37496445803 / 1000000000000), orderedInterval (-24416746334 / 1000000000000) (-24416746333 / 1000000000000)))) (orderedInterval (-1965819139 / 1000000000000) (-1965819106 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (537019424506131 / 4000000000000) 3 (IntervalRat.scale (587 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (3383903829 / 1000000000000) (3383903840 / 1000000000000), orderedInterval (-68790921013 / 1000000000000) (-68790921002 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2182954146190451 / 4000000000000) 3 (IntervalRat.scale (587 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-3865367126 / 1000000000000) (-3865367124 / 1000000000000), orderedInterval (33938601590 / 1000000000000) (33938601592 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1458112202689309 / 4000000000000) 3 (IntervalRat.scale (587 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (32430747829 / 1000000000000) (32430747830 / 1000000000000), orderedInterval (26312075146 / 1000000000000) (26312075147 / 1000000000000)))) (orderedInterval (27230159398 / 1000000000000) (27230159660 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate422_chunkChecks3 :
    compactCertificate422.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate422.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate422_chunkChecks3_0
    compactCertificate422_chunkChecks3_1 compactCertificate422_chunkChecks3_2

theorem compactCertificate422_chunkChecks4_0 :
    compactCertificate422.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (587 / 2) 4 (IntervalRat.scale (587 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-39800409269 / 1000000000000) (-39800356769 / 1000000000000), orderedInterval (24254347405 / 1000000000000) (24254399905 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (864763086417887 / 4000000000000) 4 (IntervalRat.scale (587 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-11083706803 / 1000000000000) (-11083706802 / 1000000000000), orderedInterval (-53095657888 / 1000000000000) (-53095657887 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (279646614468671 / 800000000000) 4 (IntervalRat.scale (587 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-42609391605 / 1000000000000) (-42609391197 / 1000000000000), orderedInterval (2437937581 / 1000000000000) (2437937988 / 1000000000000)))) (orderedInterval (-20770357932 / 1000000000000) (-20770336897 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (252335711866909 / 4000000000000) 4 (IntervalRat.scale (587 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (86403147991 / 1000000000000) (86403147992 / 1000000000000), orderedInterval (50559492246 / 1000000000000) (50559492247 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (677809216028473 / 4000000000000) 4 (IntervalRat.scale (587 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (34150329873 / 1000000000000) (34150329874 / 1000000000000), orderedInterval (50798027820 / 1000000000000) (50798027821 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1840383874187541 / 4000000000000) 4 (IntervalRat.scale (587 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (29885499299 / 1000000000000) (29885553689 / 1000000000000), orderedInterval (-22180243834 / 1000000000000) (-22180189444 / 1000000000000)))) (orderedInterval (-12649569318 / 1000000000000) (-12649545738 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1355618432057533 / 4000000000000) 4 (IntervalRat.scale (587 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (16783237088 / 1000000000000) (16783237089 / 1000000000000), orderedInterval (39935061381 / 1000000000000) (39935061382 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2322875289106609 / 4000000000000) 4 (IntervalRat.scale (587 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-10080393979 / 1000000000000) (-10080393978 / 1000000000000), orderedInterval (-31529355503 / 1000000000000) (-31529355502 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1711019424506131 / 4000000000000) 4 (IntervalRat.scale (587 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (36995537243 / 1000000000000) (36995537248 / 1000000000000), orderedInterval (10893445949 / 1000000000000) (10893445954 / 1000000000000)))) (orderedInterval (8855975503 / 1000000000000) (8855975676 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate422_chunkChecks4_1 :
    compactCertificate422.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2625143805584413 / 4000000000000) 4 (IntervalRat.scale (587 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-14335144787 / 1000000000000) (-14335144786 / 1000000000000), orderedInterval (-27639357376 / 1000000000000) (-27639357375 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1515627482815477 / 4000000000000) 4 (IntervalRat.scale (587 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (17487715002 / 1000000000000) (17487715493 / 1000000000000), orderedInterval (-37095022259 / 1000000000000) (-37095021767 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (2689507564977593 / 4000000000000) 4 (IntervalRat.scale (587 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (23344734375 / 1000000000000) (23344734376 / 1000000000000), orderedInterval (20028666320 / 1000000000000) (20028666321 / 1000000000000)))) (orderedInterval (159250247299 / 1000000000000) (159250249924 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2512886840947517 / 4000000000000) 4 (IntervalRat.scale (587 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (20223334261 / 1000000000000) (20223334262 / 1000000000000), orderedInterval (24568143250 / 1000000000000) (24568143251 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1793314621958861 / 4000000000000) 4 (IntervalRat.scale (587 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (5033432346 / 1000000000000) (5033432349 / 1000000000000), orderedInterval (-37350626316 / 1000000000000) (-37350626313 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2033427648085419 / 4000000000000) 4 (IntervalRat.scale (587 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (7171062615 / 1000000000000) (7171062616 / 1000000000000), orderedInterval (34646735869 / 1000000000000) (34646735870 / 1000000000000)))) (orderedInterval (-5520225961 / 1000000000000) (-5520225682 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1695259977484411 / 4000000000000) 4 (IntervalRat.scale (587 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-18071967776 / 1000000000000) (-18071967775 / 1000000000000), orderedInterval (-34264561723 / 1000000000000) (-34264561722 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1497813602184631 / 4000000000000) 4 (IntervalRat.scale (587 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-40552677870 / 1000000000000) (-40552677853 / 1000000000000), orderedInterval (-7403044536 / 1000000000000) (-7403044519 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (434124762002469 / 800000000000) 4 (IntervalRat.scale (587 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (1862653864 / 1000000000000) (1862653865 / 1000000000000), orderedInterval (-34202395127 / 1000000000000) (-34202395126 / 1000000000000)))) (orderedInterval (5758620650 / 1000000000000) (5758620801 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate422_chunkChecks4_2 :
    compactCertificate422.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1200811938433343 / 4000000000000) 4 (IntervalRat.scale (587 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-26188940539 / 1000000000000) (-26188935437 / 1000000000000), orderedInterval (37921995263 / 1000000000000) (37922000365 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1017941578838023 / 4000000000000) 4 (IntervalRat.scale (587 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-35924377550 / 1000000000000) (-35924377549 / 1000000000000), orderedInterval (-34729352401 / 1000000000000) (-34729352400 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (636980575493869 / 4000000000000) 4 (IntervalRat.scale (587 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (12032221704 / 1000000000000) (12032221781 / 1000000000000), orderedInterval (-62110141270 / 1000000000000) (-62110141194 / 1000000000000)))) (orderedInterval (5728579373 / 1000000000000) (5728580335 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (342570272002323 / 4000000000000) 4 (IntervalRat.scale (587 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-86170608981 / 1000000000000) (-86170608933 / 1000000000000), orderedInterval (3322651255 / 1000000000000) (3322651303 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (930144927895969 / 4000000000000) 4 (IntervalRat.scale (587 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (39074923212 / 1000000000000) (39074923213 / 1000000000000), orderedInterval (34713575660 / 1000000000000) (34713575661 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1270033378506113 / 4000000000000) 4 (IntervalRat.scale (587 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-37496445804 / 1000000000000) (-37496445803 / 1000000000000), orderedInterval (-24416746334 / 1000000000000) (-24416746333 / 1000000000000)))) (orderedInterval (3611342266 / 1000000000000) (3611342301 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (537019424506131 / 4000000000000) 4 (IntervalRat.scale (587 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (3383903829 / 1000000000000) (3383903840 / 1000000000000), orderedInterval (-68790921013 / 1000000000000) (-68790921002 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2182954146190451 / 4000000000000) 4 (IntervalRat.scale (587 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-3865367126 / 1000000000000) (-3865367124 / 1000000000000), orderedInterval (33938601590 / 1000000000000) (33938601592 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1458112202689309 / 4000000000000) 4 (IntervalRat.scale (587 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (32430747829 / 1000000000000) (32430747830 / 1000000000000), orderedInterval (26312075146 / 1000000000000) (26312075147 / 1000000000000)))) (orderedInterval (-10902461866 / 1000000000000) (-10902461446 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate422_chunkChecks4 :
    compactCertificate422.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate422.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate422_chunkChecks4_0
    compactCertificate422_chunkChecks4_1 compactCertificate422_chunkChecks4_2

theorem compactCertificate422_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate422.chunkCheck r b = true :=
  compactCertificate422.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate422_chunkChecks0
    · exact compactCertificate422_chunkChecks1
    · exact compactCertificate422_chunkChecks2
    · exact compactCertificate422_chunkChecks3
    · exact compactCertificate422_chunkChecks4)

theorem compactCertificate422_coefficient0 :
    compactCertificate422.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate422_coefficient1 :
    compactCertificate422.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate422_coefficient2 :
    compactCertificate422.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate422_coefficient3 :
    compactCertificate422.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate422_coefficient4 :
    compactCertificate422.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate422_coefficients : ∀ r : Fin 5,
    compactCertificate422.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate422_coefficient0
  · exact compactCertificate422_coefficient1
  · exact compactCertificate422_coefficient2
  · exact compactCertificate422_coefficient3
  · exact compactCertificate422_coefficient4

theorem compactCertificate422_lower : (1 : ℚ) ≤ compactCertificate422.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate422, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate422_proves {t : ℝ} (ht : t ∈ compactCertificate422.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate422.proves compactCertificate422_states compactCertificate422_chunks
    compactCertificate422_coefficients compactCertificate422_lower ht

end Erdos232
