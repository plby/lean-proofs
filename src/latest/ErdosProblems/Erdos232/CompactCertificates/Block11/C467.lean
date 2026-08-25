/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate467 : CompactCertificate where
  left := 338
  right := 339
  center := 677 / 2
  grid := fun i =>
    match i.val with
    | 0 => 108
    | 1 => 79
    | 2 => 128
    | 3 => 23
    | 4 => 62
    | 5 => 169
    | 6 => 124
    | 7 => 213
    | 8 => 157
    | 9 => 241
    | 10 => 139
    | 11 => 247
    | 12 => 231
    | 13 => 165
    | 14 => 187
    | 15 => 156
    | 16 => 138
    | 17 => 199
    | 18 => 110
    | 19 => 93
    | 20 => 58
    | 21 => 31
    | 22 => 85
    | 23 => 117
    | 24 => 49
    | 25 => 200
    | _ => 134
  point := fun i =>
    match i.val with
    | 0 => 677 / 2
    | 1 => 997350271728977 / 4000000000000
    | 2 => 322522586022641 / 800000000000
    | 3 => 291024321863539 / 4000000000000
    | 4 => 781732264482583 / 4000000000000
    | 5 => 2122555166652411 / 4000000000000
    | 6 => 1563464528965843 / 4000000000000
    | 7 => 2679023118782239 / 4000000000000
    | 8 => 1973356303902301 / 4000000000000
    | 9 => 3027636041534323 / 4000000000000
    | 10 => 1748006483587867 / 4000000000000
    | 11 => 3101868179710103 / 4000000000000
    | 12 => 2898167617242707 / 4000000000000
    | 13 => 2068269163656131 / 4000000000000
    | 14 => 2345196793447749 / 4000000000000
    | 15 => 1955180587320181 / 4000000000000
    | 16 => 1727461343575801 / 4000000000000
    | 17 => 500685628408299 / 800000000000
    | 18 => 1384922797818353 / 4000000000000
    | 19 => 1174014393310633 / 4000000000000
    | 20 => 734643696097699 / 4000000000000
    | 21 => 395093823075933 / 4000000000000
    | 22 => 1072756586346799 / 4000000000000
    | 23 => 1464757405875023 / 4000000000000
    | 24 => 619356303902301 / 4000000000000
    | 25 => 2517648989729021 / 4000000000000
    | _ => 1681672847053939 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-302600183 / 1000000000000) (-302600181 / 1000000000000), orderedInterval (43366549199 / 1000000000000) (43366549200 / 1000000000000))
    | 1 => (orderedInterval (-47185566842 / 1000000000000) (-47185559083 / 1000000000000), orderedInterval (18171213059 / 1000000000000) (18171220818 / 1000000000000))
    | 2 => (orderedInterval (38564046007 / 1000000000000) (38564050909 / 1000000000000), orderedInterval (-9635026756 / 1000000000000) (-9635021853 / 1000000000000))
    | 3 => (orderedInterval (-89696904531 / 1000000000000) (-89696904529 / 1000000000000), orderedInterval (-25923161107 / 1000000000000) (-25923161106 / 1000000000000))
    | 4 => (orderedInterval (56579885540 / 1000000000000) (56579885549 / 1000000000000), orderedInterval (7351154972 / 1000000000000) (7351154981 / 1000000000000))
    | 5 => (orderedInterval (-16447454701 / 1000000000000) (-16447454700 / 1000000000000), orderedInterval (-30467364965 / 1000000000000) (-30467364964 / 1000000000000))
    | 6 => (orderedInterval (34964299057 / 1000000000000) (34964364971 / 1000000000000), orderedInterval (-20200054495 / 1000000000000) (-20199988581 / 1000000000000))
    | 7 => (orderedInterval (-30281339080 / 1000000000000) (-30281338943 / 1000000000000), orderedInterval (-5770967863 / 1000000000000) (-5770967727 / 1000000000000))
    | 8 => (orderedInterval (-28008535337 / 1000000000000) (-28008535336 / 1000000000000), orderedInterval (-22464996103 / 1000000000000) (-22464996102 / 1000000000000))
    | 9 => (orderedInterval (-15660160769 / 1000000000000) (-15660160768 / 1000000000000), orderedInterval (-24399443785 / 1000000000000) (-24399443784 / 1000000000000))
    | 10 => (orderedInterval (-34107731353 / 1000000000000) (-34107731351 / 1000000000000), orderedInterval (-17091430871 / 1000000000000) (-17091430870 / 1000000000000))
    | 11 => (orderedInterval (-7887811771 / 1000000000000) (-7887811770 / 1000000000000), orderedInterval (-27540017198 / 1000000000000) (-27540017197 / 1000000000000))
    | 12 => (orderedInterval (11016119856 / 1000000000000) (11016119875 / 1000000000000), orderedInterval (-27526625981 / 1000000000000) (-27526625963 / 1000000000000))
    | 13 => (orderedInterval (17139897795 / 1000000000000) (17139898285 / 1000000000000), orderedInterval (-30634164296 / 1000000000000) (-30634163807 / 1000000000000))
    | 14 => (orderedInterval (12632783346 / 1000000000000) (12632783409 / 1000000000000), orderedInterval (-30444973322 / 1000000000000) (-30444973259 / 1000000000000))
    | 15 => (orderedInterval (-17560060716 / 1000000000000) (-17560060147 / 1000000000000), orderedInterval (31546856610 / 1000000000000) (31546857179 / 1000000000000))
    | 16 => (orderedInterval (-29819158875 / 1000000000000) (-29819116930 / 1000000000000), orderedInterval (24219935159 / 1000000000000) (24219977103 / 1000000000000))
    | 17 => (orderedInterval (-31716189544 / 1000000000000) (-31716189234 / 1000000000000), orderedInterval (-3333204909 / 1000000000000) (-3333204599 / 1000000000000))
    | 18 => (orderedInterval (42516996294 / 1000000000000) (42516996323 / 1000000000000), orderedInterval (5508046086 / 1000000000000) (5508046116 / 1000000000000))
    | 19 => (orderedInterval (-39712877954 / 1000000000000) (-39712823770 / 1000000000000), orderedInterval (24397105794 / 1000000000000) (24397159978 / 1000000000000))
    | 20 => (orderedInterval (46421390340 / 1000000000000) (46421479038 / 1000000000000), orderedInterval (-36338639219 / 1000000000000) (-36338550521 / 1000000000000))
    | 21 => (orderedInterval (-66376190578 / 1000000000000) (-66376155924 / 1000000000000), orderedInterval (45495965991 / 1000000000000) (45496000645 / 1000000000000))
    | 22 => (orderedInterval (-45461006792 / 1000000000000) (-45460998068 / 1000000000000), orderedInterval (17608042587 / 1000000000000) (17608051311 / 1000000000000))
    | 23 => (orderedInterval (23264532752 / 1000000000000) (23264535857 / 1000000000000), orderedInterval (-34633225511 / 1000000000000) (-34633222406 / 1000000000000))
    | 24 => (orderedInterval (-63698472232 / 1000000000000) (-63698471987 / 1000000000000), orderedInterval (7552577210 / 1000000000000) (7552577455 / 1000000000000))
    | 25 => (orderedInterval (30305536821 / 1000000000000) (30305565371 / 1000000000000), orderedInterval (-9669008840 / 1000000000000) (-9668980290 / 1000000000000))
    | _ => (orderedInterval (8867478257 / 1000000000000) (8867478258 / 1000000000000), orderedInterval (37879061349 / 1000000000000) (37879061350 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (1703364108 / 1000000000000) (1703364493 / 1000000000000)
      | 1 => orderedInterval (4208221858 / 1000000000000) (4208221900 / 1000000000000)
      | 2 => orderedInterval (257086601 / 1000000000000) (257086624 / 1000000000000)
      | 3 => orderedInterval (-865779718 / 1000000000000) (-865779584 / 1000000000000)
      | 4 => orderedInterval (1357993718 / 1000000000000) (1357993806 / 1000000000000)
      | 5 => orderedInterval (691611439 / 1000000000000) (691613887 / 1000000000000)
      | 6 => orderedInterval (-3039141391 / 1000000000000) (-3039135346 / 1000000000000)
      | 7 => orderedInterval (474043115 / 1000000000000) (474044232 / 1000000000000)
      | _ => orderedInterval (-4514696354 / 1000000000000) (-4514693934 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (16640318407 / 1000000000000) (16640318830 / 1000000000000)
      | 1 => orderedInterval (3610739780 / 1000000000000) (3610739827 / 1000000000000)
      | 2 => orderedInterval (-439097562 / 1000000000000) (-439097520 / 1000000000000)
      | 3 => orderedInterval (-909175855 / 1000000000000) (-909175576 / 1000000000000)
      | 4 => orderedInterval (-3094486896 / 1000000000000) (-3094486758 / 1000000000000)
      | 5 => orderedInterval (-1400076676 / 1000000000000) (-1400073543 / 1000000000000)
      | 6 => orderedInterval (-2739999541 / 1000000000000) (-2739995232 / 1000000000000)
      | 7 => orderedInterval (2309737264 / 1000000000000) (2309737902 / 1000000000000)
      | _ => orderedInterval (-7342743655 / 1000000000000) (-7342739201 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-2900654973 / 1000000000000) (-2900654493 / 1000000000000)
      | 1 => orderedInterval (-3617565376 / 1000000000000) (-3617565311 / 1000000000000)
      | 2 => orderedInterval (-2217344970 / 1000000000000) (-2217344894 / 1000000000000)
      | 3 => orderedInterval (-3813797787 / 1000000000000) (-3813797189 / 1000000000000)
      | 4 => orderedInterval (-2669782810 / 1000000000000) (-2669782591 / 1000000000000)
      | 5 => orderedInterval (425343744 / 1000000000000) (425347771 / 1000000000000)
      | 6 => orderedInterval (4985522004 / 1000000000000) (4985525252 / 1000000000000)
      | 7 => orderedInterval (1328001238 / 1000000000000) (1328001734 / 1000000000000)
      | _ => orderedInterval (11197743611 / 1000000000000) (11197751854 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-16292756728 / 1000000000000) (-16292756176 / 1000000000000)
      | 1 => orderedInterval (-8387495737 / 1000000000000) (-8387495641 / 1000000000000)
      | 2 => orderedInterval (308542836 / 1000000000000) (308542976 / 1000000000000)
      | 3 => orderedInterval (1333642664 / 1000000000000) (1333643974 / 1000000000000)
      | 4 => orderedInterval (4659082873 / 1000000000000) (4659083227 / 1000000000000)
      | 5 => orderedInterval (2319600099 / 1000000000000) (2319605273 / 1000000000000)
      | 6 => orderedInterval (2016786409 / 1000000000000) (2016788957 / 1000000000000)
      | 7 => orderedInterval (-3144699853 / 1000000000000) (-3144699398 / 1000000000000)
      | _ => orderedInterval (8518947553 / 1000000000000) (8518962817 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (4400171808 / 1000000000000) (4400172454 / 1000000000000)
      | 1 => orderedInterval (7342140334 / 1000000000000) (7342140482 / 1000000000000)
      | 2 => orderedInterval (11258613670 / 1000000000000) (11258613933 / 1000000000000)
      | 3 => orderedInterval (31653428394 / 1000000000000) (31653431303 / 1000000000000)
      | 4 => orderedInterval (4046978511 / 1000000000000) (4046979093 / 1000000000000)
      | 5 => orderedInterval (-5863892972 / 1000000000000) (-5863886290 / 1000000000000)
      | 6 => orderedInterval (-6051202130 / 1000000000000) (-6051200055 / 1000000000000)
      | 7 => orderedInterval (-2008053315 / 1000000000000) (-2008052865 / 1000000000000)
      | _ => orderedInterval (-33515205988 / 1000000000000) (-33515177636 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (272703376 / 1000000000000) (272716078 / 1000000000000)
    | 1 => orderedInterval (6635215266 / 1000000000000) (6635228729 / 1000000000000)
    | 2 => orderedInterval (2717464681 / 1000000000000) (2717482133 / 1000000000000)
    | 3 => orderedInterval (-8668349884 / 1000000000000) (-8668323991 / 1000000000000)
    | _ => orderedInterval (11262978312 / 1000000000000) (11263020419 / 1000000000000)

theorem compactCertificate467_stateChecks0 :
    compactCertificate467.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 108 12 (677 / 2)) (orderedInterval (-302600183 / 1000000000000) (-302600181 / 1000000000000), orderedInterval (43366549199 / 1000000000000) (43366549200 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 79 12 (997350271728977 / 4000000000000)) (orderedInterval (-47185566842 / 1000000000000) (-47185559083 / 1000000000000), orderedInterval (18171213059 / 1000000000000) (18171220818 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 128 12 (322522586022641 / 800000000000)) (orderedInterval (38564046007 / 1000000000000) (38564050909 / 1000000000000), orderedInterval (-9635026756 / 1000000000000) (-9635021853 / 1000000000000))) = true
  rfl'

theorem compactCertificate467_stateChecks1 :
    compactCertificate467.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 23 12 (291024321863539 / 4000000000000)) (orderedInterval (-89696904531 / 1000000000000) (-89696904529 / 1000000000000), orderedInterval (-25923161107 / 1000000000000) (-25923161106 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (781732264482583 / 4000000000000)) (orderedInterval (56579885540 / 1000000000000) (56579885549 / 1000000000000), orderedInterval (7351154972 / 1000000000000) (7351154981 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 169 12 (2122555166652411 / 4000000000000)) (orderedInterval (-16447454701 / 1000000000000) (-16447454700 / 1000000000000), orderedInterval (-30467364965 / 1000000000000) (-30467364964 / 1000000000000))) = true
  rfl'

theorem compactCertificate467_stateChecks2 :
    compactCertificate467.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 124 12 (1563464528965843 / 4000000000000)) (orderedInterval (34964299057 / 1000000000000) (34964364971 / 1000000000000), orderedInterval (-20200054495 / 1000000000000) (-20199988581 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 213 12 (2679023118782239 / 4000000000000)) (orderedInterval (-30281339080 / 1000000000000) (-30281338943 / 1000000000000), orderedInterval (-5770967863 / 1000000000000) (-5770967727 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 157 12 (1973356303902301 / 4000000000000)) (orderedInterval (-28008535337 / 1000000000000) (-28008535336 / 1000000000000), orderedInterval (-22464996103 / 1000000000000) (-22464996102 / 1000000000000))) = true
  rfl'

theorem compactCertificate467_stateChecks3 :
    compactCertificate467.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 241 12 (3027636041534323 / 4000000000000)) (orderedInterval (-15660160769 / 1000000000000) (-15660160768 / 1000000000000), orderedInterval (-24399443785 / 1000000000000) (-24399443784 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 139 12 (1748006483587867 / 4000000000000)) (orderedInterval (-34107731353 / 1000000000000) (-34107731351 / 1000000000000), orderedInterval (-17091430871 / 1000000000000) (-17091430870 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 247 12 (3101868179710103 / 4000000000000)) (orderedInterval (-7887811771 / 1000000000000) (-7887811770 / 1000000000000), orderedInterval (-27540017198 / 1000000000000) (-27540017197 / 1000000000000))) = true
  rfl'

theorem compactCertificate467_stateChecks4 :
    compactCertificate467.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 231 12 (2898167617242707 / 4000000000000)) (orderedInterval (11016119856 / 1000000000000) (11016119875 / 1000000000000), orderedInterval (-27526625981 / 1000000000000) (-27526625963 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 165 12 (2068269163656131 / 4000000000000)) (orderedInterval (17139897795 / 1000000000000) (17139898285 / 1000000000000), orderedInterval (-30634164296 / 1000000000000) (-30634163807 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 187 12 (2345196793447749 / 4000000000000)) (orderedInterval (12632783346 / 1000000000000) (12632783409 / 1000000000000), orderedInterval (-30444973322 / 1000000000000) (-30444973259 / 1000000000000))) = true
  rfl'

theorem compactCertificate467_stateChecks5 :
    compactCertificate467.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 156 12 (1955180587320181 / 4000000000000)) (orderedInterval (-17560060716 / 1000000000000) (-17560060147 / 1000000000000), orderedInterval (31546856610 / 1000000000000) (31546857179 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 138 12 (1727461343575801 / 4000000000000)) (orderedInterval (-29819158875 / 1000000000000) (-29819116930 / 1000000000000), orderedInterval (24219935159 / 1000000000000) (24219977103 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 199 12 (500685628408299 / 800000000000)) (orderedInterval (-31716189544 / 1000000000000) (-31716189234 / 1000000000000), orderedInterval (-3333204909 / 1000000000000) (-3333204599 / 1000000000000))) = true
  rfl'

theorem compactCertificate467_stateChecks6 :
    compactCertificate467.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 110 12 (1384922797818353 / 4000000000000)) (orderedInterval (42516996294 / 1000000000000) (42516996323 / 1000000000000), orderedInterval (5508046086 / 1000000000000) (5508046116 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 93 12 (1174014393310633 / 4000000000000)) (orderedInterval (-39712877954 / 1000000000000) (-39712823770 / 1000000000000), orderedInterval (24397105794 / 1000000000000) (24397159978 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (734643696097699 / 4000000000000)) (orderedInterval (46421390340 / 1000000000000) (46421479038 / 1000000000000), orderedInterval (-36338639219 / 1000000000000) (-36338550521 / 1000000000000))) = true
  rfl'

theorem compactCertificate467_stateChecks7 :
    compactCertificate467.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 31 12 (395093823075933 / 4000000000000)) (orderedInterval (-66376190578 / 1000000000000) (-66376155924 / 1000000000000), orderedInterval (45495965991 / 1000000000000) (45496000645 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 85 12 (1072756586346799 / 4000000000000)) (orderedInterval (-45461006792 / 1000000000000) (-45460998068 / 1000000000000), orderedInterval (17608042587 / 1000000000000) (17608051311 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 117 12 (1464757405875023 / 4000000000000)) (orderedInterval (23264532752 / 1000000000000) (23264535857 / 1000000000000), orderedInterval (-34633225511 / 1000000000000) (-34633222406 / 1000000000000))) = true
  rfl'

theorem compactCertificate467_stateChecks8 :
    compactCertificate467.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 49 12 (619356303902301 / 4000000000000)) (orderedInterval (-63698472232 / 1000000000000) (-63698471987 / 1000000000000), orderedInterval (7552577210 / 1000000000000) (7552577455 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 200 12 (2517648989729021 / 4000000000000)) (orderedInterval (30305536821 / 1000000000000) (30305565371 / 1000000000000), orderedInterval (-9669008840 / 1000000000000) (-9668980290 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 134 12 (1681672847053939 / 4000000000000)) (orderedInterval (8867478257 / 1000000000000) (8867478258 / 1000000000000), orderedInterval (37879061349 / 1000000000000) (37879061350 / 1000000000000))) = true
  rfl'

theorem compactCertificate467_states : ∀ j,
    BesselStateValid (compactCertificate467.point j) (compactCertificate467.state j) :=
  compactCertificate467.statesValid_of_checks3 compactCertificate467_stateChecks0
    compactCertificate467_stateChecks1 compactCertificate467_stateChecks2
    compactCertificate467_stateChecks3 compactCertificate467_stateChecks4
    compactCertificate467_stateChecks5 compactCertificate467_stateChecks6
    compactCertificate467_stateChecks7 compactCertificate467_stateChecks8

theorem compactCertificate467_chunkChecks0_0 :
    compactCertificate467.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (677 / 2) 0 (IntervalRat.scale (677 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-302600183 / 1000000000000) (-302600181 / 1000000000000), orderedInterval (43366549199 / 1000000000000) (43366549200 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (997350271728977 / 4000000000000) 0 (IntervalRat.scale (677 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-47185566842 / 1000000000000) (-47185559083 / 1000000000000), orderedInterval (18171213059 / 1000000000000) (18171220818 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (322522586022641 / 800000000000) 0 (IntervalRat.scale (677 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (38564046007 / 1000000000000) (38564050909 / 1000000000000), orderedInterval (-9635026756 / 1000000000000) (-9635021853 / 1000000000000)))) (orderedInterval (1703364108 / 1000000000000) (1703364493 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (291024321863539 / 4000000000000) 0 (IntervalRat.scale (677 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-89696904531 / 1000000000000) (-89696904529 / 1000000000000), orderedInterval (-25923161107 / 1000000000000) (-25923161106 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (781732264482583 / 4000000000000) 0 (IntervalRat.scale (677 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (56579885540 / 1000000000000) (56579885549 / 1000000000000), orderedInterval (7351154972 / 1000000000000) (7351154981 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2122555166652411 / 4000000000000) 0 (IntervalRat.scale (677 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-16447454701 / 1000000000000) (-16447454700 / 1000000000000), orderedInterval (-30467364965 / 1000000000000) (-30467364964 / 1000000000000)))) (orderedInterval (4208221858 / 1000000000000) (4208221900 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1563464528965843 / 4000000000000) 0 (IntervalRat.scale (677 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (34964299057 / 1000000000000) (34964364971 / 1000000000000), orderedInterval (-20200054495 / 1000000000000) (-20199988581 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2679023118782239 / 4000000000000) 0 (IntervalRat.scale (677 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-30281339080 / 1000000000000) (-30281338943 / 1000000000000), orderedInterval (-5770967863 / 1000000000000) (-5770967727 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1973356303902301 / 4000000000000) 0 (IntervalRat.scale (677 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-28008535337 / 1000000000000) (-28008535336 / 1000000000000), orderedInterval (-22464996103 / 1000000000000) (-22464996102 / 1000000000000)))) (orderedInterval (257086601 / 1000000000000) (257086624 / 1000000000000))) = true
  rfl'

theorem compactCertificate467_chunkChecks0_1 :
    compactCertificate467.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3027636041534323 / 4000000000000) 0 (IntervalRat.scale (677 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-15660160769 / 1000000000000) (-15660160768 / 1000000000000), orderedInterval (-24399443785 / 1000000000000) (-24399443784 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1748006483587867 / 4000000000000) 0 (IntervalRat.scale (677 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-34107731353 / 1000000000000) (-34107731351 / 1000000000000), orderedInterval (-17091430871 / 1000000000000) (-17091430870 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3101868179710103 / 4000000000000) 0 (IntervalRat.scale (677 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-7887811771 / 1000000000000) (-7887811770 / 1000000000000), orderedInterval (-27540017198 / 1000000000000) (-27540017197 / 1000000000000)))) (orderedInterval (-865779718 / 1000000000000) (-865779584 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2898167617242707 / 4000000000000) 0 (IntervalRat.scale (677 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (11016119856 / 1000000000000) (11016119875 / 1000000000000), orderedInterval (-27526625981 / 1000000000000) (-27526625963 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2068269163656131 / 4000000000000) 0 (IntervalRat.scale (677 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (17139897795 / 1000000000000) (17139898285 / 1000000000000), orderedInterval (-30634164296 / 1000000000000) (-30634163807 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2345196793447749 / 4000000000000) 0 (IntervalRat.scale (677 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (12632783346 / 1000000000000) (12632783409 / 1000000000000), orderedInterval (-30444973322 / 1000000000000) (-30444973259 / 1000000000000)))) (orderedInterval (1357993718 / 1000000000000) (1357993806 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1955180587320181 / 4000000000000) 0 (IntervalRat.scale (677 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-17560060716 / 1000000000000) (-17560060147 / 1000000000000), orderedInterval (31546856610 / 1000000000000) (31546857179 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1727461343575801 / 4000000000000) 0 (IntervalRat.scale (677 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-29819158875 / 1000000000000) (-29819116930 / 1000000000000), orderedInterval (24219935159 / 1000000000000) (24219977103 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (500685628408299 / 800000000000) 0 (IntervalRat.scale (677 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-31716189544 / 1000000000000) (-31716189234 / 1000000000000), orderedInterval (-3333204909 / 1000000000000) (-3333204599 / 1000000000000)))) (orderedInterval (691611439 / 1000000000000) (691613887 / 1000000000000))) = true
  rfl'

theorem compactCertificate467_chunkChecks0_2 :
    compactCertificate467.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1384922797818353 / 4000000000000) 0 (IntervalRat.scale (677 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (42516996294 / 1000000000000) (42516996323 / 1000000000000), orderedInterval (5508046086 / 1000000000000) (5508046116 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1174014393310633 / 4000000000000) 0 (IntervalRat.scale (677 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-39712877954 / 1000000000000) (-39712823770 / 1000000000000), orderedInterval (24397105794 / 1000000000000) (24397159978 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (734643696097699 / 4000000000000) 0 (IntervalRat.scale (677 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (46421390340 / 1000000000000) (46421479038 / 1000000000000), orderedInterval (-36338639219 / 1000000000000) (-36338550521 / 1000000000000)))) (orderedInterval (-3039141391 / 1000000000000) (-3039135346 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (395093823075933 / 4000000000000) 0 (IntervalRat.scale (677 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-66376190578 / 1000000000000) (-66376155924 / 1000000000000), orderedInterval (45495965991 / 1000000000000) (45496000645 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1072756586346799 / 4000000000000) 0 (IntervalRat.scale (677 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-45461006792 / 1000000000000) (-45460998068 / 1000000000000), orderedInterval (17608042587 / 1000000000000) (17608051311 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1464757405875023 / 4000000000000) 0 (IntervalRat.scale (677 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (23264532752 / 1000000000000) (23264535857 / 1000000000000), orderedInterval (-34633225511 / 1000000000000) (-34633222406 / 1000000000000)))) (orderedInterval (474043115 / 1000000000000) (474044232 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (619356303902301 / 4000000000000) 0 (IntervalRat.scale (677 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-63698472232 / 1000000000000) (-63698471987 / 1000000000000), orderedInterval (7552577210 / 1000000000000) (7552577455 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2517648989729021 / 4000000000000) 0 (IntervalRat.scale (677 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (30305536821 / 1000000000000) (30305565371 / 1000000000000), orderedInterval (-9669008840 / 1000000000000) (-9668980290 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1681672847053939 / 4000000000000) 0 (IntervalRat.scale (677 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (8867478257 / 1000000000000) (8867478258 / 1000000000000), orderedInterval (37879061349 / 1000000000000) (37879061350 / 1000000000000)))) (orderedInterval (-4514696354 / 1000000000000) (-4514693934 / 1000000000000))) = true
  rfl'

theorem compactCertificate467_chunkChecks0 :
    compactCertificate467.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate467.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate467_chunkChecks0_0
    compactCertificate467_chunkChecks0_1 compactCertificate467_chunkChecks0_2

theorem compactCertificate467_chunkChecks1_0 :
    compactCertificate467.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (677 / 2) 1 (IntervalRat.scale (677 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-302600183 / 1000000000000) (-302600181 / 1000000000000), orderedInterval (43366549199 / 1000000000000) (43366549200 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (997350271728977 / 4000000000000) 1 (IntervalRat.scale (677 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-47185566842 / 1000000000000) (-47185559083 / 1000000000000), orderedInterval (18171213059 / 1000000000000) (18171220818 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (322522586022641 / 800000000000) 1 (IntervalRat.scale (677 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (38564046007 / 1000000000000) (38564050909 / 1000000000000), orderedInterval (-9635026756 / 1000000000000) (-9635021853 / 1000000000000)))) (orderedInterval (16640318407 / 1000000000000) (16640318830 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (291024321863539 / 4000000000000) 1 (IntervalRat.scale (677 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-89696904531 / 1000000000000) (-89696904529 / 1000000000000), orderedInterval (-25923161107 / 1000000000000) (-25923161106 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (781732264482583 / 4000000000000) 1 (IntervalRat.scale (677 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (56579885540 / 1000000000000) (56579885549 / 1000000000000), orderedInterval (7351154972 / 1000000000000) (7351154981 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2122555166652411 / 4000000000000) 1 (IntervalRat.scale (677 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-16447454701 / 1000000000000) (-16447454700 / 1000000000000), orderedInterval (-30467364965 / 1000000000000) (-30467364964 / 1000000000000)))) (orderedInterval (3610739780 / 1000000000000) (3610739827 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1563464528965843 / 4000000000000) 1 (IntervalRat.scale (677 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (34964299057 / 1000000000000) (34964364971 / 1000000000000), orderedInterval (-20200054495 / 1000000000000) (-20199988581 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2679023118782239 / 4000000000000) 1 (IntervalRat.scale (677 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-30281339080 / 1000000000000) (-30281338943 / 1000000000000), orderedInterval (-5770967863 / 1000000000000) (-5770967727 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1973356303902301 / 4000000000000) 1 (IntervalRat.scale (677 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-28008535337 / 1000000000000) (-28008535336 / 1000000000000), orderedInterval (-22464996103 / 1000000000000) (-22464996102 / 1000000000000)))) (orderedInterval (-439097562 / 1000000000000) (-439097520 / 1000000000000))) = true
  rfl'

theorem compactCertificate467_chunkChecks1_1 :
    compactCertificate467.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3027636041534323 / 4000000000000) 1 (IntervalRat.scale (677 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-15660160769 / 1000000000000) (-15660160768 / 1000000000000), orderedInterval (-24399443785 / 1000000000000) (-24399443784 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1748006483587867 / 4000000000000) 1 (IntervalRat.scale (677 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-34107731353 / 1000000000000) (-34107731351 / 1000000000000), orderedInterval (-17091430871 / 1000000000000) (-17091430870 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3101868179710103 / 4000000000000) 1 (IntervalRat.scale (677 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-7887811771 / 1000000000000) (-7887811770 / 1000000000000), orderedInterval (-27540017198 / 1000000000000) (-27540017197 / 1000000000000)))) (orderedInterval (-909175855 / 1000000000000) (-909175576 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2898167617242707 / 4000000000000) 1 (IntervalRat.scale (677 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (11016119856 / 1000000000000) (11016119875 / 1000000000000), orderedInterval (-27526625981 / 1000000000000) (-27526625963 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2068269163656131 / 4000000000000) 1 (IntervalRat.scale (677 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (17139897795 / 1000000000000) (17139898285 / 1000000000000), orderedInterval (-30634164296 / 1000000000000) (-30634163807 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2345196793447749 / 4000000000000) 1 (IntervalRat.scale (677 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (12632783346 / 1000000000000) (12632783409 / 1000000000000), orderedInterval (-30444973322 / 1000000000000) (-30444973259 / 1000000000000)))) (orderedInterval (-3094486896 / 1000000000000) (-3094486758 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1955180587320181 / 4000000000000) 1 (IntervalRat.scale (677 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-17560060716 / 1000000000000) (-17560060147 / 1000000000000), orderedInterval (31546856610 / 1000000000000) (31546857179 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1727461343575801 / 4000000000000) 1 (IntervalRat.scale (677 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-29819158875 / 1000000000000) (-29819116930 / 1000000000000), orderedInterval (24219935159 / 1000000000000) (24219977103 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (500685628408299 / 800000000000) 1 (IntervalRat.scale (677 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-31716189544 / 1000000000000) (-31716189234 / 1000000000000), orderedInterval (-3333204909 / 1000000000000) (-3333204599 / 1000000000000)))) (orderedInterval (-1400076676 / 1000000000000) (-1400073543 / 1000000000000))) = true
  rfl'

theorem compactCertificate467_chunkChecks1_2 :
    compactCertificate467.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1384922797818353 / 4000000000000) 1 (IntervalRat.scale (677 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (42516996294 / 1000000000000) (42516996323 / 1000000000000), orderedInterval (5508046086 / 1000000000000) (5508046116 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1174014393310633 / 4000000000000) 1 (IntervalRat.scale (677 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-39712877954 / 1000000000000) (-39712823770 / 1000000000000), orderedInterval (24397105794 / 1000000000000) (24397159978 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (734643696097699 / 4000000000000) 1 (IntervalRat.scale (677 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (46421390340 / 1000000000000) (46421479038 / 1000000000000), orderedInterval (-36338639219 / 1000000000000) (-36338550521 / 1000000000000)))) (orderedInterval (-2739999541 / 1000000000000) (-2739995232 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (395093823075933 / 4000000000000) 1 (IntervalRat.scale (677 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-66376190578 / 1000000000000) (-66376155924 / 1000000000000), orderedInterval (45495965991 / 1000000000000) (45496000645 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1072756586346799 / 4000000000000) 1 (IntervalRat.scale (677 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-45461006792 / 1000000000000) (-45460998068 / 1000000000000), orderedInterval (17608042587 / 1000000000000) (17608051311 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1464757405875023 / 4000000000000) 1 (IntervalRat.scale (677 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (23264532752 / 1000000000000) (23264535857 / 1000000000000), orderedInterval (-34633225511 / 1000000000000) (-34633222406 / 1000000000000)))) (orderedInterval (2309737264 / 1000000000000) (2309737902 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (619356303902301 / 4000000000000) 1 (IntervalRat.scale (677 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-63698472232 / 1000000000000) (-63698471987 / 1000000000000), orderedInterval (7552577210 / 1000000000000) (7552577455 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2517648989729021 / 4000000000000) 1 (IntervalRat.scale (677 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (30305536821 / 1000000000000) (30305565371 / 1000000000000), orderedInterval (-9669008840 / 1000000000000) (-9668980290 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1681672847053939 / 4000000000000) 1 (IntervalRat.scale (677 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (8867478257 / 1000000000000) (8867478258 / 1000000000000), orderedInterval (37879061349 / 1000000000000) (37879061350 / 1000000000000)))) (orderedInterval (-7342743655 / 1000000000000) (-7342739201 / 1000000000000))) = true
  rfl'

theorem compactCertificate467_chunkChecks1 :
    compactCertificate467.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate467.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate467_chunkChecks1_0
    compactCertificate467_chunkChecks1_1 compactCertificate467_chunkChecks1_2

theorem compactCertificate467_chunkChecks2_0 :
    compactCertificate467.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (677 / 2) 2 (IntervalRat.scale (677 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-302600183 / 1000000000000) (-302600181 / 1000000000000), orderedInterval (43366549199 / 1000000000000) (43366549200 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (997350271728977 / 4000000000000) 2 (IntervalRat.scale (677 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-47185566842 / 1000000000000) (-47185559083 / 1000000000000), orderedInterval (18171213059 / 1000000000000) (18171220818 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (322522586022641 / 800000000000) 2 (IntervalRat.scale (677 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (38564046007 / 1000000000000) (38564050909 / 1000000000000), orderedInterval (-9635026756 / 1000000000000) (-9635021853 / 1000000000000)))) (orderedInterval (-2900654973 / 1000000000000) (-2900654493 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (291024321863539 / 4000000000000) 2 (IntervalRat.scale (677 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-89696904531 / 1000000000000) (-89696904529 / 1000000000000), orderedInterval (-25923161107 / 1000000000000) (-25923161106 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (781732264482583 / 4000000000000) 2 (IntervalRat.scale (677 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (56579885540 / 1000000000000) (56579885549 / 1000000000000), orderedInterval (7351154972 / 1000000000000) (7351154981 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2122555166652411 / 4000000000000) 2 (IntervalRat.scale (677 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-16447454701 / 1000000000000) (-16447454700 / 1000000000000), orderedInterval (-30467364965 / 1000000000000) (-30467364964 / 1000000000000)))) (orderedInterval (-3617565376 / 1000000000000) (-3617565311 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1563464528965843 / 4000000000000) 2 (IntervalRat.scale (677 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (34964299057 / 1000000000000) (34964364971 / 1000000000000), orderedInterval (-20200054495 / 1000000000000) (-20199988581 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2679023118782239 / 4000000000000) 2 (IntervalRat.scale (677 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-30281339080 / 1000000000000) (-30281338943 / 1000000000000), orderedInterval (-5770967863 / 1000000000000) (-5770967727 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1973356303902301 / 4000000000000) 2 (IntervalRat.scale (677 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-28008535337 / 1000000000000) (-28008535336 / 1000000000000), orderedInterval (-22464996103 / 1000000000000) (-22464996102 / 1000000000000)))) (orderedInterval (-2217344970 / 1000000000000) (-2217344894 / 1000000000000))) = true
  rfl'

theorem compactCertificate467_chunkChecks2_1 :
    compactCertificate467.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3027636041534323 / 4000000000000) 2 (IntervalRat.scale (677 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-15660160769 / 1000000000000) (-15660160768 / 1000000000000), orderedInterval (-24399443785 / 1000000000000) (-24399443784 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1748006483587867 / 4000000000000) 2 (IntervalRat.scale (677 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-34107731353 / 1000000000000) (-34107731351 / 1000000000000), orderedInterval (-17091430871 / 1000000000000) (-17091430870 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3101868179710103 / 4000000000000) 2 (IntervalRat.scale (677 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-7887811771 / 1000000000000) (-7887811770 / 1000000000000), orderedInterval (-27540017198 / 1000000000000) (-27540017197 / 1000000000000)))) (orderedInterval (-3813797787 / 1000000000000) (-3813797189 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2898167617242707 / 4000000000000) 2 (IntervalRat.scale (677 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (11016119856 / 1000000000000) (11016119875 / 1000000000000), orderedInterval (-27526625981 / 1000000000000) (-27526625963 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2068269163656131 / 4000000000000) 2 (IntervalRat.scale (677 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (17139897795 / 1000000000000) (17139898285 / 1000000000000), orderedInterval (-30634164296 / 1000000000000) (-30634163807 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2345196793447749 / 4000000000000) 2 (IntervalRat.scale (677 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (12632783346 / 1000000000000) (12632783409 / 1000000000000), orderedInterval (-30444973322 / 1000000000000) (-30444973259 / 1000000000000)))) (orderedInterval (-2669782810 / 1000000000000) (-2669782591 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1955180587320181 / 4000000000000) 2 (IntervalRat.scale (677 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-17560060716 / 1000000000000) (-17560060147 / 1000000000000), orderedInterval (31546856610 / 1000000000000) (31546857179 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1727461343575801 / 4000000000000) 2 (IntervalRat.scale (677 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-29819158875 / 1000000000000) (-29819116930 / 1000000000000), orderedInterval (24219935159 / 1000000000000) (24219977103 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (500685628408299 / 800000000000) 2 (IntervalRat.scale (677 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-31716189544 / 1000000000000) (-31716189234 / 1000000000000), orderedInterval (-3333204909 / 1000000000000) (-3333204599 / 1000000000000)))) (orderedInterval (425343744 / 1000000000000) (425347771 / 1000000000000))) = true
  rfl'

theorem compactCertificate467_chunkChecks2_2 :
    compactCertificate467.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1384922797818353 / 4000000000000) 2 (IntervalRat.scale (677 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (42516996294 / 1000000000000) (42516996323 / 1000000000000), orderedInterval (5508046086 / 1000000000000) (5508046116 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1174014393310633 / 4000000000000) 2 (IntervalRat.scale (677 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-39712877954 / 1000000000000) (-39712823770 / 1000000000000), orderedInterval (24397105794 / 1000000000000) (24397159978 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (734643696097699 / 4000000000000) 2 (IntervalRat.scale (677 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (46421390340 / 1000000000000) (46421479038 / 1000000000000), orderedInterval (-36338639219 / 1000000000000) (-36338550521 / 1000000000000)))) (orderedInterval (4985522004 / 1000000000000) (4985525252 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (395093823075933 / 4000000000000) 2 (IntervalRat.scale (677 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-66376190578 / 1000000000000) (-66376155924 / 1000000000000), orderedInterval (45495965991 / 1000000000000) (45496000645 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1072756586346799 / 4000000000000) 2 (IntervalRat.scale (677 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-45461006792 / 1000000000000) (-45460998068 / 1000000000000), orderedInterval (17608042587 / 1000000000000) (17608051311 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1464757405875023 / 4000000000000) 2 (IntervalRat.scale (677 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (23264532752 / 1000000000000) (23264535857 / 1000000000000), orderedInterval (-34633225511 / 1000000000000) (-34633222406 / 1000000000000)))) (orderedInterval (1328001238 / 1000000000000) (1328001734 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (619356303902301 / 4000000000000) 2 (IntervalRat.scale (677 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-63698472232 / 1000000000000) (-63698471987 / 1000000000000), orderedInterval (7552577210 / 1000000000000) (7552577455 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2517648989729021 / 4000000000000) 2 (IntervalRat.scale (677 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (30305536821 / 1000000000000) (30305565371 / 1000000000000), orderedInterval (-9669008840 / 1000000000000) (-9668980290 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1681672847053939 / 4000000000000) 2 (IntervalRat.scale (677 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (8867478257 / 1000000000000) (8867478258 / 1000000000000), orderedInterval (37879061349 / 1000000000000) (37879061350 / 1000000000000)))) (orderedInterval (11197743611 / 1000000000000) (11197751854 / 1000000000000))) = true
  rfl'

theorem compactCertificate467_chunkChecks2 :
    compactCertificate467.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate467.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate467_chunkChecks2_0
    compactCertificate467_chunkChecks2_1 compactCertificate467_chunkChecks2_2

theorem compactCertificate467_chunkChecks3_0 :
    compactCertificate467.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (677 / 2) 3 (IntervalRat.scale (677 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-302600183 / 1000000000000) (-302600181 / 1000000000000), orderedInterval (43366549199 / 1000000000000) (43366549200 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (997350271728977 / 4000000000000) 3 (IntervalRat.scale (677 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-47185566842 / 1000000000000) (-47185559083 / 1000000000000), orderedInterval (18171213059 / 1000000000000) (18171220818 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (322522586022641 / 800000000000) 3 (IntervalRat.scale (677 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (38564046007 / 1000000000000) (38564050909 / 1000000000000), orderedInterval (-9635026756 / 1000000000000) (-9635021853 / 1000000000000)))) (orderedInterval (-16292756728 / 1000000000000) (-16292756176 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (291024321863539 / 4000000000000) 3 (IntervalRat.scale (677 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-89696904531 / 1000000000000) (-89696904529 / 1000000000000), orderedInterval (-25923161107 / 1000000000000) (-25923161106 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (781732264482583 / 4000000000000) 3 (IntervalRat.scale (677 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (56579885540 / 1000000000000) (56579885549 / 1000000000000), orderedInterval (7351154972 / 1000000000000) (7351154981 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2122555166652411 / 4000000000000) 3 (IntervalRat.scale (677 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-16447454701 / 1000000000000) (-16447454700 / 1000000000000), orderedInterval (-30467364965 / 1000000000000) (-30467364964 / 1000000000000)))) (orderedInterval (-8387495737 / 1000000000000) (-8387495641 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1563464528965843 / 4000000000000) 3 (IntervalRat.scale (677 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (34964299057 / 1000000000000) (34964364971 / 1000000000000), orderedInterval (-20200054495 / 1000000000000) (-20199988581 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2679023118782239 / 4000000000000) 3 (IntervalRat.scale (677 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-30281339080 / 1000000000000) (-30281338943 / 1000000000000), orderedInterval (-5770967863 / 1000000000000) (-5770967727 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1973356303902301 / 4000000000000) 3 (IntervalRat.scale (677 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-28008535337 / 1000000000000) (-28008535336 / 1000000000000), orderedInterval (-22464996103 / 1000000000000) (-22464996102 / 1000000000000)))) (orderedInterval (308542836 / 1000000000000) (308542976 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate467_chunkChecks3_1 :
    compactCertificate467.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3027636041534323 / 4000000000000) 3 (IntervalRat.scale (677 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-15660160769 / 1000000000000) (-15660160768 / 1000000000000), orderedInterval (-24399443785 / 1000000000000) (-24399443784 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1748006483587867 / 4000000000000) 3 (IntervalRat.scale (677 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-34107731353 / 1000000000000) (-34107731351 / 1000000000000), orderedInterval (-17091430871 / 1000000000000) (-17091430870 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3101868179710103 / 4000000000000) 3 (IntervalRat.scale (677 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-7887811771 / 1000000000000) (-7887811770 / 1000000000000), orderedInterval (-27540017198 / 1000000000000) (-27540017197 / 1000000000000)))) (orderedInterval (1333642664 / 1000000000000) (1333643974 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2898167617242707 / 4000000000000) 3 (IntervalRat.scale (677 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (11016119856 / 1000000000000) (11016119875 / 1000000000000), orderedInterval (-27526625981 / 1000000000000) (-27526625963 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2068269163656131 / 4000000000000) 3 (IntervalRat.scale (677 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (17139897795 / 1000000000000) (17139898285 / 1000000000000), orderedInterval (-30634164296 / 1000000000000) (-30634163807 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2345196793447749 / 4000000000000) 3 (IntervalRat.scale (677 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (12632783346 / 1000000000000) (12632783409 / 1000000000000), orderedInterval (-30444973322 / 1000000000000) (-30444973259 / 1000000000000)))) (orderedInterval (4659082873 / 1000000000000) (4659083227 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1955180587320181 / 4000000000000) 3 (IntervalRat.scale (677 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-17560060716 / 1000000000000) (-17560060147 / 1000000000000), orderedInterval (31546856610 / 1000000000000) (31546857179 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1727461343575801 / 4000000000000) 3 (IntervalRat.scale (677 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-29819158875 / 1000000000000) (-29819116930 / 1000000000000), orderedInterval (24219935159 / 1000000000000) (24219977103 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (500685628408299 / 800000000000) 3 (IntervalRat.scale (677 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-31716189544 / 1000000000000) (-31716189234 / 1000000000000), orderedInterval (-3333204909 / 1000000000000) (-3333204599 / 1000000000000)))) (orderedInterval (2319600099 / 1000000000000) (2319605273 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate467_chunkChecks3_2 :
    compactCertificate467.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1384922797818353 / 4000000000000) 3 (IntervalRat.scale (677 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (42516996294 / 1000000000000) (42516996323 / 1000000000000), orderedInterval (5508046086 / 1000000000000) (5508046116 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1174014393310633 / 4000000000000) 3 (IntervalRat.scale (677 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-39712877954 / 1000000000000) (-39712823770 / 1000000000000), orderedInterval (24397105794 / 1000000000000) (24397159978 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (734643696097699 / 4000000000000) 3 (IntervalRat.scale (677 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (46421390340 / 1000000000000) (46421479038 / 1000000000000), orderedInterval (-36338639219 / 1000000000000) (-36338550521 / 1000000000000)))) (orderedInterval (2016786409 / 1000000000000) (2016788957 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (395093823075933 / 4000000000000) 3 (IntervalRat.scale (677 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-66376190578 / 1000000000000) (-66376155924 / 1000000000000), orderedInterval (45495965991 / 1000000000000) (45496000645 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1072756586346799 / 4000000000000) 3 (IntervalRat.scale (677 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-45461006792 / 1000000000000) (-45460998068 / 1000000000000), orderedInterval (17608042587 / 1000000000000) (17608051311 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1464757405875023 / 4000000000000) 3 (IntervalRat.scale (677 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (23264532752 / 1000000000000) (23264535857 / 1000000000000), orderedInterval (-34633225511 / 1000000000000) (-34633222406 / 1000000000000)))) (orderedInterval (-3144699853 / 1000000000000) (-3144699398 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (619356303902301 / 4000000000000) 3 (IntervalRat.scale (677 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-63698472232 / 1000000000000) (-63698471987 / 1000000000000), orderedInterval (7552577210 / 1000000000000) (7552577455 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2517648989729021 / 4000000000000) 3 (IntervalRat.scale (677 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (30305536821 / 1000000000000) (30305565371 / 1000000000000), orderedInterval (-9669008840 / 1000000000000) (-9668980290 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1681672847053939 / 4000000000000) 3 (IntervalRat.scale (677 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (8867478257 / 1000000000000) (8867478258 / 1000000000000), orderedInterval (37879061349 / 1000000000000) (37879061350 / 1000000000000)))) (orderedInterval (8518947553 / 1000000000000) (8518962817 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate467_chunkChecks3 :
    compactCertificate467.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate467.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate467_chunkChecks3_0
    compactCertificate467_chunkChecks3_1 compactCertificate467_chunkChecks3_2

theorem compactCertificate467_chunkChecks4_0 :
    compactCertificate467.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (677 / 2) 4 (IntervalRat.scale (677 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-302600183 / 1000000000000) (-302600181 / 1000000000000), orderedInterval (43366549199 / 1000000000000) (43366549200 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (997350271728977 / 4000000000000) 4 (IntervalRat.scale (677 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-47185566842 / 1000000000000) (-47185559083 / 1000000000000), orderedInterval (18171213059 / 1000000000000) (18171220818 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (322522586022641 / 800000000000) 4 (IntervalRat.scale (677 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (38564046007 / 1000000000000) (38564050909 / 1000000000000), orderedInterval (-9635026756 / 1000000000000) (-9635021853 / 1000000000000)))) (orderedInterval (4400171808 / 1000000000000) (4400172454 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (291024321863539 / 4000000000000) 4 (IntervalRat.scale (677 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-89696904531 / 1000000000000) (-89696904529 / 1000000000000), orderedInterval (-25923161107 / 1000000000000) (-25923161106 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (781732264482583 / 4000000000000) 4 (IntervalRat.scale (677 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (56579885540 / 1000000000000) (56579885549 / 1000000000000), orderedInterval (7351154972 / 1000000000000) (7351154981 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2122555166652411 / 4000000000000) 4 (IntervalRat.scale (677 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-16447454701 / 1000000000000) (-16447454700 / 1000000000000), orderedInterval (-30467364965 / 1000000000000) (-30467364964 / 1000000000000)))) (orderedInterval (7342140334 / 1000000000000) (7342140482 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1563464528965843 / 4000000000000) 4 (IntervalRat.scale (677 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (34964299057 / 1000000000000) (34964364971 / 1000000000000), orderedInterval (-20200054495 / 1000000000000) (-20199988581 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2679023118782239 / 4000000000000) 4 (IntervalRat.scale (677 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-30281339080 / 1000000000000) (-30281338943 / 1000000000000), orderedInterval (-5770967863 / 1000000000000) (-5770967727 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1973356303902301 / 4000000000000) 4 (IntervalRat.scale (677 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-28008535337 / 1000000000000) (-28008535336 / 1000000000000), orderedInterval (-22464996103 / 1000000000000) (-22464996102 / 1000000000000)))) (orderedInterval (11258613670 / 1000000000000) (11258613933 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate467_chunkChecks4_1 :
    compactCertificate467.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3027636041534323 / 4000000000000) 4 (IntervalRat.scale (677 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-15660160769 / 1000000000000) (-15660160768 / 1000000000000), orderedInterval (-24399443785 / 1000000000000) (-24399443784 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1748006483587867 / 4000000000000) 4 (IntervalRat.scale (677 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-34107731353 / 1000000000000) (-34107731351 / 1000000000000), orderedInterval (-17091430871 / 1000000000000) (-17091430870 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3101868179710103 / 4000000000000) 4 (IntervalRat.scale (677 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-7887811771 / 1000000000000) (-7887811770 / 1000000000000), orderedInterval (-27540017198 / 1000000000000) (-27540017197 / 1000000000000)))) (orderedInterval (31653428394 / 1000000000000) (31653431303 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2898167617242707 / 4000000000000) 4 (IntervalRat.scale (677 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (11016119856 / 1000000000000) (11016119875 / 1000000000000), orderedInterval (-27526625981 / 1000000000000) (-27526625963 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2068269163656131 / 4000000000000) 4 (IntervalRat.scale (677 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (17139897795 / 1000000000000) (17139898285 / 1000000000000), orderedInterval (-30634164296 / 1000000000000) (-30634163807 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2345196793447749 / 4000000000000) 4 (IntervalRat.scale (677 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (12632783346 / 1000000000000) (12632783409 / 1000000000000), orderedInterval (-30444973322 / 1000000000000) (-30444973259 / 1000000000000)))) (orderedInterval (4046978511 / 1000000000000) (4046979093 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1955180587320181 / 4000000000000) 4 (IntervalRat.scale (677 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-17560060716 / 1000000000000) (-17560060147 / 1000000000000), orderedInterval (31546856610 / 1000000000000) (31546857179 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1727461343575801 / 4000000000000) 4 (IntervalRat.scale (677 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-29819158875 / 1000000000000) (-29819116930 / 1000000000000), orderedInterval (24219935159 / 1000000000000) (24219977103 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (500685628408299 / 800000000000) 4 (IntervalRat.scale (677 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-31716189544 / 1000000000000) (-31716189234 / 1000000000000), orderedInterval (-3333204909 / 1000000000000) (-3333204599 / 1000000000000)))) (orderedInterval (-5863892972 / 1000000000000) (-5863886290 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate467_chunkChecks4_2 :
    compactCertificate467.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1384922797818353 / 4000000000000) 4 (IntervalRat.scale (677 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (42516996294 / 1000000000000) (42516996323 / 1000000000000), orderedInterval (5508046086 / 1000000000000) (5508046116 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1174014393310633 / 4000000000000) 4 (IntervalRat.scale (677 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-39712877954 / 1000000000000) (-39712823770 / 1000000000000), orderedInterval (24397105794 / 1000000000000) (24397159978 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (734643696097699 / 4000000000000) 4 (IntervalRat.scale (677 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (46421390340 / 1000000000000) (46421479038 / 1000000000000), orderedInterval (-36338639219 / 1000000000000) (-36338550521 / 1000000000000)))) (orderedInterval (-6051202130 / 1000000000000) (-6051200055 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (395093823075933 / 4000000000000) 4 (IntervalRat.scale (677 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-66376190578 / 1000000000000) (-66376155924 / 1000000000000), orderedInterval (45495965991 / 1000000000000) (45496000645 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1072756586346799 / 4000000000000) 4 (IntervalRat.scale (677 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-45461006792 / 1000000000000) (-45460998068 / 1000000000000), orderedInterval (17608042587 / 1000000000000) (17608051311 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1464757405875023 / 4000000000000) 4 (IntervalRat.scale (677 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (23264532752 / 1000000000000) (23264535857 / 1000000000000), orderedInterval (-34633225511 / 1000000000000) (-34633222406 / 1000000000000)))) (orderedInterval (-2008053315 / 1000000000000) (-2008052865 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (619356303902301 / 4000000000000) 4 (IntervalRat.scale (677 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-63698472232 / 1000000000000) (-63698471987 / 1000000000000), orderedInterval (7552577210 / 1000000000000) (7552577455 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2517648989729021 / 4000000000000) 4 (IntervalRat.scale (677 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (30305536821 / 1000000000000) (30305565371 / 1000000000000), orderedInterval (-9669008840 / 1000000000000) (-9668980290 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1681672847053939 / 4000000000000) 4 (IntervalRat.scale (677 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (8867478257 / 1000000000000) (8867478258 / 1000000000000), orderedInterval (37879061349 / 1000000000000) (37879061350 / 1000000000000)))) (orderedInterval (-33515205988 / 1000000000000) (-33515177636 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate467_chunkChecks4 :
    compactCertificate467.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate467.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate467_chunkChecks4_0
    compactCertificate467_chunkChecks4_1 compactCertificate467_chunkChecks4_2

theorem compactCertificate467_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate467.chunkCheck r b = true :=
  compactCertificate467.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate467_chunkChecks0
    · exact compactCertificate467_chunkChecks1
    · exact compactCertificate467_chunkChecks2
    · exact compactCertificate467_chunkChecks3
    · exact compactCertificate467_chunkChecks4)

theorem compactCertificate467_coefficient0 :
    compactCertificate467.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate467_coefficient1 :
    compactCertificate467.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate467_coefficient2 :
    compactCertificate467.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate467_coefficient3 :
    compactCertificate467.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate467_coefficient4 :
    compactCertificate467.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate467_coefficients : ∀ r : Fin 5,
    compactCertificate467.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate467_coefficient0
  · exact compactCertificate467_coefficient1
  · exact compactCertificate467_coefficient2
  · exact compactCertificate467_coefficient3
  · exact compactCertificate467_coefficient4

theorem compactCertificate467_lower : (1 : ℚ) ≤ compactCertificate467.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate467, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate467_proves {t : ℝ} (ht : t ∈ compactCertificate467.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate467.proves compactCertificate467_states compactCertificate467_chunks
    compactCertificate467_coefficients compactCertificate467_lower ht

end Erdos232
