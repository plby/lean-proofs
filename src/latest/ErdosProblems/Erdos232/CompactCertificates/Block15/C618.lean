/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate618 : CompactCertificate where
  left := 489
  right := 490
  center := 979 / 2
  grid := fun i =>
    match i.val with
    | 0 => 156
    | 1 => 115
    | 2 => 186
    | 3 => 34
    | 4 => 90
    | 5 => 244
    | 6 => 180
    | 7 => 308
    | 8 => 227
    | 9 => 349
    | 10 => 201
    | 11 => 357
    | 12 => 334
    | 13 => 238
    | 14 => 270
    | 15 => 225
    | 16 => 199
    | 17 => 288
    | 18 => 159
    | 19 => 135
    | 20 => 85
    | 21 => 45
    | 22 => 124
    | 23 => 169
    | 24 => 71
    | 25 => 290
    | _ => 194
  point := fun i =>
    match i.val with
    | 0 => 979 / 2
    | 1 => 1442253937995079 / 4000000000000
    | 2 => 466395290570407 / 800000000000
    | 3 => 420846102074453 / 4000000000000
    | 4 => 1130451827073041 / 4000000000000
    | 5 => 3069396614701197 / 4000000000000
    | 6 => 2260903654147061 / 4000000000000
    | 7 => 3874096947249353 / 4000000000000
    | 8 => 2853642276987227 / 4000000000000
    | 9 => 4378221099944021 / 4000000000000
    | 10 => 2527767130624109 / 4000000000000
    | 11 => 4485567131368081 / 4000000000000
    | 12 => 4190998666588789 / 4000000000000
    | 13 => 2990894403573637 / 4000000000000
    | 14 => 3391355481219123 / 4000000000000
    | 15 => 2827358633657987 / 4000000000000
    | 16 => 2498057098021727 / 4000000000000
    | 17 => 724034313458973 / 800000000000
    | 18 => 2002717014865831 / 4000000000000
    | 19 => 1697725392985391 / 4000000000000
    | 20 => 1062357723012773 / 4000000000000
    | 21 => 571339516678491 / 4000000000000
    | 22 => 1551297929148473 / 4000000000000
    | 23 => 2118164697712921 / 4000000000000
    | 24 => 895642276987227 / 4000000000000
    | 25 => 3640736131380667 / 4000000000000
    | _ => 2431843009255253 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (7047571325 / 1000000000000) (7047571326 / 1000000000000), orderedInterval (35360632455 / 1000000000000) (35360632456 / 1000000000000))
    | 1 => (orderedInterval (-2745300561 / 1000000000000) (-2745300560 / 1000000000000), orderedInterval (-41925772674 / 1000000000000) (-41925772673 / 1000000000000))
    | 2 => (orderedInterval (-17467284417 / 1000000000000) (-17467283841 / 1000000000000), orderedInterval (28066314622 / 1000000000000) (28066315198 / 1000000000000))
    | 3 => (orderedInterval (-56789337870 / 1000000000000) (-56789243354 / 1000000000000), orderedInterval (53428338584 / 1000000000000) (53428433100 / 1000000000000))
    | 4 => (orderedInterval (28895715553 / 1000000000000) (28895715554 / 1000000000000), orderedInterval (37600692428 / 1000000000000) (37600692429 / 1000000000000))
    | 5 => (orderedInterval (28800147988 / 1000000000000) (28800151042 / 1000000000000), orderedInterval (-450374104 / 1000000000000) (-450371049 / 1000000000000))
    | 6 => (orderedInterval (16803926648 / 1000000000000) (16803926649 / 1000000000000), orderedInterval (29035756150 / 1000000000000) (29035756151 / 1000000000000))
    | 7 => (orderedInterval (25427719964 / 1000000000000) (25427746479 / 1000000000000), orderedInterval (-3290236425 / 1000000000000) (-3290209910 / 1000000000000))
    | 8 => (orderedInterval (-25975102203 / 1000000000000) (-25975102201 / 1000000000000), orderedInterval (-14734928974 / 1000000000000) (-14734928972 / 1000000000000))
    | 9 => (orderedInterval (21216147205 / 1000000000000) (21216157404 / 1000000000000), orderedInterval (-11476997429 / 1000000000000) (-11476987231 / 1000000000000))
    | 10 => (orderedInterval (-30284838926 / 1000000000000) (-30284838907 / 1000000000000), orderedInterval (-9475029676 / 1000000000000) (-9475029657 / 1000000000000))
    | 11 => (orderedInterval (-14008248470 / 1000000000000) (-14008248469 / 1000000000000), orderedInterval (-19267415827 / 1000000000000) (-19267415826 / 1000000000000))
    | 12 => (orderedInterval (-16928029699 / 1000000000000) (-16928029330 / 1000000000000), orderedInterval (17925906449 / 1000000000000) (17925906818 / 1000000000000))
    | 13 => (orderedInterval (21129509895 / 1000000000000) (21129509896 / 1000000000000), orderedInterval (20109348756 / 1000000000000) (20109348757 / 1000000000000))
    | 14 => (orderedInterval (10521889125 / 1000000000000) (10521889126 / 1000000000000), orderedInterval (25295247001 / 1000000000000) (25295247002 / 1000000000000))
    | 15 => (orderedInterval (-20816841180 / 1000000000000) (-20816841179 / 1000000000000), orderedInterval (-21602760410 / 1000000000000) (-21602760409 / 1000000000000))
    | 16 => (orderedInterval (-3902470835 / 1000000000000) (-3902470834 / 1000000000000), orderedInterval (-31685278828 / 1000000000000) (-31685278827 / 1000000000000))
    | 17 => (orderedInterval (22998726576 / 1000000000000) (22998726582 / 1000000000000), orderedInterval (13196095968 / 1000000000000) (13196095973 / 1000000000000))
    | 18 => (orderedInterval (-33109631805 / 1000000000000) (-33109601358 / 1000000000000), orderedInterval (13271817487 / 1000000000000) (13271847934 / 1000000000000))
    | 19 => (orderedInterval (-34540887299 / 1000000000000) (-34540887297 / 1000000000000), orderedInterval (-17476794430 / 1000000000000) (-17476794429 / 1000000000000))
    | 20 => (orderedInterval (30057033308 / 1000000000000) (30057044117 / 1000000000000), orderedInterval (-38703487442 / 1000000000000) (-38703476633 / 1000000000000))
    | 21 => (orderedInterval (-52039783482 / 1000000000000) (-52039699203 / 1000000000000), orderedInterval (42001880319 / 1000000000000) (42001964598 / 1000000000000))
    | 22 => (orderedInterval (-32907224369 / 1000000000000) (-32907139633 / 1000000000000), orderedInterval (23677779543 / 1000000000000) (23677864279 / 1000000000000))
    | 23 => (orderedInterval (19658464303 / 1000000000000) (19658465687 / 1000000000000), orderedInterval (-28579989067 / 1000000000000) (-28579987684 / 1000000000000))
    | 24 => (orderedInterval (-53185114032 / 1000000000000) (-53185113813 / 1000000000000), orderedInterval (3929842420 / 1000000000000) (3929842639 / 1000000000000))
    | 25 => (orderedInterval (-2444852687 / 1000000000000) (-2444852686 / 1000000000000), orderedInterval (26335038500 / 1000000000000) (26335038501 / 1000000000000))
    | _ => (orderedInterval (-21410994457 / 1000000000000) (-21410991047 / 1000000000000), orderedInterval (24280933778 / 1000000000000) (24280937188 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (1742829504 / 1000000000000) (1742829573 / 1000000000000)
      | 1 => orderedInterval (-376236374 / 1000000000000) (-376235073 / 1000000000000)
      | 2 => orderedInterval (-1412060423 / 1000000000000) (-1412059577 / 1000000000000)
      | 3 => orderedInterval (-8005067511 / 1000000000000) (-8005065503 / 1000000000000)
      | 4 => orderedInterval (2250423333 / 1000000000000) (2250423399 / 1000000000000)
      | 5 => orderedInterval (571797647 / 1000000000000) (571797695 / 1000000000000)
      | 6 => orderedInterval (8227502519 / 1000000000000) (8227507862 / 1000000000000)
      | 7 => orderedInterval (200876245 / 1000000000000) (200879888 / 1000000000000)
      | _ => orderedInterval (3895667863 / 1000000000000) (3895668640 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (15689485405 / 1000000000000) (15689485484 / 1000000000000)
      | 1 => orderedInterval (718224696 / 1000000000000) (718225323 / 1000000000000)
      | 2 => orderedInterval (-318215818 / 1000000000000) (-318214152 / 1000000000000)
      | 3 => orderedInterval (-2620944212 / 1000000000000) (-2620939756 / 1000000000000)
      | 4 => orderedInterval (1990333474 / 1000000000000) (1990333583 / 1000000000000)
      | 5 => orderedInterval (2577846284 / 1000000000000) (2577846352 / 1000000000000)
      | 6 => orderedInterval (-1996480961 / 1000000000000) (-1996475677 / 1000000000000)
      | 7 => orderedInterval (1717600268 / 1000000000000) (1717602413 / 1000000000000)
      | _ => orderedInterval (-9633483541 / 1000000000000) (-9633482555 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-1357641878 / 1000000000000) (-1357641785 / 1000000000000)
      | 1 => orderedInterval (4649708489 / 1000000000000) (4649709164 / 1000000000000)
      | 2 => orderedInterval (4404477223 / 1000000000000) (4404480513 / 1000000000000)
      | 3 => orderedInterval (33045386924 / 1000000000000) (33045396858 / 1000000000000)
      | 4 => orderedInterval (-5906609370 / 1000000000000) (-5906609182 / 1000000000000)
      | 5 => orderedInterval (-1880537057 / 1000000000000) (-1880536955 / 1000000000000)
      | 6 => orderedInterval (-7292334959 / 1000000000000) (-7292329643 / 1000000000000)
      | 7 => orderedInterval (1209206232 / 1000000000000) (1209207752 / 1000000000000)
      | _ => orderedInterval (-6798247762 / 1000000000000) (-6798246492 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-16639137496 / 1000000000000) (-16639137387 / 1000000000000)
      | 1 => orderedInterval (-391287620 / 1000000000000) (-391286633 / 1000000000000)
      | 2 => orderedInterval (307339434 / 1000000000000) (307345931 / 1000000000000)
      | 3 => orderedInterval (11573461483 / 1000000000000) (11573483654 / 1000000000000)
      | 4 => orderedInterval (-2926933653 / 1000000000000) (-2926933322 / 1000000000000)
      | 5 => orderedInterval (-5146061594 / 1000000000000) (-5146061437 / 1000000000000)
      | 6 => orderedInterval (1842118987 / 1000000000000) (1842124369 / 1000000000000)
      | 7 => orderedInterval (-2489054369 / 1000000000000) (-2489053183 / 1000000000000)
      | _ => orderedInterval (22521378821 / 1000000000000) (22521380483 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (791472903 / 1000000000000) (791473032 / 1000000000000)
      | 1 => orderedInterval (-12243937352 / 1000000000000) (-12243935822 / 1000000000000)
      | 2 => orderedInterval (-14853727179 / 1000000000000) (-14853714333 / 1000000000000)
      | 3 => orderedInterval (-155375296707 / 1000000000000) (-155375247118 / 1000000000000)
      | 4 => orderedInterval (16825789914 / 1000000000000) (16825790516 / 1000000000000)
      | 5 => orderedInterval (6448950340 / 1000000000000) (6448950588 / 1000000000000)
      | 6 => orderedInterval (6976673408 / 1000000000000) (6976678893 / 1000000000000)
      | 7 => orderedInterval (-1752107593 / 1000000000000) (-1752106618 / 1000000000000)
      | _ => orderedInterval (11832125376 / 1000000000000) (11832127600 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (7095732803 / 1000000000000) (7095746904 / 1000000000000)
    | 1 => orderedInterval (8124365595 / 1000000000000) (8124381015 / 1000000000000)
    | 2 => orderedInterval (20073407842 / 1000000000000) (20073430230 / 1000000000000)
    | 3 => orderedInterval (8651823993 / 1000000000000) (8651862475 / 1000000000000)
    | _ => orderedInterval (-141350056890 / 1000000000000) (-141349983262 / 1000000000000)

theorem compactCertificate618_stateChecks0 :
    compactCertificate618.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 156 12 (979 / 2)) (orderedInterval (7047571325 / 1000000000000) (7047571326 / 1000000000000), orderedInterval (35360632455 / 1000000000000) (35360632456 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 115 12 (1442253937995079 / 4000000000000)) (orderedInterval (-2745300561 / 1000000000000) (-2745300560 / 1000000000000), orderedInterval (-41925772674 / 1000000000000) (-41925772673 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 186 12 (466395290570407 / 800000000000)) (orderedInterval (-17467284417 / 1000000000000) (-17467283841 / 1000000000000), orderedInterval (28066314622 / 1000000000000) (28066315198 / 1000000000000))) = true
  rfl'

theorem compactCertificate618_stateChecks1 :
    compactCertificate618.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (420846102074453 / 4000000000000)) (orderedInterval (-56789337870 / 1000000000000) (-56789243354 / 1000000000000), orderedInterval (53428338584 / 1000000000000) (53428433100 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 90 12 (1130451827073041 / 4000000000000)) (orderedInterval (28895715553 / 1000000000000) (28895715554 / 1000000000000), orderedInterval (37600692428 / 1000000000000) (37600692429 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 244 12 (3069396614701197 / 4000000000000)) (orderedInterval (28800147988 / 1000000000000) (28800151042 / 1000000000000), orderedInterval (-450374104 / 1000000000000) (-450371049 / 1000000000000))) = true
  rfl'

theorem compactCertificate618_stateChecks2 :
    compactCertificate618.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 180 12 (2260903654147061 / 4000000000000)) (orderedInterval (16803926648 / 1000000000000) (16803926649 / 1000000000000), orderedInterval (29035756150 / 1000000000000) (29035756151 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 308 12 (3874096947249353 / 4000000000000)) (orderedInterval (25427719964 / 1000000000000) (25427746479 / 1000000000000), orderedInterval (-3290236425 / 1000000000000) (-3290209910 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 227 12 (2853642276987227 / 4000000000000)) (orderedInterval (-25975102203 / 1000000000000) (-25975102201 / 1000000000000), orderedInterval (-14734928974 / 1000000000000) (-14734928972 / 1000000000000))) = true
  rfl'

theorem compactCertificate618_stateChecks3 :
    compactCertificate618.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 349 12 (4378221099944021 / 4000000000000)) (orderedInterval (21216147205 / 1000000000000) (21216157404 / 1000000000000), orderedInterval (-11476997429 / 1000000000000) (-11476987231 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 201 12 (2527767130624109 / 4000000000000)) (orderedInterval (-30284838926 / 1000000000000) (-30284838907 / 1000000000000), orderedInterval (-9475029676 / 1000000000000) (-9475029657 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 357 12 (4485567131368081 / 4000000000000)) (orderedInterval (-14008248470 / 1000000000000) (-14008248469 / 1000000000000), orderedInterval (-19267415827 / 1000000000000) (-19267415826 / 1000000000000))) = true
  rfl'

theorem compactCertificate618_stateChecks4 :
    compactCertificate618.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 334 12 (4190998666588789 / 4000000000000)) (orderedInterval (-16928029699 / 1000000000000) (-16928029330 / 1000000000000), orderedInterval (17925906449 / 1000000000000) (17925906818 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 238 12 (2990894403573637 / 4000000000000)) (orderedInterval (21129509895 / 1000000000000) (21129509896 / 1000000000000), orderedInterval (20109348756 / 1000000000000) (20109348757 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 270 12 (3391355481219123 / 4000000000000)) (orderedInterval (10521889125 / 1000000000000) (10521889126 / 1000000000000), orderedInterval (25295247001 / 1000000000000) (25295247002 / 1000000000000))) = true
  rfl'

theorem compactCertificate618_stateChecks5 :
    compactCertificate618.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 225 12 (2827358633657987 / 4000000000000)) (orderedInterval (-20816841180 / 1000000000000) (-20816841179 / 1000000000000), orderedInterval (-21602760410 / 1000000000000) (-21602760409 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 199 12 (2498057098021727 / 4000000000000)) (orderedInterval (-3902470835 / 1000000000000) (-3902470834 / 1000000000000), orderedInterval (-31685278828 / 1000000000000) (-31685278827 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 288 12 (724034313458973 / 800000000000)) (orderedInterval (22998726576 / 1000000000000) (22998726582 / 1000000000000), orderedInterval (13196095968 / 1000000000000) (13196095973 / 1000000000000))) = true
  rfl'

theorem compactCertificate618_stateChecks6 :
    compactCertificate618.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 159 12 (2002717014865831 / 4000000000000)) (orderedInterval (-33109631805 / 1000000000000) (-33109601358 / 1000000000000), orderedInterval (13271817487 / 1000000000000) (13271847934 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 135 12 (1697725392985391 / 4000000000000)) (orderedInterval (-34540887299 / 1000000000000) (-34540887297 / 1000000000000), orderedInterval (-17476794430 / 1000000000000) (-17476794429 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 85 12 (1062357723012773 / 4000000000000)) (orderedInterval (30057033308 / 1000000000000) (30057044117 / 1000000000000), orderedInterval (-38703487442 / 1000000000000) (-38703476633 / 1000000000000))) = true
  rfl'

theorem compactCertificate618_stateChecks7 :
    compactCertificate618.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (571339516678491 / 4000000000000)) (orderedInterval (-52039783482 / 1000000000000) (-52039699203 / 1000000000000), orderedInterval (42001880319 / 1000000000000) (42001964598 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 124 12 (1551297929148473 / 4000000000000)) (orderedInterval (-32907224369 / 1000000000000) (-32907139633 / 1000000000000), orderedInterval (23677779543 / 1000000000000) (23677864279 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 169 12 (2118164697712921 / 4000000000000)) (orderedInterval (19658464303 / 1000000000000) (19658465687 / 1000000000000), orderedInterval (-28579989067 / 1000000000000) (-28579987684 / 1000000000000))) = true
  rfl'

theorem compactCertificate618_stateChecks8 :
    compactCertificate618.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 71 12 (895642276987227 / 4000000000000)) (orderedInterval (-53185114032 / 1000000000000) (-53185113813 / 1000000000000), orderedInterval (3929842420 / 1000000000000) (3929842639 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 290 12 (3640736131380667 / 4000000000000)) (orderedInterval (-2444852687 / 1000000000000) (-2444852686 / 1000000000000), orderedInterval (26335038500 / 1000000000000) (26335038501 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 194 12 (2431843009255253 / 4000000000000)) (orderedInterval (-21410994457 / 1000000000000) (-21410991047 / 1000000000000), orderedInterval (24280933778 / 1000000000000) (24280937188 / 1000000000000))) = true
  rfl'

theorem compactCertificate618_states : ∀ j,
    BesselStateValid (compactCertificate618.point j) (compactCertificate618.state j) :=
  compactCertificate618.statesValid_of_checks3 compactCertificate618_stateChecks0
    compactCertificate618_stateChecks1 compactCertificate618_stateChecks2
    compactCertificate618_stateChecks3 compactCertificate618_stateChecks4
    compactCertificate618_stateChecks5 compactCertificate618_stateChecks6
    compactCertificate618_stateChecks7 compactCertificate618_stateChecks8

theorem compactCertificate618_chunkChecks0_0 :
    compactCertificate618.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (979 / 2) 0 (IntervalRat.scale (979 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (7047571325 / 1000000000000) (7047571326 / 1000000000000), orderedInterval (35360632455 / 1000000000000) (35360632456 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1442253937995079 / 4000000000000) 0 (IntervalRat.scale (979 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-2745300561 / 1000000000000) (-2745300560 / 1000000000000), orderedInterval (-41925772674 / 1000000000000) (-41925772673 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (466395290570407 / 800000000000) 0 (IntervalRat.scale (979 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-17467284417 / 1000000000000) (-17467283841 / 1000000000000), orderedInterval (28066314622 / 1000000000000) (28066315198 / 1000000000000)))) (orderedInterval (1742829504 / 1000000000000) (1742829573 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (420846102074453 / 4000000000000) 0 (IntervalRat.scale (979 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-56789337870 / 1000000000000) (-56789243354 / 1000000000000), orderedInterval (53428338584 / 1000000000000) (53428433100 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (1130451827073041 / 4000000000000) 0 (IntervalRat.scale (979 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (28895715553 / 1000000000000) (28895715554 / 1000000000000), orderedInterval (37600692428 / 1000000000000) (37600692429 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (3069396614701197 / 4000000000000) 0 (IntervalRat.scale (979 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (28800147988 / 1000000000000) (28800151042 / 1000000000000), orderedInterval (-450374104 / 1000000000000) (-450371049 / 1000000000000)))) (orderedInterval (-376236374 / 1000000000000) (-376235073 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (2260903654147061 / 4000000000000) 0 (IntervalRat.scale (979 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (16803926648 / 1000000000000) (16803926649 / 1000000000000), orderedInterval (29035756150 / 1000000000000) (29035756151 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3874096947249353 / 4000000000000) 0 (IntervalRat.scale (979 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (25427719964 / 1000000000000) (25427746479 / 1000000000000), orderedInterval (-3290236425 / 1000000000000) (-3290209910 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2853642276987227 / 4000000000000) 0 (IntervalRat.scale (979 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-25975102203 / 1000000000000) (-25975102201 / 1000000000000), orderedInterval (-14734928974 / 1000000000000) (-14734928972 / 1000000000000)))) (orderedInterval (-1412060423 / 1000000000000) (-1412059577 / 1000000000000))) = true
  rfl'

theorem compactCertificate618_chunkChecks0_1 :
    compactCertificate618.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (4378221099944021 / 4000000000000) 0 (IntervalRat.scale (979 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (21216147205 / 1000000000000) (21216157404 / 1000000000000), orderedInterval (-11476997429 / 1000000000000) (-11476987231 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2527767130624109 / 4000000000000) 0 (IntervalRat.scale (979 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-30284838926 / 1000000000000) (-30284838907 / 1000000000000), orderedInterval (-9475029676 / 1000000000000) (-9475029657 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (4485567131368081 / 4000000000000) 0 (IntervalRat.scale (979 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-14008248470 / 1000000000000) (-14008248469 / 1000000000000), orderedInterval (-19267415827 / 1000000000000) (-19267415826 / 1000000000000)))) (orderedInterval (-8005067511 / 1000000000000) (-8005065503 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (4190998666588789 / 4000000000000) 0 (IntervalRat.scale (979 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-16928029699 / 1000000000000) (-16928029330 / 1000000000000), orderedInterval (17925906449 / 1000000000000) (17925906818 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2990894403573637 / 4000000000000) 0 (IntervalRat.scale (979 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (21129509895 / 1000000000000) (21129509896 / 1000000000000), orderedInterval (20109348756 / 1000000000000) (20109348757 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (3391355481219123 / 4000000000000) 0 (IntervalRat.scale (979 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (10521889125 / 1000000000000) (10521889126 / 1000000000000), orderedInterval (25295247001 / 1000000000000) (25295247002 / 1000000000000)))) (orderedInterval (2250423333 / 1000000000000) (2250423399 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2827358633657987 / 4000000000000) 0 (IntervalRat.scale (979 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-20816841180 / 1000000000000) (-20816841179 / 1000000000000), orderedInterval (-21602760410 / 1000000000000) (-21602760409 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2498057098021727 / 4000000000000) 0 (IntervalRat.scale (979 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-3902470835 / 1000000000000) (-3902470834 / 1000000000000), orderedInterval (-31685278828 / 1000000000000) (-31685278827 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (724034313458973 / 800000000000) 0 (IntervalRat.scale (979 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (22998726576 / 1000000000000) (22998726582 / 1000000000000), orderedInterval (13196095968 / 1000000000000) (13196095973 / 1000000000000)))) (orderedInterval (571797647 / 1000000000000) (571797695 / 1000000000000))) = true
  rfl'

theorem compactCertificate618_chunkChecks0_2 :
    compactCertificate618.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (2002717014865831 / 4000000000000) 0 (IntervalRat.scale (979 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-33109631805 / 1000000000000) (-33109601358 / 1000000000000), orderedInterval (13271817487 / 1000000000000) (13271847934 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1697725392985391 / 4000000000000) 0 (IntervalRat.scale (979 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-34540887299 / 1000000000000) (-34540887297 / 1000000000000), orderedInterval (-17476794430 / 1000000000000) (-17476794429 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (1062357723012773 / 4000000000000) 0 (IntervalRat.scale (979 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (30057033308 / 1000000000000) (30057044117 / 1000000000000), orderedInterval (-38703487442 / 1000000000000) (-38703476633 / 1000000000000)))) (orderedInterval (8227502519 / 1000000000000) (8227507862 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (571339516678491 / 4000000000000) 0 (IntervalRat.scale (979 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-52039783482 / 1000000000000) (-52039699203 / 1000000000000), orderedInterval (42001880319 / 1000000000000) (42001964598 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1551297929148473 / 4000000000000) 0 (IntervalRat.scale (979 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-32907224369 / 1000000000000) (-32907139633 / 1000000000000), orderedInterval (23677779543 / 1000000000000) (23677864279 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (2118164697712921 / 4000000000000) 0 (IntervalRat.scale (979 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (19658464303 / 1000000000000) (19658465687 / 1000000000000), orderedInterval (-28579989067 / 1000000000000) (-28579987684 / 1000000000000)))) (orderedInterval (200876245 / 1000000000000) (200879888 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (895642276987227 / 4000000000000) 0 (IntervalRat.scale (979 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-53185114032 / 1000000000000) (-53185113813 / 1000000000000), orderedInterval (3929842420 / 1000000000000) (3929842639 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3640736131380667 / 4000000000000) 0 (IntervalRat.scale (979 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-2444852687 / 1000000000000) (-2444852686 / 1000000000000), orderedInterval (26335038500 / 1000000000000) (26335038501 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2431843009255253 / 4000000000000) 0 (IntervalRat.scale (979 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-21410994457 / 1000000000000) (-21410991047 / 1000000000000), orderedInterval (24280933778 / 1000000000000) (24280937188 / 1000000000000)))) (orderedInterval (3895667863 / 1000000000000) (3895668640 / 1000000000000))) = true
  rfl'

theorem compactCertificate618_chunkChecks0 :
    compactCertificate618.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate618.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate618_chunkChecks0_0
    compactCertificate618_chunkChecks0_1 compactCertificate618_chunkChecks0_2

theorem compactCertificate618_chunkChecks1_0 :
    compactCertificate618.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (979 / 2) 1 (IntervalRat.scale (979 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (7047571325 / 1000000000000) (7047571326 / 1000000000000), orderedInterval (35360632455 / 1000000000000) (35360632456 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1442253937995079 / 4000000000000) 1 (IntervalRat.scale (979 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-2745300561 / 1000000000000) (-2745300560 / 1000000000000), orderedInterval (-41925772674 / 1000000000000) (-41925772673 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (466395290570407 / 800000000000) 1 (IntervalRat.scale (979 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-17467284417 / 1000000000000) (-17467283841 / 1000000000000), orderedInterval (28066314622 / 1000000000000) (28066315198 / 1000000000000)))) (orderedInterval (15689485405 / 1000000000000) (15689485484 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (420846102074453 / 4000000000000) 1 (IntervalRat.scale (979 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-56789337870 / 1000000000000) (-56789243354 / 1000000000000), orderedInterval (53428338584 / 1000000000000) (53428433100 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (1130451827073041 / 4000000000000) 1 (IntervalRat.scale (979 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (28895715553 / 1000000000000) (28895715554 / 1000000000000), orderedInterval (37600692428 / 1000000000000) (37600692429 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (3069396614701197 / 4000000000000) 1 (IntervalRat.scale (979 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (28800147988 / 1000000000000) (28800151042 / 1000000000000), orderedInterval (-450374104 / 1000000000000) (-450371049 / 1000000000000)))) (orderedInterval (718224696 / 1000000000000) (718225323 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (2260903654147061 / 4000000000000) 1 (IntervalRat.scale (979 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (16803926648 / 1000000000000) (16803926649 / 1000000000000), orderedInterval (29035756150 / 1000000000000) (29035756151 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3874096947249353 / 4000000000000) 1 (IntervalRat.scale (979 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (25427719964 / 1000000000000) (25427746479 / 1000000000000), orderedInterval (-3290236425 / 1000000000000) (-3290209910 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2853642276987227 / 4000000000000) 1 (IntervalRat.scale (979 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-25975102203 / 1000000000000) (-25975102201 / 1000000000000), orderedInterval (-14734928974 / 1000000000000) (-14734928972 / 1000000000000)))) (orderedInterval (-318215818 / 1000000000000) (-318214152 / 1000000000000))) = true
  rfl'

theorem compactCertificate618_chunkChecks1_1 :
    compactCertificate618.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (4378221099944021 / 4000000000000) 1 (IntervalRat.scale (979 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (21216147205 / 1000000000000) (21216157404 / 1000000000000), orderedInterval (-11476997429 / 1000000000000) (-11476987231 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2527767130624109 / 4000000000000) 1 (IntervalRat.scale (979 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-30284838926 / 1000000000000) (-30284838907 / 1000000000000), orderedInterval (-9475029676 / 1000000000000) (-9475029657 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (4485567131368081 / 4000000000000) 1 (IntervalRat.scale (979 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-14008248470 / 1000000000000) (-14008248469 / 1000000000000), orderedInterval (-19267415827 / 1000000000000) (-19267415826 / 1000000000000)))) (orderedInterval (-2620944212 / 1000000000000) (-2620939756 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (4190998666588789 / 4000000000000) 1 (IntervalRat.scale (979 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-16928029699 / 1000000000000) (-16928029330 / 1000000000000), orderedInterval (17925906449 / 1000000000000) (17925906818 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2990894403573637 / 4000000000000) 1 (IntervalRat.scale (979 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (21129509895 / 1000000000000) (21129509896 / 1000000000000), orderedInterval (20109348756 / 1000000000000) (20109348757 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (3391355481219123 / 4000000000000) 1 (IntervalRat.scale (979 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (10521889125 / 1000000000000) (10521889126 / 1000000000000), orderedInterval (25295247001 / 1000000000000) (25295247002 / 1000000000000)))) (orderedInterval (1990333474 / 1000000000000) (1990333583 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2827358633657987 / 4000000000000) 1 (IntervalRat.scale (979 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-20816841180 / 1000000000000) (-20816841179 / 1000000000000), orderedInterval (-21602760410 / 1000000000000) (-21602760409 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2498057098021727 / 4000000000000) 1 (IntervalRat.scale (979 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-3902470835 / 1000000000000) (-3902470834 / 1000000000000), orderedInterval (-31685278828 / 1000000000000) (-31685278827 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (724034313458973 / 800000000000) 1 (IntervalRat.scale (979 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (22998726576 / 1000000000000) (22998726582 / 1000000000000), orderedInterval (13196095968 / 1000000000000) (13196095973 / 1000000000000)))) (orderedInterval (2577846284 / 1000000000000) (2577846352 / 1000000000000))) = true
  rfl'

theorem compactCertificate618_chunkChecks1_2 :
    compactCertificate618.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (2002717014865831 / 4000000000000) 1 (IntervalRat.scale (979 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-33109631805 / 1000000000000) (-33109601358 / 1000000000000), orderedInterval (13271817487 / 1000000000000) (13271847934 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1697725392985391 / 4000000000000) 1 (IntervalRat.scale (979 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-34540887299 / 1000000000000) (-34540887297 / 1000000000000), orderedInterval (-17476794430 / 1000000000000) (-17476794429 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (1062357723012773 / 4000000000000) 1 (IntervalRat.scale (979 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (30057033308 / 1000000000000) (30057044117 / 1000000000000), orderedInterval (-38703487442 / 1000000000000) (-38703476633 / 1000000000000)))) (orderedInterval (-1996480961 / 1000000000000) (-1996475677 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (571339516678491 / 4000000000000) 1 (IntervalRat.scale (979 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-52039783482 / 1000000000000) (-52039699203 / 1000000000000), orderedInterval (42001880319 / 1000000000000) (42001964598 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1551297929148473 / 4000000000000) 1 (IntervalRat.scale (979 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-32907224369 / 1000000000000) (-32907139633 / 1000000000000), orderedInterval (23677779543 / 1000000000000) (23677864279 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (2118164697712921 / 4000000000000) 1 (IntervalRat.scale (979 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (19658464303 / 1000000000000) (19658465687 / 1000000000000), orderedInterval (-28579989067 / 1000000000000) (-28579987684 / 1000000000000)))) (orderedInterval (1717600268 / 1000000000000) (1717602413 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (895642276987227 / 4000000000000) 1 (IntervalRat.scale (979 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-53185114032 / 1000000000000) (-53185113813 / 1000000000000), orderedInterval (3929842420 / 1000000000000) (3929842639 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3640736131380667 / 4000000000000) 1 (IntervalRat.scale (979 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-2444852687 / 1000000000000) (-2444852686 / 1000000000000), orderedInterval (26335038500 / 1000000000000) (26335038501 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2431843009255253 / 4000000000000) 1 (IntervalRat.scale (979 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-21410994457 / 1000000000000) (-21410991047 / 1000000000000), orderedInterval (24280933778 / 1000000000000) (24280937188 / 1000000000000)))) (orderedInterval (-9633483541 / 1000000000000) (-9633482555 / 1000000000000))) = true
  rfl'

theorem compactCertificate618_chunkChecks1 :
    compactCertificate618.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate618.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate618_chunkChecks1_0
    compactCertificate618_chunkChecks1_1 compactCertificate618_chunkChecks1_2

theorem compactCertificate618_chunkChecks2_0 :
    compactCertificate618.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (979 / 2) 2 (IntervalRat.scale (979 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (7047571325 / 1000000000000) (7047571326 / 1000000000000), orderedInterval (35360632455 / 1000000000000) (35360632456 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1442253937995079 / 4000000000000) 2 (IntervalRat.scale (979 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-2745300561 / 1000000000000) (-2745300560 / 1000000000000), orderedInterval (-41925772674 / 1000000000000) (-41925772673 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (466395290570407 / 800000000000) 2 (IntervalRat.scale (979 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-17467284417 / 1000000000000) (-17467283841 / 1000000000000), orderedInterval (28066314622 / 1000000000000) (28066315198 / 1000000000000)))) (orderedInterval (-1357641878 / 1000000000000) (-1357641785 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (420846102074453 / 4000000000000) 2 (IntervalRat.scale (979 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-56789337870 / 1000000000000) (-56789243354 / 1000000000000), orderedInterval (53428338584 / 1000000000000) (53428433100 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (1130451827073041 / 4000000000000) 2 (IntervalRat.scale (979 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (28895715553 / 1000000000000) (28895715554 / 1000000000000), orderedInterval (37600692428 / 1000000000000) (37600692429 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (3069396614701197 / 4000000000000) 2 (IntervalRat.scale (979 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (28800147988 / 1000000000000) (28800151042 / 1000000000000), orderedInterval (-450374104 / 1000000000000) (-450371049 / 1000000000000)))) (orderedInterval (4649708489 / 1000000000000) (4649709164 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (2260903654147061 / 4000000000000) 2 (IntervalRat.scale (979 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (16803926648 / 1000000000000) (16803926649 / 1000000000000), orderedInterval (29035756150 / 1000000000000) (29035756151 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3874096947249353 / 4000000000000) 2 (IntervalRat.scale (979 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (25427719964 / 1000000000000) (25427746479 / 1000000000000), orderedInterval (-3290236425 / 1000000000000) (-3290209910 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2853642276987227 / 4000000000000) 2 (IntervalRat.scale (979 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-25975102203 / 1000000000000) (-25975102201 / 1000000000000), orderedInterval (-14734928974 / 1000000000000) (-14734928972 / 1000000000000)))) (orderedInterval (4404477223 / 1000000000000) (4404480513 / 1000000000000))) = true
  rfl'

theorem compactCertificate618_chunkChecks2_1 :
    compactCertificate618.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (4378221099944021 / 4000000000000) 2 (IntervalRat.scale (979 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (21216147205 / 1000000000000) (21216157404 / 1000000000000), orderedInterval (-11476997429 / 1000000000000) (-11476987231 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2527767130624109 / 4000000000000) 2 (IntervalRat.scale (979 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-30284838926 / 1000000000000) (-30284838907 / 1000000000000), orderedInterval (-9475029676 / 1000000000000) (-9475029657 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (4485567131368081 / 4000000000000) 2 (IntervalRat.scale (979 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-14008248470 / 1000000000000) (-14008248469 / 1000000000000), orderedInterval (-19267415827 / 1000000000000) (-19267415826 / 1000000000000)))) (orderedInterval (33045386924 / 1000000000000) (33045396858 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (4190998666588789 / 4000000000000) 2 (IntervalRat.scale (979 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-16928029699 / 1000000000000) (-16928029330 / 1000000000000), orderedInterval (17925906449 / 1000000000000) (17925906818 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2990894403573637 / 4000000000000) 2 (IntervalRat.scale (979 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (21129509895 / 1000000000000) (21129509896 / 1000000000000), orderedInterval (20109348756 / 1000000000000) (20109348757 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (3391355481219123 / 4000000000000) 2 (IntervalRat.scale (979 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (10521889125 / 1000000000000) (10521889126 / 1000000000000), orderedInterval (25295247001 / 1000000000000) (25295247002 / 1000000000000)))) (orderedInterval (-5906609370 / 1000000000000) (-5906609182 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2827358633657987 / 4000000000000) 2 (IntervalRat.scale (979 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-20816841180 / 1000000000000) (-20816841179 / 1000000000000), orderedInterval (-21602760410 / 1000000000000) (-21602760409 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2498057098021727 / 4000000000000) 2 (IntervalRat.scale (979 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-3902470835 / 1000000000000) (-3902470834 / 1000000000000), orderedInterval (-31685278828 / 1000000000000) (-31685278827 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (724034313458973 / 800000000000) 2 (IntervalRat.scale (979 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (22998726576 / 1000000000000) (22998726582 / 1000000000000), orderedInterval (13196095968 / 1000000000000) (13196095973 / 1000000000000)))) (orderedInterval (-1880537057 / 1000000000000) (-1880536955 / 1000000000000))) = true
  rfl'

theorem compactCertificate618_chunkChecks2_2 :
    compactCertificate618.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (2002717014865831 / 4000000000000) 2 (IntervalRat.scale (979 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-33109631805 / 1000000000000) (-33109601358 / 1000000000000), orderedInterval (13271817487 / 1000000000000) (13271847934 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1697725392985391 / 4000000000000) 2 (IntervalRat.scale (979 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-34540887299 / 1000000000000) (-34540887297 / 1000000000000), orderedInterval (-17476794430 / 1000000000000) (-17476794429 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (1062357723012773 / 4000000000000) 2 (IntervalRat.scale (979 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (30057033308 / 1000000000000) (30057044117 / 1000000000000), orderedInterval (-38703487442 / 1000000000000) (-38703476633 / 1000000000000)))) (orderedInterval (-7292334959 / 1000000000000) (-7292329643 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (571339516678491 / 4000000000000) 2 (IntervalRat.scale (979 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-52039783482 / 1000000000000) (-52039699203 / 1000000000000), orderedInterval (42001880319 / 1000000000000) (42001964598 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1551297929148473 / 4000000000000) 2 (IntervalRat.scale (979 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-32907224369 / 1000000000000) (-32907139633 / 1000000000000), orderedInterval (23677779543 / 1000000000000) (23677864279 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (2118164697712921 / 4000000000000) 2 (IntervalRat.scale (979 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (19658464303 / 1000000000000) (19658465687 / 1000000000000), orderedInterval (-28579989067 / 1000000000000) (-28579987684 / 1000000000000)))) (orderedInterval (1209206232 / 1000000000000) (1209207752 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (895642276987227 / 4000000000000) 2 (IntervalRat.scale (979 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-53185114032 / 1000000000000) (-53185113813 / 1000000000000), orderedInterval (3929842420 / 1000000000000) (3929842639 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3640736131380667 / 4000000000000) 2 (IntervalRat.scale (979 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-2444852687 / 1000000000000) (-2444852686 / 1000000000000), orderedInterval (26335038500 / 1000000000000) (26335038501 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2431843009255253 / 4000000000000) 2 (IntervalRat.scale (979 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-21410994457 / 1000000000000) (-21410991047 / 1000000000000), orderedInterval (24280933778 / 1000000000000) (24280937188 / 1000000000000)))) (orderedInterval (-6798247762 / 1000000000000) (-6798246492 / 1000000000000))) = true
  rfl'

theorem compactCertificate618_chunkChecks2 :
    compactCertificate618.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate618.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate618_chunkChecks2_0
    compactCertificate618_chunkChecks2_1 compactCertificate618_chunkChecks2_2

theorem compactCertificate618_chunkChecks3_0 :
    compactCertificate618.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (979 / 2) 3 (IntervalRat.scale (979 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (7047571325 / 1000000000000) (7047571326 / 1000000000000), orderedInterval (35360632455 / 1000000000000) (35360632456 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1442253937995079 / 4000000000000) 3 (IntervalRat.scale (979 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-2745300561 / 1000000000000) (-2745300560 / 1000000000000), orderedInterval (-41925772674 / 1000000000000) (-41925772673 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (466395290570407 / 800000000000) 3 (IntervalRat.scale (979 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-17467284417 / 1000000000000) (-17467283841 / 1000000000000), orderedInterval (28066314622 / 1000000000000) (28066315198 / 1000000000000)))) (orderedInterval (-16639137496 / 1000000000000) (-16639137387 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (420846102074453 / 4000000000000) 3 (IntervalRat.scale (979 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-56789337870 / 1000000000000) (-56789243354 / 1000000000000), orderedInterval (53428338584 / 1000000000000) (53428433100 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (1130451827073041 / 4000000000000) 3 (IntervalRat.scale (979 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (28895715553 / 1000000000000) (28895715554 / 1000000000000), orderedInterval (37600692428 / 1000000000000) (37600692429 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (3069396614701197 / 4000000000000) 3 (IntervalRat.scale (979 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (28800147988 / 1000000000000) (28800151042 / 1000000000000), orderedInterval (-450374104 / 1000000000000) (-450371049 / 1000000000000)))) (orderedInterval (-391287620 / 1000000000000) (-391286633 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (2260903654147061 / 4000000000000) 3 (IntervalRat.scale (979 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (16803926648 / 1000000000000) (16803926649 / 1000000000000), orderedInterval (29035756150 / 1000000000000) (29035756151 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3874096947249353 / 4000000000000) 3 (IntervalRat.scale (979 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (25427719964 / 1000000000000) (25427746479 / 1000000000000), orderedInterval (-3290236425 / 1000000000000) (-3290209910 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2853642276987227 / 4000000000000) 3 (IntervalRat.scale (979 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-25975102203 / 1000000000000) (-25975102201 / 1000000000000), orderedInterval (-14734928974 / 1000000000000) (-14734928972 / 1000000000000)))) (orderedInterval (307339434 / 1000000000000) (307345931 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate618_chunkChecks3_1 :
    compactCertificate618.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (4378221099944021 / 4000000000000) 3 (IntervalRat.scale (979 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (21216147205 / 1000000000000) (21216157404 / 1000000000000), orderedInterval (-11476997429 / 1000000000000) (-11476987231 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2527767130624109 / 4000000000000) 3 (IntervalRat.scale (979 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-30284838926 / 1000000000000) (-30284838907 / 1000000000000), orderedInterval (-9475029676 / 1000000000000) (-9475029657 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (4485567131368081 / 4000000000000) 3 (IntervalRat.scale (979 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-14008248470 / 1000000000000) (-14008248469 / 1000000000000), orderedInterval (-19267415827 / 1000000000000) (-19267415826 / 1000000000000)))) (orderedInterval (11573461483 / 1000000000000) (11573483654 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (4190998666588789 / 4000000000000) 3 (IntervalRat.scale (979 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-16928029699 / 1000000000000) (-16928029330 / 1000000000000), orderedInterval (17925906449 / 1000000000000) (17925906818 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2990894403573637 / 4000000000000) 3 (IntervalRat.scale (979 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (21129509895 / 1000000000000) (21129509896 / 1000000000000), orderedInterval (20109348756 / 1000000000000) (20109348757 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (3391355481219123 / 4000000000000) 3 (IntervalRat.scale (979 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (10521889125 / 1000000000000) (10521889126 / 1000000000000), orderedInterval (25295247001 / 1000000000000) (25295247002 / 1000000000000)))) (orderedInterval (-2926933653 / 1000000000000) (-2926933322 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2827358633657987 / 4000000000000) 3 (IntervalRat.scale (979 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-20816841180 / 1000000000000) (-20816841179 / 1000000000000), orderedInterval (-21602760410 / 1000000000000) (-21602760409 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2498057098021727 / 4000000000000) 3 (IntervalRat.scale (979 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-3902470835 / 1000000000000) (-3902470834 / 1000000000000), orderedInterval (-31685278828 / 1000000000000) (-31685278827 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (724034313458973 / 800000000000) 3 (IntervalRat.scale (979 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (22998726576 / 1000000000000) (22998726582 / 1000000000000), orderedInterval (13196095968 / 1000000000000) (13196095973 / 1000000000000)))) (orderedInterval (-5146061594 / 1000000000000) (-5146061437 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate618_chunkChecks3_2 :
    compactCertificate618.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (2002717014865831 / 4000000000000) 3 (IntervalRat.scale (979 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-33109631805 / 1000000000000) (-33109601358 / 1000000000000), orderedInterval (13271817487 / 1000000000000) (13271847934 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1697725392985391 / 4000000000000) 3 (IntervalRat.scale (979 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-34540887299 / 1000000000000) (-34540887297 / 1000000000000), orderedInterval (-17476794430 / 1000000000000) (-17476794429 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (1062357723012773 / 4000000000000) 3 (IntervalRat.scale (979 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (30057033308 / 1000000000000) (30057044117 / 1000000000000), orderedInterval (-38703487442 / 1000000000000) (-38703476633 / 1000000000000)))) (orderedInterval (1842118987 / 1000000000000) (1842124369 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (571339516678491 / 4000000000000) 3 (IntervalRat.scale (979 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-52039783482 / 1000000000000) (-52039699203 / 1000000000000), orderedInterval (42001880319 / 1000000000000) (42001964598 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1551297929148473 / 4000000000000) 3 (IntervalRat.scale (979 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-32907224369 / 1000000000000) (-32907139633 / 1000000000000), orderedInterval (23677779543 / 1000000000000) (23677864279 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (2118164697712921 / 4000000000000) 3 (IntervalRat.scale (979 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (19658464303 / 1000000000000) (19658465687 / 1000000000000), orderedInterval (-28579989067 / 1000000000000) (-28579987684 / 1000000000000)))) (orderedInterval (-2489054369 / 1000000000000) (-2489053183 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (895642276987227 / 4000000000000) 3 (IntervalRat.scale (979 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-53185114032 / 1000000000000) (-53185113813 / 1000000000000), orderedInterval (3929842420 / 1000000000000) (3929842639 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3640736131380667 / 4000000000000) 3 (IntervalRat.scale (979 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-2444852687 / 1000000000000) (-2444852686 / 1000000000000), orderedInterval (26335038500 / 1000000000000) (26335038501 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2431843009255253 / 4000000000000) 3 (IntervalRat.scale (979 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-21410994457 / 1000000000000) (-21410991047 / 1000000000000), orderedInterval (24280933778 / 1000000000000) (24280937188 / 1000000000000)))) (orderedInterval (22521378821 / 1000000000000) (22521380483 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate618_chunkChecks3 :
    compactCertificate618.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate618.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate618_chunkChecks3_0
    compactCertificate618_chunkChecks3_1 compactCertificate618_chunkChecks3_2

theorem compactCertificate618_chunkChecks4_0 :
    compactCertificate618.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (979 / 2) 4 (IntervalRat.scale (979 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (7047571325 / 1000000000000) (7047571326 / 1000000000000), orderedInterval (35360632455 / 1000000000000) (35360632456 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1442253937995079 / 4000000000000) 4 (IntervalRat.scale (979 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-2745300561 / 1000000000000) (-2745300560 / 1000000000000), orderedInterval (-41925772674 / 1000000000000) (-41925772673 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (466395290570407 / 800000000000) 4 (IntervalRat.scale (979 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-17467284417 / 1000000000000) (-17467283841 / 1000000000000), orderedInterval (28066314622 / 1000000000000) (28066315198 / 1000000000000)))) (orderedInterval (791472903 / 1000000000000) (791473032 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (420846102074453 / 4000000000000) 4 (IntervalRat.scale (979 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-56789337870 / 1000000000000) (-56789243354 / 1000000000000), orderedInterval (53428338584 / 1000000000000) (53428433100 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (1130451827073041 / 4000000000000) 4 (IntervalRat.scale (979 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (28895715553 / 1000000000000) (28895715554 / 1000000000000), orderedInterval (37600692428 / 1000000000000) (37600692429 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (3069396614701197 / 4000000000000) 4 (IntervalRat.scale (979 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (28800147988 / 1000000000000) (28800151042 / 1000000000000), orderedInterval (-450374104 / 1000000000000) (-450371049 / 1000000000000)))) (orderedInterval (-12243937352 / 1000000000000) (-12243935822 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (2260903654147061 / 4000000000000) 4 (IntervalRat.scale (979 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (16803926648 / 1000000000000) (16803926649 / 1000000000000), orderedInterval (29035756150 / 1000000000000) (29035756151 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3874096947249353 / 4000000000000) 4 (IntervalRat.scale (979 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (25427719964 / 1000000000000) (25427746479 / 1000000000000), orderedInterval (-3290236425 / 1000000000000) (-3290209910 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2853642276987227 / 4000000000000) 4 (IntervalRat.scale (979 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-25975102203 / 1000000000000) (-25975102201 / 1000000000000), orderedInterval (-14734928974 / 1000000000000) (-14734928972 / 1000000000000)))) (orderedInterval (-14853727179 / 1000000000000) (-14853714333 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate618_chunkChecks4_1 :
    compactCertificate618.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (4378221099944021 / 4000000000000) 4 (IntervalRat.scale (979 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (21216147205 / 1000000000000) (21216157404 / 1000000000000), orderedInterval (-11476997429 / 1000000000000) (-11476987231 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2527767130624109 / 4000000000000) 4 (IntervalRat.scale (979 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-30284838926 / 1000000000000) (-30284838907 / 1000000000000), orderedInterval (-9475029676 / 1000000000000) (-9475029657 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (4485567131368081 / 4000000000000) 4 (IntervalRat.scale (979 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-14008248470 / 1000000000000) (-14008248469 / 1000000000000), orderedInterval (-19267415827 / 1000000000000) (-19267415826 / 1000000000000)))) (orderedInterval (-155375296707 / 1000000000000) (-155375247118 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (4190998666588789 / 4000000000000) 4 (IntervalRat.scale (979 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-16928029699 / 1000000000000) (-16928029330 / 1000000000000), orderedInterval (17925906449 / 1000000000000) (17925906818 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2990894403573637 / 4000000000000) 4 (IntervalRat.scale (979 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (21129509895 / 1000000000000) (21129509896 / 1000000000000), orderedInterval (20109348756 / 1000000000000) (20109348757 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (3391355481219123 / 4000000000000) 4 (IntervalRat.scale (979 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (10521889125 / 1000000000000) (10521889126 / 1000000000000), orderedInterval (25295247001 / 1000000000000) (25295247002 / 1000000000000)))) (orderedInterval (16825789914 / 1000000000000) (16825790516 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2827358633657987 / 4000000000000) 4 (IntervalRat.scale (979 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-20816841180 / 1000000000000) (-20816841179 / 1000000000000), orderedInterval (-21602760410 / 1000000000000) (-21602760409 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2498057098021727 / 4000000000000) 4 (IntervalRat.scale (979 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-3902470835 / 1000000000000) (-3902470834 / 1000000000000), orderedInterval (-31685278828 / 1000000000000) (-31685278827 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (724034313458973 / 800000000000) 4 (IntervalRat.scale (979 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (22998726576 / 1000000000000) (22998726582 / 1000000000000), orderedInterval (13196095968 / 1000000000000) (13196095973 / 1000000000000)))) (orderedInterval (6448950340 / 1000000000000) (6448950588 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate618_chunkChecks4_2 :
    compactCertificate618.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (2002717014865831 / 4000000000000) 4 (IntervalRat.scale (979 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-33109631805 / 1000000000000) (-33109601358 / 1000000000000), orderedInterval (13271817487 / 1000000000000) (13271847934 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1697725392985391 / 4000000000000) 4 (IntervalRat.scale (979 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-34540887299 / 1000000000000) (-34540887297 / 1000000000000), orderedInterval (-17476794430 / 1000000000000) (-17476794429 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (1062357723012773 / 4000000000000) 4 (IntervalRat.scale (979 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (30057033308 / 1000000000000) (30057044117 / 1000000000000), orderedInterval (-38703487442 / 1000000000000) (-38703476633 / 1000000000000)))) (orderedInterval (6976673408 / 1000000000000) (6976678893 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (571339516678491 / 4000000000000) 4 (IntervalRat.scale (979 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-52039783482 / 1000000000000) (-52039699203 / 1000000000000), orderedInterval (42001880319 / 1000000000000) (42001964598 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1551297929148473 / 4000000000000) 4 (IntervalRat.scale (979 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-32907224369 / 1000000000000) (-32907139633 / 1000000000000), orderedInterval (23677779543 / 1000000000000) (23677864279 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (2118164697712921 / 4000000000000) 4 (IntervalRat.scale (979 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (19658464303 / 1000000000000) (19658465687 / 1000000000000), orderedInterval (-28579989067 / 1000000000000) (-28579987684 / 1000000000000)))) (orderedInterval (-1752107593 / 1000000000000) (-1752106618 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (895642276987227 / 4000000000000) 4 (IntervalRat.scale (979 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-53185114032 / 1000000000000) (-53185113813 / 1000000000000), orderedInterval (3929842420 / 1000000000000) (3929842639 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3640736131380667 / 4000000000000) 4 (IntervalRat.scale (979 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-2444852687 / 1000000000000) (-2444852686 / 1000000000000), orderedInterval (26335038500 / 1000000000000) (26335038501 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2431843009255253 / 4000000000000) 4 (IntervalRat.scale (979 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-21410994457 / 1000000000000) (-21410991047 / 1000000000000), orderedInterval (24280933778 / 1000000000000) (24280937188 / 1000000000000)))) (orderedInterval (11832125376 / 1000000000000) (11832127600 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate618_chunkChecks4 :
    compactCertificate618.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate618.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate618_chunkChecks4_0
    compactCertificate618_chunkChecks4_1 compactCertificate618_chunkChecks4_2

theorem compactCertificate618_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate618.chunkCheck r b = true :=
  compactCertificate618.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate618_chunkChecks0
    · exact compactCertificate618_chunkChecks1
    · exact compactCertificate618_chunkChecks2
    · exact compactCertificate618_chunkChecks3
    · exact compactCertificate618_chunkChecks4)

theorem compactCertificate618_coefficient0 :
    compactCertificate618.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate618_coefficient1 :
    compactCertificate618.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate618_coefficient2 :
    compactCertificate618.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate618_coefficient3 :
    compactCertificate618.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate618_coefficient4 :
    compactCertificate618.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate618_coefficients : ∀ r : Fin 5,
    compactCertificate618.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate618_coefficient0
  · exact compactCertificate618_coefficient1
  · exact compactCertificate618_coefficient2
  · exact compactCertificate618_coefficient3
  · exact compactCertificate618_coefficient4

theorem compactCertificate618_lower : (1 : ℚ) ≤ compactCertificate618.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate618, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate618_proves {t : ℝ} (ht : t ∈ compactCertificate618.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate618.proves compactCertificate618_states compactCertificate618_chunks
    compactCertificate618_coefficients compactCertificate618_lower ht

end Erdos232
