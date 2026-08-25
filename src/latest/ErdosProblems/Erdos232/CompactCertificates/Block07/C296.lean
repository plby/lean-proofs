/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate296 : CompactCertificate where
  left := 169
  right := 170
  center := 339 / 2
  grid := fun i =>
    match i.val with
    | 0 => 54
    | 1 => 40
    | 2 => 64
    | 3 => 12
    | 4 => 31
    | 5 => 85
    | 6 => 62
    | 7 => 107
    | 8 => 79
    | 9 => 121
    | 10 => 70
    | 11 => 124
    | 12 => 116
    | 13 => 82
    | 14 => 93
    | 15 => 78
    | 16 => 69
    | 17 => 100
    | 18 => 55
    | 19 => 47
    | 20 => 29
    | 21 => 16
    | 22 => 43
    | 23 => 58
    | 24 => 25
    | 25 => 100
    | _ => 67
  point := fun i =>
    match i.val with
    | 0 => 339 / 2
    | 1 => 499411731338439 / 4000000000000
    | 2 => 161499492853287 / 800000000000
    | 3 => 145727097653973 / 4000000000000
    | 4 => 391443482510481 / 4000000000000
    | 5 => 1062845201617677 / 4000000000000
    | 6 => 782886965021301 / 4000000000000
    | 7 => 1341490158444873 / 4000000000000
    | 8 => 988135579058907 / 4000000000000
    | 9 => 1516054088744661 / 4000000000000
    | 10 => 875294236242669 / 4000000000000
    | 11 => 1553224982159121 / 4000000000000
    | 12 => 1451224257378549 / 4000000000000
    | 13 => 1035662107059717 / 4000000000000
    | 14 => 1174330447531443 / 4000000000000
    | 15 => 979034297048067 / 4000000000000
    | 16 => 865006492573407 / 4000000000000
    | 17 => 250712596795293 / 800000000000
    | 18 => 693484237016871 / 4000000000000
    | 19 => 587874267846831 / 4000000000000
    | 20 => 367864420941093 / 4000000000000
    | 21 => 197838709043931 / 4000000000000
    | 22 => 537170580164793 / 4000000000000
    | 23 => 733460503089561 / 4000000000000
    | 24 => 310135579058907 / 4000000000000
    | 25 => 1260683910661947 / 4000000000000
    | _ => 842078427106773 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (36533099511 / 1000000000000) (36533099512 / 1000000000000), orderedInterval (49097987722 / 1000000000000) (49097987723 / 1000000000000))
    | 1 => (orderedInterval (-1883225382 / 1000000000000) (-1883225374 / 1000000000000), orderedInterval (71389973532 / 1000000000000) (71389973541 / 1000000000000))
    | 2 => (orderedInterval (56136745361 / 1000000000000) (56136745463 / 1000000000000), orderedInterval (-1622457884 / 1000000000000) (-1622457783 / 1000000000000))
    | 3 => (orderedInterval (-61668517248 / 1000000000000) (-61668511512 / 1000000000000), orderedInterval (117774475514 / 1000000000000) (117774481250 / 1000000000000))
    | 4 => (orderedInterval (-76682302770 / 1000000000000) (-76682302769 / 1000000000000), orderedInterval (-24610448859 / 1000000000000) (-24610448858 / 1000000000000))
    | 5 => (orderedInterval (25130107199 / 1000000000000) (25130110238 / 1000000000000), orderedInterval (-42051901574 / 1000000000000) (-42051898534 / 1000000000000))
    | 6 => (orderedInterval (56331066534 / 1000000000000) (56331067082 / 1000000000000), orderedInterval (-9058986112 / 1000000000000) (-9058985564 / 1000000000000))
    | 7 => (orderedInterval (-311563505 / 1000000000000) (-311563504 / 1000000000000), orderedInterval (-43567317238 / 1000000000000) (-43567317236 / 1000000000000))
    | 8 => (orderedInterval (18216757869 / 1000000000000) (18216758319 / 1000000000000), orderedInterval (-47420496798 / 1000000000000) (-47420496348 / 1000000000000))
    | 9 => (orderedInterval (13440173746 / 1000000000000) (13440173866 / 1000000000000), orderedInterval (-38735148977 / 1000000000000) (-38735148857 / 1000000000000))
    | 10 => (orderedInterval (-16099331065 / 1000000000000) (-16099330828 / 1000000000000), orderedInterval (51515920355 / 1000000000000) (51515920592 / 1000000000000))
    | 11 => (orderedInterval (-18199077009 / 1000000000000) (-18199076374 / 1000000000000), orderedInterval (36193490208 / 1000000000000) (36193490844 / 1000000000000))
    | 12 => (orderedInterval (-31013820543 / 1000000000000) (-31013785738 / 1000000000000), orderedInterval (28200400502 / 1000000000000) (28200435308 / 1000000000000))
    | 13 => (orderedInterval (43055246090 / 1000000000000) (43055281401 / 1000000000000), orderedInterval (-24680625815 / 1000000000000) (-24680590504 / 1000000000000))
    | 14 => (orderedInterval (-37663572377 / 1000000000000) (-37663466007 / 1000000000000), orderedInterval (27448576399 / 1000000000000) (27448682769 / 1000000000000))
    | 15 => (orderedInterval (24416471606 / 1000000000000) (24416471607 / 1000000000000), orderedInterval (44725672546 / 1000000000000) (44725672547 / 1000000000000))
    | 16 => (orderedInterval (-14291698603 / 1000000000000) (-14291698602 / 1000000000000), orderedInterval (-52308512118 / 1000000000000) (-52308512117 / 1000000000000))
    | 17 => (orderedInterval (742732801 / 1000000000000) (742732803 / 1000000000000), orderedInterval (45063700971 / 1000000000000) (45063700973 / 1000000000000))
    | 18 => (orderedInterval (-59356875503 / 1000000000000) (-59356875500 / 1000000000000), orderedInterval (-12025310945 / 1000000000000) (-12025310942 / 1000000000000))
    | 19 => (orderedInterval (-6456599330 / 1000000000000) (-6456599329 / 1000000000000), orderedInterval (-65476201500 / 1000000000000) (-65476201499 / 1000000000000))
    | 20 => (orderedInterval (-82977363153 / 1000000000000) (-82977363063 / 1000000000000), orderedInterval (6532768363 / 1000000000000) (6532768453 / 1000000000000))
    | 21 => (orderedInterval (-2601605347 / 1000000000000) (-2601605333 / 1000000000000), orderedInterval (113451951114 / 1000000000000) (113451951127 / 1000000000000))
    | 22 => (orderedInterval (782938329 / 1000000000000) (782938335 / 1000000000000), orderedInterval (-68850287679 / 1000000000000) (-68850287673 / 1000000000000))
    | 23 => (orderedInterval (55005625575 / 1000000000000) (55005631128 / 1000000000000), orderedInterval (-21274400121 / 1000000000000) (-21274394567 / 1000000000000))
    | 24 => (orderedInterval (19963197950 / 1000000000000) (19963198156 / 1000000000000), orderedInterval (-88516981830 / 1000000000000) (-88516981624 / 1000000000000))
    | 25 => (orderedInterval (43801417593 / 1000000000000) (43801420094 / 1000000000000), orderedInterval (-10136871523 / 1000000000000) (-10136869022 / 1000000000000))
    | _ => (orderedInterval (-40120318401 / 1000000000000) (-40120318400 / 1000000000000), orderedInterval (-37513218616 / 1000000000000) (-37513218615 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (17757061932 / 1000000000000) (17757061951 / 1000000000000)
      | 1 => orderedInterval (-3917235660 / 1000000000000) (-3917235361 / 1000000000000)
      | 2 => orderedInterval (449872956 / 1000000000000) (449872977 / 1000000000000)
      | 3 => orderedInterval (-6168090630 / 1000000000000) (-6168090433 / 1000000000000)
      | 4 => orderedInterval (4821920829 / 1000000000000) (4821925356 / 1000000000000)
      | 5 => orderedInterval (1118836661 / 1000000000000) (1118836678 / 1000000000000)
      | 6 => orderedInterval (7154808445 / 1000000000000) (7154808492 / 1000000000000)
      | 7 => orderedInterval (-4185292891 / 1000000000000) (-4185292444 / 1000000000000)
      | _ => orderedInterval (4082467254 / 1000000000000) (4082467507 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (19837326420 / 1000000000000) (19837326441 / 1000000000000)
      | 1 => orderedInterval (3892893831 / 1000000000000) (3892894207 / 1000000000000)
      | 2 => orderedInterval (988523670 / 1000000000000) (988523704 / 1000000000000)
      | 3 => orderedInterval (32104852773 / 1000000000000) (32104853190 / 1000000000000)
      | 4 => orderedInterval (-4895351833 / 1000000000000) (-4895344422 / 1000000000000)
      | 5 => orderedInterval (6698182850 / 1000000000000) (6698182875 / 1000000000000)
      | 6 => orderedInterval (5295383275 / 1000000000000) (5295383317 / 1000000000000)
      | 7 => orderedInterval (2390078497 / 1000000000000) (2390078977 / 1000000000000)
      | _ => orderedInterval (10032037578 / 1000000000000) (10032038024 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-19260663872 / 1000000000000) (-19260663847 / 1000000000000)
      | 1 => orderedInterval (5269561917 / 1000000000000) (5269562485 / 1000000000000)
      | 2 => orderedInterval (-978613359 / 1000000000000) (-978613305 / 1000000000000)
      | 3 => orderedInterval (27317037391 / 1000000000000) (27317038301 / 1000000000000)
      | 4 => orderedInterval (-12608093675 / 1000000000000) (-12608081291 / 1000000000000)
      | 5 => orderedInterval (-2023696474 / 1000000000000) (-2023696438 / 1000000000000)
      | 6 => orderedInterval (-9439913899 / 1000000000000) (-9439913860 / 1000000000000)
      | 7 => orderedInterval (4926403559 / 1000000000000) (4926404079 / 1000000000000)
      | _ => orderedInterval (631207856 / 1000000000000) (631208660 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-19451414388 / 1000000000000) (-19451414359 / 1000000000000)
      | 1 => orderedInterval (-11361634555 / 1000000000000) (-11361633670 / 1000000000000)
      | 2 => orderedInterval (-6855223032 / 1000000000000) (-6855222943 / 1000000000000)
      | 3 => orderedInterval (-147184328237 / 1000000000000) (-147184326216 / 1000000000000)
      | 4 => orderedInterval (14106954246 / 1000000000000) (14106975271 / 1000000000000)
      | 5 => orderedInterval (-15051946677 / 1000000000000) (-15051946622 / 1000000000000)
      | 6 => orderedInterval (-4451432913 / 1000000000000) (-4451432875 / 1000000000000)
      | 7 => orderedInterval (-2817945591 / 1000000000000) (-2817945030 / 1000000000000)
      | _ => orderedInterval (-18741962852 / 1000000000000) (-18741961388 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (21332256476 / 1000000000000) (21332256510 / 1000000000000)
      | 1 => orderedInterval (-10963941639 / 1000000000000) (-10963940250 / 1000000000000)
      | 2 => orderedInterval (2214502615 / 1000000000000) (2214502765 / 1000000000000)
      | 3 => orderedInterval (-132537578546 / 1000000000000) (-132537574009 / 1000000000000)
      | 4 => orderedInterval (35467531434 / 1000000000000) (35467568052 / 1000000000000)
      | 5 => orderedInterval (3792560715 / 1000000000000) (3792560802 / 1000000000000)
      | 6 => orderedInterval (10412516213 / 1000000000000) (10412516250 / 1000000000000)
      | 7 => orderedInterval (-5746799096 / 1000000000000) (-5746798486 / 1000000000000)
      | _ => orderedInterval (-24482765410 / 1000000000000) (-24482762719 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (21114348896 / 1000000000000) (21114354723 / 1000000000000)
    | 1 => orderedInterval (76343927061 / 1000000000000) (76343936313 / 1000000000000)
    | 2 => orderedInterval (-6166770556 / 1000000000000) (-6166755216 / 1000000000000)
    | 3 => orderedInterval (-211808933999 / 1000000000000) (-211808907832 / 1000000000000)
    | _ => orderedInterval (-100511717238 / 1000000000000) (-100511671085 / 1000000000000)

theorem compactCertificate296_stateChecks0 :
    compactCertificate296.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (339 / 2)) (orderedInterval (36533099511 / 1000000000000) (36533099512 / 1000000000000), orderedInterval (49097987722 / 1000000000000) (49097987723 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 40 12 (499411731338439 / 4000000000000)) (orderedInterval (-1883225382 / 1000000000000) (-1883225374 / 1000000000000), orderedInterval (71389973532 / 1000000000000) (71389973541 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (161499492853287 / 800000000000)) (orderedInterval (56136745361 / 1000000000000) (56136745463 / 1000000000000), orderedInterval (-1622457884 / 1000000000000) (-1622457783 / 1000000000000))) = true
  rfl'

theorem compactCertificate296_stateChecks1 :
    compactCertificate296.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 12 12 (145727097653973 / 4000000000000)) (orderedInterval (-61668517248 / 1000000000000) (-61668511512 / 1000000000000), orderedInterval (117774475514 / 1000000000000) (117774481250 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 31 12 (391443482510481 / 4000000000000)) (orderedInterval (-76682302770 / 1000000000000) (-76682302769 / 1000000000000), orderedInterval (-24610448859 / 1000000000000) (-24610448858 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 85 12 (1062845201617677 / 4000000000000)) (orderedInterval (25130107199 / 1000000000000) (25130110238 / 1000000000000), orderedInterval (-42051901574 / 1000000000000) (-42051898534 / 1000000000000))) = true
  rfl'

theorem compactCertificate296_stateChecks2 :
    compactCertificate296.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (782886965021301 / 4000000000000)) (orderedInterval (56331066534 / 1000000000000) (56331067082 / 1000000000000), orderedInterval (-9058986112 / 1000000000000) (-9058985564 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 107 12 (1341490158444873 / 4000000000000)) (orderedInterval (-311563505 / 1000000000000) (-311563504 / 1000000000000), orderedInterval (-43567317238 / 1000000000000) (-43567317236 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 79 12 (988135579058907 / 4000000000000)) (orderedInterval (18216757869 / 1000000000000) (18216758319 / 1000000000000), orderedInterval (-47420496798 / 1000000000000) (-47420496348 / 1000000000000))) = true
  rfl'

theorem compactCertificate296_stateChecks3 :
    compactCertificate296.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 121 12 (1516054088744661 / 4000000000000)) (orderedInterval (13440173746 / 1000000000000) (13440173866 / 1000000000000), orderedInterval (-38735148977 / 1000000000000) (-38735148857 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (875294236242669 / 4000000000000)) (orderedInterval (-16099331065 / 1000000000000) (-16099330828 / 1000000000000), orderedInterval (51515920355 / 1000000000000) (51515920592 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 124 12 (1553224982159121 / 4000000000000)) (orderedInterval (-18199077009 / 1000000000000) (-18199076374 / 1000000000000), orderedInterval (36193490208 / 1000000000000) (36193490844 / 1000000000000))) = true
  rfl'

theorem compactCertificate296_stateChecks4 :
    compactCertificate296.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 116 12 (1451224257378549 / 4000000000000)) (orderedInterval (-31013820543 / 1000000000000) (-31013785738 / 1000000000000), orderedInterval (28200400502 / 1000000000000) (28200435308 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 82 12 (1035662107059717 / 4000000000000)) (orderedInterval (43055246090 / 1000000000000) (43055281401 / 1000000000000), orderedInterval (-24680625815 / 1000000000000) (-24680590504 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 93 12 (1174330447531443 / 4000000000000)) (orderedInterval (-37663572377 / 1000000000000) (-37663466007 / 1000000000000), orderedInterval (27448576399 / 1000000000000) (27448682769 / 1000000000000))) = true
  rfl'

theorem compactCertificate296_stateChecks5 :
    compactCertificate296.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 78 12 (979034297048067 / 4000000000000)) (orderedInterval (24416471606 / 1000000000000) (24416471607 / 1000000000000), orderedInterval (44725672546 / 1000000000000) (44725672547 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (865006492573407 / 4000000000000)) (orderedInterval (-14291698603 / 1000000000000) (-14291698602 / 1000000000000), orderedInterval (-52308512118 / 1000000000000) (-52308512117 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 100 12 (250712596795293 / 800000000000)) (orderedInterval (742732801 / 1000000000000) (742732803 / 1000000000000), orderedInterval (45063700971 / 1000000000000) (45063700973 / 1000000000000))) = true
  rfl'

theorem compactCertificate296_stateChecks6 :
    compactCertificate296.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (693484237016871 / 4000000000000)) (orderedInterval (-59356875503 / 1000000000000) (-59356875500 / 1000000000000), orderedInterval (-12025310945 / 1000000000000) (-12025310942 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 47 12 (587874267846831 / 4000000000000)) (orderedInterval (-6456599330 / 1000000000000) (-6456599329 / 1000000000000), orderedInterval (-65476201500 / 1000000000000) (-65476201499 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 29 12 (367864420941093 / 4000000000000)) (orderedInterval (-82977363153 / 1000000000000) (-82977363063 / 1000000000000), orderedInterval (6532768363 / 1000000000000) (6532768453 / 1000000000000))) = true
  rfl'

theorem compactCertificate296_stateChecks7 :
    compactCertificate296.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 16 12 (197838709043931 / 4000000000000)) (orderedInterval (-2601605347 / 1000000000000) (-2601605333 / 1000000000000), orderedInterval (113451951114 / 1000000000000) (113451951127 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (537170580164793 / 4000000000000)) (orderedInterval (782938329 / 1000000000000) (782938335 / 1000000000000), orderedInterval (-68850287679 / 1000000000000) (-68850287673 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (733460503089561 / 4000000000000)) (orderedInterval (55005625575 / 1000000000000) (55005631128 / 1000000000000), orderedInterval (-21274400121 / 1000000000000) (-21274394567 / 1000000000000))) = true
  rfl'

theorem compactCertificate296_stateChecks8 :
    compactCertificate296.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 25 12 (310135579058907 / 4000000000000)) (orderedInterval (19963197950 / 1000000000000) (19963198156 / 1000000000000), orderedInterval (-88516981830 / 1000000000000) (-88516981624 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 100 12 (1260683910661947 / 4000000000000)) (orderedInterval (43801417593 / 1000000000000) (43801420094 / 1000000000000), orderedInterval (-10136871523 / 1000000000000) (-10136869022 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (842078427106773 / 4000000000000)) (orderedInterval (-40120318401 / 1000000000000) (-40120318400 / 1000000000000), orderedInterval (-37513218616 / 1000000000000) (-37513218615 / 1000000000000))) = true
  rfl'

theorem compactCertificate296_states : ∀ j,
    BesselStateValid (compactCertificate296.point j) (compactCertificate296.state j) :=
  compactCertificate296.statesValid_of_checks3 compactCertificate296_stateChecks0
    compactCertificate296_stateChecks1 compactCertificate296_stateChecks2
    compactCertificate296_stateChecks3 compactCertificate296_stateChecks4
    compactCertificate296_stateChecks5 compactCertificate296_stateChecks6
    compactCertificate296_stateChecks7 compactCertificate296_stateChecks8

theorem compactCertificate296_chunkChecks0_0 :
    compactCertificate296.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (339 / 2) 0 (IntervalRat.scale (339 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (36533099511 / 1000000000000) (36533099512 / 1000000000000), orderedInterval (49097987722 / 1000000000000) (49097987723 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (499411731338439 / 4000000000000) 0 (IntervalRat.scale (339 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-1883225382 / 1000000000000) (-1883225374 / 1000000000000), orderedInterval (71389973532 / 1000000000000) (71389973541 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (161499492853287 / 800000000000) 0 (IntervalRat.scale (339 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (56136745361 / 1000000000000) (56136745463 / 1000000000000), orderedInterval (-1622457884 / 1000000000000) (-1622457783 / 1000000000000)))) (orderedInterval (17757061932 / 1000000000000) (17757061951 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (145727097653973 / 4000000000000) 0 (IntervalRat.scale (339 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-61668517248 / 1000000000000) (-61668511512 / 1000000000000), orderedInterval (117774475514 / 1000000000000) (117774481250 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (391443482510481 / 4000000000000) 0 (IntervalRat.scale (339 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-76682302770 / 1000000000000) (-76682302769 / 1000000000000), orderedInterval (-24610448859 / 1000000000000) (-24610448858 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (1062845201617677 / 4000000000000) 0 (IntervalRat.scale (339 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (25130107199 / 1000000000000) (25130110238 / 1000000000000), orderedInterval (-42051901574 / 1000000000000) (-42051898534 / 1000000000000)))) (orderedInterval (-3917235660 / 1000000000000) (-3917235361 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (782886965021301 / 4000000000000) 0 (IntervalRat.scale (339 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (56331066534 / 1000000000000) (56331067082 / 1000000000000), orderedInterval (-9058986112 / 1000000000000) (-9058985564 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1341490158444873 / 4000000000000) 0 (IntervalRat.scale (339 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-311563505 / 1000000000000) (-311563504 / 1000000000000), orderedInterval (-43567317238 / 1000000000000) (-43567317236 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (988135579058907 / 4000000000000) 0 (IntervalRat.scale (339 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (18216757869 / 1000000000000) (18216758319 / 1000000000000), orderedInterval (-47420496798 / 1000000000000) (-47420496348 / 1000000000000)))) (orderedInterval (449872956 / 1000000000000) (449872977 / 1000000000000))) = true
  rfl'

theorem compactCertificate296_chunkChecks0_1 :
    compactCertificate296.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1516054088744661 / 4000000000000) 0 (IntervalRat.scale (339 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (13440173746 / 1000000000000) (13440173866 / 1000000000000), orderedInterval (-38735148977 / 1000000000000) (-38735148857 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (875294236242669 / 4000000000000) 0 (IntervalRat.scale (339 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-16099331065 / 1000000000000) (-16099330828 / 1000000000000), orderedInterval (51515920355 / 1000000000000) (51515920592 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1553224982159121 / 4000000000000) 0 (IntervalRat.scale (339 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-18199077009 / 1000000000000) (-18199076374 / 1000000000000), orderedInterval (36193490208 / 1000000000000) (36193490844 / 1000000000000)))) (orderedInterval (-6168090630 / 1000000000000) (-6168090433 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1451224257378549 / 4000000000000) 0 (IntervalRat.scale (339 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-31013820543 / 1000000000000) (-31013785738 / 1000000000000), orderedInterval (28200400502 / 1000000000000) (28200435308 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (1035662107059717 / 4000000000000) 0 (IntervalRat.scale (339 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (43055246090 / 1000000000000) (43055281401 / 1000000000000), orderedInterval (-24680625815 / 1000000000000) (-24680590504 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1174330447531443 / 4000000000000) 0 (IntervalRat.scale (339 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-37663572377 / 1000000000000) (-37663466007 / 1000000000000), orderedInterval (27448576399 / 1000000000000) (27448682769 / 1000000000000)))) (orderedInterval (4821920829 / 1000000000000) (4821925356 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (979034297048067 / 4000000000000) 0 (IntervalRat.scale (339 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (24416471606 / 1000000000000) (24416471607 / 1000000000000), orderedInterval (44725672546 / 1000000000000) (44725672547 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (865006492573407 / 4000000000000) 0 (IntervalRat.scale (339 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-14291698603 / 1000000000000) (-14291698602 / 1000000000000), orderedInterval (-52308512118 / 1000000000000) (-52308512117 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (250712596795293 / 800000000000) 0 (IntervalRat.scale (339 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (742732801 / 1000000000000) (742732803 / 1000000000000), orderedInterval (45063700971 / 1000000000000) (45063700973 / 1000000000000)))) (orderedInterval (1118836661 / 1000000000000) (1118836678 / 1000000000000))) = true
  rfl'

theorem compactCertificate296_chunkChecks0_2 :
    compactCertificate296.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (693484237016871 / 4000000000000) 0 (IntervalRat.scale (339 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-59356875503 / 1000000000000) (-59356875500 / 1000000000000), orderedInterval (-12025310945 / 1000000000000) (-12025310942 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (587874267846831 / 4000000000000) 0 (IntervalRat.scale (339 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-6456599330 / 1000000000000) (-6456599329 / 1000000000000), orderedInterval (-65476201500 / 1000000000000) (-65476201499 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (367864420941093 / 4000000000000) 0 (IntervalRat.scale (339 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-82977363153 / 1000000000000) (-82977363063 / 1000000000000), orderedInterval (6532768363 / 1000000000000) (6532768453 / 1000000000000)))) (orderedInterval (7154808445 / 1000000000000) (7154808492 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (197838709043931 / 4000000000000) 0 (IntervalRat.scale (339 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-2601605347 / 1000000000000) (-2601605333 / 1000000000000), orderedInterval (113451951114 / 1000000000000) (113451951127 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (537170580164793 / 4000000000000) 0 (IntervalRat.scale (339 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (782938329 / 1000000000000) (782938335 / 1000000000000), orderedInterval (-68850287679 / 1000000000000) (-68850287673 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (733460503089561 / 4000000000000) 0 (IntervalRat.scale (339 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (55005625575 / 1000000000000) (55005631128 / 1000000000000), orderedInterval (-21274400121 / 1000000000000) (-21274394567 / 1000000000000)))) (orderedInterval (-4185292891 / 1000000000000) (-4185292444 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (310135579058907 / 4000000000000) 0 (IntervalRat.scale (339 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (19963197950 / 1000000000000) (19963198156 / 1000000000000), orderedInterval (-88516981830 / 1000000000000) (-88516981624 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1260683910661947 / 4000000000000) 0 (IntervalRat.scale (339 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (43801417593 / 1000000000000) (43801420094 / 1000000000000), orderedInterval (-10136871523 / 1000000000000) (-10136869022 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (842078427106773 / 4000000000000) 0 (IntervalRat.scale (339 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-40120318401 / 1000000000000) (-40120318400 / 1000000000000), orderedInterval (-37513218616 / 1000000000000) (-37513218615 / 1000000000000)))) (orderedInterval (4082467254 / 1000000000000) (4082467507 / 1000000000000))) = true
  rfl'

theorem compactCertificate296_chunkChecks0 :
    compactCertificate296.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate296.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate296_chunkChecks0_0
    compactCertificate296_chunkChecks0_1 compactCertificate296_chunkChecks0_2

theorem compactCertificate296_chunkChecks1_0 :
    compactCertificate296.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (339 / 2) 1 (IntervalRat.scale (339 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (36533099511 / 1000000000000) (36533099512 / 1000000000000), orderedInterval (49097987722 / 1000000000000) (49097987723 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (499411731338439 / 4000000000000) 1 (IntervalRat.scale (339 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-1883225382 / 1000000000000) (-1883225374 / 1000000000000), orderedInterval (71389973532 / 1000000000000) (71389973541 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (161499492853287 / 800000000000) 1 (IntervalRat.scale (339 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (56136745361 / 1000000000000) (56136745463 / 1000000000000), orderedInterval (-1622457884 / 1000000000000) (-1622457783 / 1000000000000)))) (orderedInterval (19837326420 / 1000000000000) (19837326441 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (145727097653973 / 4000000000000) 1 (IntervalRat.scale (339 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-61668517248 / 1000000000000) (-61668511512 / 1000000000000), orderedInterval (117774475514 / 1000000000000) (117774481250 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (391443482510481 / 4000000000000) 1 (IntervalRat.scale (339 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-76682302770 / 1000000000000) (-76682302769 / 1000000000000), orderedInterval (-24610448859 / 1000000000000) (-24610448858 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (1062845201617677 / 4000000000000) 1 (IntervalRat.scale (339 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (25130107199 / 1000000000000) (25130110238 / 1000000000000), orderedInterval (-42051901574 / 1000000000000) (-42051898534 / 1000000000000)))) (orderedInterval (3892893831 / 1000000000000) (3892894207 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (782886965021301 / 4000000000000) 1 (IntervalRat.scale (339 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (56331066534 / 1000000000000) (56331067082 / 1000000000000), orderedInterval (-9058986112 / 1000000000000) (-9058985564 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1341490158444873 / 4000000000000) 1 (IntervalRat.scale (339 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-311563505 / 1000000000000) (-311563504 / 1000000000000), orderedInterval (-43567317238 / 1000000000000) (-43567317236 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (988135579058907 / 4000000000000) 1 (IntervalRat.scale (339 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (18216757869 / 1000000000000) (18216758319 / 1000000000000), orderedInterval (-47420496798 / 1000000000000) (-47420496348 / 1000000000000)))) (orderedInterval (988523670 / 1000000000000) (988523704 / 1000000000000))) = true
  rfl'

theorem compactCertificate296_chunkChecks1_1 :
    compactCertificate296.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1516054088744661 / 4000000000000) 1 (IntervalRat.scale (339 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (13440173746 / 1000000000000) (13440173866 / 1000000000000), orderedInterval (-38735148977 / 1000000000000) (-38735148857 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (875294236242669 / 4000000000000) 1 (IntervalRat.scale (339 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-16099331065 / 1000000000000) (-16099330828 / 1000000000000), orderedInterval (51515920355 / 1000000000000) (51515920592 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1553224982159121 / 4000000000000) 1 (IntervalRat.scale (339 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-18199077009 / 1000000000000) (-18199076374 / 1000000000000), orderedInterval (36193490208 / 1000000000000) (36193490844 / 1000000000000)))) (orderedInterval (32104852773 / 1000000000000) (32104853190 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1451224257378549 / 4000000000000) 1 (IntervalRat.scale (339 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-31013820543 / 1000000000000) (-31013785738 / 1000000000000), orderedInterval (28200400502 / 1000000000000) (28200435308 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (1035662107059717 / 4000000000000) 1 (IntervalRat.scale (339 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (43055246090 / 1000000000000) (43055281401 / 1000000000000), orderedInterval (-24680625815 / 1000000000000) (-24680590504 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1174330447531443 / 4000000000000) 1 (IntervalRat.scale (339 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-37663572377 / 1000000000000) (-37663466007 / 1000000000000), orderedInterval (27448576399 / 1000000000000) (27448682769 / 1000000000000)))) (orderedInterval (-4895351833 / 1000000000000) (-4895344422 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (979034297048067 / 4000000000000) 1 (IntervalRat.scale (339 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (24416471606 / 1000000000000) (24416471607 / 1000000000000), orderedInterval (44725672546 / 1000000000000) (44725672547 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (865006492573407 / 4000000000000) 1 (IntervalRat.scale (339 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-14291698603 / 1000000000000) (-14291698602 / 1000000000000), orderedInterval (-52308512118 / 1000000000000) (-52308512117 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (250712596795293 / 800000000000) 1 (IntervalRat.scale (339 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (742732801 / 1000000000000) (742732803 / 1000000000000), orderedInterval (45063700971 / 1000000000000) (45063700973 / 1000000000000)))) (orderedInterval (6698182850 / 1000000000000) (6698182875 / 1000000000000))) = true
  rfl'

theorem compactCertificate296_chunkChecks1_2 :
    compactCertificate296.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (693484237016871 / 4000000000000) 1 (IntervalRat.scale (339 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-59356875503 / 1000000000000) (-59356875500 / 1000000000000), orderedInterval (-12025310945 / 1000000000000) (-12025310942 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (587874267846831 / 4000000000000) 1 (IntervalRat.scale (339 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-6456599330 / 1000000000000) (-6456599329 / 1000000000000), orderedInterval (-65476201500 / 1000000000000) (-65476201499 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (367864420941093 / 4000000000000) 1 (IntervalRat.scale (339 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-82977363153 / 1000000000000) (-82977363063 / 1000000000000), orderedInterval (6532768363 / 1000000000000) (6532768453 / 1000000000000)))) (orderedInterval (5295383275 / 1000000000000) (5295383317 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (197838709043931 / 4000000000000) 1 (IntervalRat.scale (339 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-2601605347 / 1000000000000) (-2601605333 / 1000000000000), orderedInterval (113451951114 / 1000000000000) (113451951127 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (537170580164793 / 4000000000000) 1 (IntervalRat.scale (339 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (782938329 / 1000000000000) (782938335 / 1000000000000), orderedInterval (-68850287679 / 1000000000000) (-68850287673 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (733460503089561 / 4000000000000) 1 (IntervalRat.scale (339 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (55005625575 / 1000000000000) (55005631128 / 1000000000000), orderedInterval (-21274400121 / 1000000000000) (-21274394567 / 1000000000000)))) (orderedInterval (2390078497 / 1000000000000) (2390078977 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (310135579058907 / 4000000000000) 1 (IntervalRat.scale (339 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (19963197950 / 1000000000000) (19963198156 / 1000000000000), orderedInterval (-88516981830 / 1000000000000) (-88516981624 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1260683910661947 / 4000000000000) 1 (IntervalRat.scale (339 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (43801417593 / 1000000000000) (43801420094 / 1000000000000), orderedInterval (-10136871523 / 1000000000000) (-10136869022 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (842078427106773 / 4000000000000) 1 (IntervalRat.scale (339 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-40120318401 / 1000000000000) (-40120318400 / 1000000000000), orderedInterval (-37513218616 / 1000000000000) (-37513218615 / 1000000000000)))) (orderedInterval (10032037578 / 1000000000000) (10032038024 / 1000000000000))) = true
  rfl'

theorem compactCertificate296_chunkChecks1 :
    compactCertificate296.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate296.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate296_chunkChecks1_0
    compactCertificate296_chunkChecks1_1 compactCertificate296_chunkChecks1_2

theorem compactCertificate296_chunkChecks2_0 :
    compactCertificate296.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (339 / 2) 2 (IntervalRat.scale (339 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (36533099511 / 1000000000000) (36533099512 / 1000000000000), orderedInterval (49097987722 / 1000000000000) (49097987723 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (499411731338439 / 4000000000000) 2 (IntervalRat.scale (339 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-1883225382 / 1000000000000) (-1883225374 / 1000000000000), orderedInterval (71389973532 / 1000000000000) (71389973541 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (161499492853287 / 800000000000) 2 (IntervalRat.scale (339 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (56136745361 / 1000000000000) (56136745463 / 1000000000000), orderedInterval (-1622457884 / 1000000000000) (-1622457783 / 1000000000000)))) (orderedInterval (-19260663872 / 1000000000000) (-19260663847 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (145727097653973 / 4000000000000) 2 (IntervalRat.scale (339 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-61668517248 / 1000000000000) (-61668511512 / 1000000000000), orderedInterval (117774475514 / 1000000000000) (117774481250 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (391443482510481 / 4000000000000) 2 (IntervalRat.scale (339 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-76682302770 / 1000000000000) (-76682302769 / 1000000000000), orderedInterval (-24610448859 / 1000000000000) (-24610448858 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (1062845201617677 / 4000000000000) 2 (IntervalRat.scale (339 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (25130107199 / 1000000000000) (25130110238 / 1000000000000), orderedInterval (-42051901574 / 1000000000000) (-42051898534 / 1000000000000)))) (orderedInterval (5269561917 / 1000000000000) (5269562485 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (782886965021301 / 4000000000000) 2 (IntervalRat.scale (339 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (56331066534 / 1000000000000) (56331067082 / 1000000000000), orderedInterval (-9058986112 / 1000000000000) (-9058985564 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1341490158444873 / 4000000000000) 2 (IntervalRat.scale (339 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-311563505 / 1000000000000) (-311563504 / 1000000000000), orderedInterval (-43567317238 / 1000000000000) (-43567317236 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (988135579058907 / 4000000000000) 2 (IntervalRat.scale (339 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (18216757869 / 1000000000000) (18216758319 / 1000000000000), orderedInterval (-47420496798 / 1000000000000) (-47420496348 / 1000000000000)))) (orderedInterval (-978613359 / 1000000000000) (-978613305 / 1000000000000))) = true
  rfl'

theorem compactCertificate296_chunkChecks2_1 :
    compactCertificate296.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1516054088744661 / 4000000000000) 2 (IntervalRat.scale (339 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (13440173746 / 1000000000000) (13440173866 / 1000000000000), orderedInterval (-38735148977 / 1000000000000) (-38735148857 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (875294236242669 / 4000000000000) 2 (IntervalRat.scale (339 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-16099331065 / 1000000000000) (-16099330828 / 1000000000000), orderedInterval (51515920355 / 1000000000000) (51515920592 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1553224982159121 / 4000000000000) 2 (IntervalRat.scale (339 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-18199077009 / 1000000000000) (-18199076374 / 1000000000000), orderedInterval (36193490208 / 1000000000000) (36193490844 / 1000000000000)))) (orderedInterval (27317037391 / 1000000000000) (27317038301 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1451224257378549 / 4000000000000) 2 (IntervalRat.scale (339 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-31013820543 / 1000000000000) (-31013785738 / 1000000000000), orderedInterval (28200400502 / 1000000000000) (28200435308 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (1035662107059717 / 4000000000000) 2 (IntervalRat.scale (339 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (43055246090 / 1000000000000) (43055281401 / 1000000000000), orderedInterval (-24680625815 / 1000000000000) (-24680590504 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1174330447531443 / 4000000000000) 2 (IntervalRat.scale (339 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-37663572377 / 1000000000000) (-37663466007 / 1000000000000), orderedInterval (27448576399 / 1000000000000) (27448682769 / 1000000000000)))) (orderedInterval (-12608093675 / 1000000000000) (-12608081291 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (979034297048067 / 4000000000000) 2 (IntervalRat.scale (339 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (24416471606 / 1000000000000) (24416471607 / 1000000000000), orderedInterval (44725672546 / 1000000000000) (44725672547 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (865006492573407 / 4000000000000) 2 (IntervalRat.scale (339 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-14291698603 / 1000000000000) (-14291698602 / 1000000000000), orderedInterval (-52308512118 / 1000000000000) (-52308512117 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (250712596795293 / 800000000000) 2 (IntervalRat.scale (339 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (742732801 / 1000000000000) (742732803 / 1000000000000), orderedInterval (45063700971 / 1000000000000) (45063700973 / 1000000000000)))) (orderedInterval (-2023696474 / 1000000000000) (-2023696438 / 1000000000000))) = true
  rfl'

theorem compactCertificate296_chunkChecks2_2 :
    compactCertificate296.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (693484237016871 / 4000000000000) 2 (IntervalRat.scale (339 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-59356875503 / 1000000000000) (-59356875500 / 1000000000000), orderedInterval (-12025310945 / 1000000000000) (-12025310942 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (587874267846831 / 4000000000000) 2 (IntervalRat.scale (339 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-6456599330 / 1000000000000) (-6456599329 / 1000000000000), orderedInterval (-65476201500 / 1000000000000) (-65476201499 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (367864420941093 / 4000000000000) 2 (IntervalRat.scale (339 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-82977363153 / 1000000000000) (-82977363063 / 1000000000000), orderedInterval (6532768363 / 1000000000000) (6532768453 / 1000000000000)))) (orderedInterval (-9439913899 / 1000000000000) (-9439913860 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (197838709043931 / 4000000000000) 2 (IntervalRat.scale (339 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-2601605347 / 1000000000000) (-2601605333 / 1000000000000), orderedInterval (113451951114 / 1000000000000) (113451951127 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (537170580164793 / 4000000000000) 2 (IntervalRat.scale (339 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (782938329 / 1000000000000) (782938335 / 1000000000000), orderedInterval (-68850287679 / 1000000000000) (-68850287673 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (733460503089561 / 4000000000000) 2 (IntervalRat.scale (339 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (55005625575 / 1000000000000) (55005631128 / 1000000000000), orderedInterval (-21274400121 / 1000000000000) (-21274394567 / 1000000000000)))) (orderedInterval (4926403559 / 1000000000000) (4926404079 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (310135579058907 / 4000000000000) 2 (IntervalRat.scale (339 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (19963197950 / 1000000000000) (19963198156 / 1000000000000), orderedInterval (-88516981830 / 1000000000000) (-88516981624 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1260683910661947 / 4000000000000) 2 (IntervalRat.scale (339 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (43801417593 / 1000000000000) (43801420094 / 1000000000000), orderedInterval (-10136871523 / 1000000000000) (-10136869022 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (842078427106773 / 4000000000000) 2 (IntervalRat.scale (339 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-40120318401 / 1000000000000) (-40120318400 / 1000000000000), orderedInterval (-37513218616 / 1000000000000) (-37513218615 / 1000000000000)))) (orderedInterval (631207856 / 1000000000000) (631208660 / 1000000000000))) = true
  rfl'

theorem compactCertificate296_chunkChecks2 :
    compactCertificate296.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate296.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate296_chunkChecks2_0
    compactCertificate296_chunkChecks2_1 compactCertificate296_chunkChecks2_2

theorem compactCertificate296_chunkChecks3_0 :
    compactCertificate296.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (339 / 2) 3 (IntervalRat.scale (339 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (36533099511 / 1000000000000) (36533099512 / 1000000000000), orderedInterval (49097987722 / 1000000000000) (49097987723 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (499411731338439 / 4000000000000) 3 (IntervalRat.scale (339 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-1883225382 / 1000000000000) (-1883225374 / 1000000000000), orderedInterval (71389973532 / 1000000000000) (71389973541 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (161499492853287 / 800000000000) 3 (IntervalRat.scale (339 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (56136745361 / 1000000000000) (56136745463 / 1000000000000), orderedInterval (-1622457884 / 1000000000000) (-1622457783 / 1000000000000)))) (orderedInterval (-19451414388 / 1000000000000) (-19451414359 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (145727097653973 / 4000000000000) 3 (IntervalRat.scale (339 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-61668517248 / 1000000000000) (-61668511512 / 1000000000000), orderedInterval (117774475514 / 1000000000000) (117774481250 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (391443482510481 / 4000000000000) 3 (IntervalRat.scale (339 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-76682302770 / 1000000000000) (-76682302769 / 1000000000000), orderedInterval (-24610448859 / 1000000000000) (-24610448858 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (1062845201617677 / 4000000000000) 3 (IntervalRat.scale (339 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (25130107199 / 1000000000000) (25130110238 / 1000000000000), orderedInterval (-42051901574 / 1000000000000) (-42051898534 / 1000000000000)))) (orderedInterval (-11361634555 / 1000000000000) (-11361633670 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (782886965021301 / 4000000000000) 3 (IntervalRat.scale (339 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (56331066534 / 1000000000000) (56331067082 / 1000000000000), orderedInterval (-9058986112 / 1000000000000) (-9058985564 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1341490158444873 / 4000000000000) 3 (IntervalRat.scale (339 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-311563505 / 1000000000000) (-311563504 / 1000000000000), orderedInterval (-43567317238 / 1000000000000) (-43567317236 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (988135579058907 / 4000000000000) 3 (IntervalRat.scale (339 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (18216757869 / 1000000000000) (18216758319 / 1000000000000), orderedInterval (-47420496798 / 1000000000000) (-47420496348 / 1000000000000)))) (orderedInterval (-6855223032 / 1000000000000) (-6855222943 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate296_chunkChecks3_1 :
    compactCertificate296.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1516054088744661 / 4000000000000) 3 (IntervalRat.scale (339 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (13440173746 / 1000000000000) (13440173866 / 1000000000000), orderedInterval (-38735148977 / 1000000000000) (-38735148857 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (875294236242669 / 4000000000000) 3 (IntervalRat.scale (339 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-16099331065 / 1000000000000) (-16099330828 / 1000000000000), orderedInterval (51515920355 / 1000000000000) (51515920592 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1553224982159121 / 4000000000000) 3 (IntervalRat.scale (339 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-18199077009 / 1000000000000) (-18199076374 / 1000000000000), orderedInterval (36193490208 / 1000000000000) (36193490844 / 1000000000000)))) (orderedInterval (-147184328237 / 1000000000000) (-147184326216 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1451224257378549 / 4000000000000) 3 (IntervalRat.scale (339 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-31013820543 / 1000000000000) (-31013785738 / 1000000000000), orderedInterval (28200400502 / 1000000000000) (28200435308 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (1035662107059717 / 4000000000000) 3 (IntervalRat.scale (339 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (43055246090 / 1000000000000) (43055281401 / 1000000000000), orderedInterval (-24680625815 / 1000000000000) (-24680590504 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1174330447531443 / 4000000000000) 3 (IntervalRat.scale (339 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-37663572377 / 1000000000000) (-37663466007 / 1000000000000), orderedInterval (27448576399 / 1000000000000) (27448682769 / 1000000000000)))) (orderedInterval (14106954246 / 1000000000000) (14106975271 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (979034297048067 / 4000000000000) 3 (IntervalRat.scale (339 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (24416471606 / 1000000000000) (24416471607 / 1000000000000), orderedInterval (44725672546 / 1000000000000) (44725672547 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (865006492573407 / 4000000000000) 3 (IntervalRat.scale (339 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-14291698603 / 1000000000000) (-14291698602 / 1000000000000), orderedInterval (-52308512118 / 1000000000000) (-52308512117 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (250712596795293 / 800000000000) 3 (IntervalRat.scale (339 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (742732801 / 1000000000000) (742732803 / 1000000000000), orderedInterval (45063700971 / 1000000000000) (45063700973 / 1000000000000)))) (orderedInterval (-15051946677 / 1000000000000) (-15051946622 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate296_chunkChecks3_2 :
    compactCertificate296.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (693484237016871 / 4000000000000) 3 (IntervalRat.scale (339 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-59356875503 / 1000000000000) (-59356875500 / 1000000000000), orderedInterval (-12025310945 / 1000000000000) (-12025310942 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (587874267846831 / 4000000000000) 3 (IntervalRat.scale (339 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-6456599330 / 1000000000000) (-6456599329 / 1000000000000), orderedInterval (-65476201500 / 1000000000000) (-65476201499 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (367864420941093 / 4000000000000) 3 (IntervalRat.scale (339 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-82977363153 / 1000000000000) (-82977363063 / 1000000000000), orderedInterval (6532768363 / 1000000000000) (6532768453 / 1000000000000)))) (orderedInterval (-4451432913 / 1000000000000) (-4451432875 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (197838709043931 / 4000000000000) 3 (IntervalRat.scale (339 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-2601605347 / 1000000000000) (-2601605333 / 1000000000000), orderedInterval (113451951114 / 1000000000000) (113451951127 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (537170580164793 / 4000000000000) 3 (IntervalRat.scale (339 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (782938329 / 1000000000000) (782938335 / 1000000000000), orderedInterval (-68850287679 / 1000000000000) (-68850287673 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (733460503089561 / 4000000000000) 3 (IntervalRat.scale (339 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (55005625575 / 1000000000000) (55005631128 / 1000000000000), orderedInterval (-21274400121 / 1000000000000) (-21274394567 / 1000000000000)))) (orderedInterval (-2817945591 / 1000000000000) (-2817945030 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (310135579058907 / 4000000000000) 3 (IntervalRat.scale (339 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (19963197950 / 1000000000000) (19963198156 / 1000000000000), orderedInterval (-88516981830 / 1000000000000) (-88516981624 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1260683910661947 / 4000000000000) 3 (IntervalRat.scale (339 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (43801417593 / 1000000000000) (43801420094 / 1000000000000), orderedInterval (-10136871523 / 1000000000000) (-10136869022 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (842078427106773 / 4000000000000) 3 (IntervalRat.scale (339 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-40120318401 / 1000000000000) (-40120318400 / 1000000000000), orderedInterval (-37513218616 / 1000000000000) (-37513218615 / 1000000000000)))) (orderedInterval (-18741962852 / 1000000000000) (-18741961388 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate296_chunkChecks3 :
    compactCertificate296.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate296.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate296_chunkChecks3_0
    compactCertificate296_chunkChecks3_1 compactCertificate296_chunkChecks3_2

theorem compactCertificate296_chunkChecks4_0 :
    compactCertificate296.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (339 / 2) 4 (IntervalRat.scale (339 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (36533099511 / 1000000000000) (36533099512 / 1000000000000), orderedInterval (49097987722 / 1000000000000) (49097987723 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (499411731338439 / 4000000000000) 4 (IntervalRat.scale (339 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-1883225382 / 1000000000000) (-1883225374 / 1000000000000), orderedInterval (71389973532 / 1000000000000) (71389973541 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (161499492853287 / 800000000000) 4 (IntervalRat.scale (339 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (56136745361 / 1000000000000) (56136745463 / 1000000000000), orderedInterval (-1622457884 / 1000000000000) (-1622457783 / 1000000000000)))) (orderedInterval (21332256476 / 1000000000000) (21332256510 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (145727097653973 / 4000000000000) 4 (IntervalRat.scale (339 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-61668517248 / 1000000000000) (-61668511512 / 1000000000000), orderedInterval (117774475514 / 1000000000000) (117774481250 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (391443482510481 / 4000000000000) 4 (IntervalRat.scale (339 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-76682302770 / 1000000000000) (-76682302769 / 1000000000000), orderedInterval (-24610448859 / 1000000000000) (-24610448858 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (1062845201617677 / 4000000000000) 4 (IntervalRat.scale (339 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (25130107199 / 1000000000000) (25130110238 / 1000000000000), orderedInterval (-42051901574 / 1000000000000) (-42051898534 / 1000000000000)))) (orderedInterval (-10963941639 / 1000000000000) (-10963940250 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (782886965021301 / 4000000000000) 4 (IntervalRat.scale (339 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (56331066534 / 1000000000000) (56331067082 / 1000000000000), orderedInterval (-9058986112 / 1000000000000) (-9058985564 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1341490158444873 / 4000000000000) 4 (IntervalRat.scale (339 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-311563505 / 1000000000000) (-311563504 / 1000000000000), orderedInterval (-43567317238 / 1000000000000) (-43567317236 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (988135579058907 / 4000000000000) 4 (IntervalRat.scale (339 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (18216757869 / 1000000000000) (18216758319 / 1000000000000), orderedInterval (-47420496798 / 1000000000000) (-47420496348 / 1000000000000)))) (orderedInterval (2214502615 / 1000000000000) (2214502765 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate296_chunkChecks4_1 :
    compactCertificate296.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1516054088744661 / 4000000000000) 4 (IntervalRat.scale (339 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (13440173746 / 1000000000000) (13440173866 / 1000000000000), orderedInterval (-38735148977 / 1000000000000) (-38735148857 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (875294236242669 / 4000000000000) 4 (IntervalRat.scale (339 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-16099331065 / 1000000000000) (-16099330828 / 1000000000000), orderedInterval (51515920355 / 1000000000000) (51515920592 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1553224982159121 / 4000000000000) 4 (IntervalRat.scale (339 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-18199077009 / 1000000000000) (-18199076374 / 1000000000000), orderedInterval (36193490208 / 1000000000000) (36193490844 / 1000000000000)))) (orderedInterval (-132537578546 / 1000000000000) (-132537574009 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1451224257378549 / 4000000000000) 4 (IntervalRat.scale (339 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-31013820543 / 1000000000000) (-31013785738 / 1000000000000), orderedInterval (28200400502 / 1000000000000) (28200435308 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (1035662107059717 / 4000000000000) 4 (IntervalRat.scale (339 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (43055246090 / 1000000000000) (43055281401 / 1000000000000), orderedInterval (-24680625815 / 1000000000000) (-24680590504 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1174330447531443 / 4000000000000) 4 (IntervalRat.scale (339 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-37663572377 / 1000000000000) (-37663466007 / 1000000000000), orderedInterval (27448576399 / 1000000000000) (27448682769 / 1000000000000)))) (orderedInterval (35467531434 / 1000000000000) (35467568052 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (979034297048067 / 4000000000000) 4 (IntervalRat.scale (339 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (24416471606 / 1000000000000) (24416471607 / 1000000000000), orderedInterval (44725672546 / 1000000000000) (44725672547 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (865006492573407 / 4000000000000) 4 (IntervalRat.scale (339 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-14291698603 / 1000000000000) (-14291698602 / 1000000000000), orderedInterval (-52308512118 / 1000000000000) (-52308512117 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (250712596795293 / 800000000000) 4 (IntervalRat.scale (339 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (742732801 / 1000000000000) (742732803 / 1000000000000), orderedInterval (45063700971 / 1000000000000) (45063700973 / 1000000000000)))) (orderedInterval (3792560715 / 1000000000000) (3792560802 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate296_chunkChecks4_2 :
    compactCertificate296.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (693484237016871 / 4000000000000) 4 (IntervalRat.scale (339 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-59356875503 / 1000000000000) (-59356875500 / 1000000000000), orderedInterval (-12025310945 / 1000000000000) (-12025310942 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (587874267846831 / 4000000000000) 4 (IntervalRat.scale (339 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-6456599330 / 1000000000000) (-6456599329 / 1000000000000), orderedInterval (-65476201500 / 1000000000000) (-65476201499 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (367864420941093 / 4000000000000) 4 (IntervalRat.scale (339 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-82977363153 / 1000000000000) (-82977363063 / 1000000000000), orderedInterval (6532768363 / 1000000000000) (6532768453 / 1000000000000)))) (orderedInterval (10412516213 / 1000000000000) (10412516250 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (197838709043931 / 4000000000000) 4 (IntervalRat.scale (339 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-2601605347 / 1000000000000) (-2601605333 / 1000000000000), orderedInterval (113451951114 / 1000000000000) (113451951127 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (537170580164793 / 4000000000000) 4 (IntervalRat.scale (339 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (782938329 / 1000000000000) (782938335 / 1000000000000), orderedInterval (-68850287679 / 1000000000000) (-68850287673 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (733460503089561 / 4000000000000) 4 (IntervalRat.scale (339 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (55005625575 / 1000000000000) (55005631128 / 1000000000000), orderedInterval (-21274400121 / 1000000000000) (-21274394567 / 1000000000000)))) (orderedInterval (-5746799096 / 1000000000000) (-5746798486 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (310135579058907 / 4000000000000) 4 (IntervalRat.scale (339 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (19963197950 / 1000000000000) (19963198156 / 1000000000000), orderedInterval (-88516981830 / 1000000000000) (-88516981624 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1260683910661947 / 4000000000000) 4 (IntervalRat.scale (339 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (43801417593 / 1000000000000) (43801420094 / 1000000000000), orderedInterval (-10136871523 / 1000000000000) (-10136869022 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (842078427106773 / 4000000000000) 4 (IntervalRat.scale (339 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-40120318401 / 1000000000000) (-40120318400 / 1000000000000), orderedInterval (-37513218616 / 1000000000000) (-37513218615 / 1000000000000)))) (orderedInterval (-24482765410 / 1000000000000) (-24482762719 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate296_chunkChecks4 :
    compactCertificate296.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate296.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate296_chunkChecks4_0
    compactCertificate296_chunkChecks4_1 compactCertificate296_chunkChecks4_2

theorem compactCertificate296_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate296.chunkCheck r b = true :=
  compactCertificate296.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate296_chunkChecks0
    · exact compactCertificate296_chunkChecks1
    · exact compactCertificate296_chunkChecks2
    · exact compactCertificate296_chunkChecks3
    · exact compactCertificate296_chunkChecks4)

theorem compactCertificate296_coefficient0 :
    compactCertificate296.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate296_coefficient1 :
    compactCertificate296.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate296_coefficient2 :
    compactCertificate296.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate296_coefficient3 :
    compactCertificate296.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate296_coefficient4 :
    compactCertificate296.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate296_coefficients : ∀ r : Fin 5,
    compactCertificate296.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate296_coefficient0
  · exact compactCertificate296_coefficient1
  · exact compactCertificate296_coefficient2
  · exact compactCertificate296_coefficient3
  · exact compactCertificate296_coefficient4

theorem compactCertificate296_lower : (1 : ℚ) ≤ compactCertificate296.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate296, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate296_proves {t : ℝ} (ht : t ∈ compactCertificate296.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate296.proves compactCertificate296_states compactCertificate296_chunks
    compactCertificate296_coefficients compactCertificate296_lower ht

end Erdos232
