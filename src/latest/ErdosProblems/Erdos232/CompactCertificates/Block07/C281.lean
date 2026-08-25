/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate281 : CompactCertificate where
  left := 155
  right := 156
  center := 311 / 2
  grid := fun i =>
    match i.val with
    | 0 => 50
    | 1 => 36
    | 2 => 59
    | 3 => 11
    | 4 => 29
    | 5 => 78
    | 6 => 57
    | 7 => 98
    | 8 => 72
    | 9 => 111
    | 10 => 64
    | 11 => 113
    | 12 => 106
    | 13 => 76
    | 14 => 86
    | 15 => 72
    | 16 => 63
    | 17 => 92
    | 18 => 51
    | 19 => 43
    | 20 => 27
    | 21 => 14
    | 22 => 39
    | 23 => 54
    | 24 => 23
    | 25 => 92
    | _ => 62
  point := fun i =>
    match i.val with
    | 0 => 311 / 2
    | 1 => 458162384797211 / 4000000000000
    | 2 => 148160301703163 / 800000000000
    | 3 => 133690641210577 / 4000000000000
    | 4 => 359111867435869 / 4000000000000
    | 5 => 975058577295273 / 4000000000000
    | 6 => 718223734872049 / 4000000000000
    | 7 => 1230688611434677 / 4000000000000
    | 8 => 906519661024543 / 4000000000000
    | 9 => 1390834282004689 / 4000000000000
    | 10 => 802998547113481 / 4000000000000
    | 11 => 1424935013131229 / 4000000000000
    | 12 => 1331359126975601 / 4000000000000
    | 13 => 950120694087233 / 4000000000000
    | 14 => 1077335602307607 / 4000000000000
    | 15 => 898170107321383 / 4000000000000
    | 16 => 793560528585043 / 4000000000000
    | 17 => 230004771691257 / 800000000000
    | 18 => 636205302985979 / 4000000000000
    | 19 => 539318281122019 / 4000000000000
    | 20 => 337480338975457 / 4000000000000
    | 21 => 181498048709919 / 4000000000000
    | 22 => 492802508646757 / 4000000000000
    | 23 => 672879694574789 / 4000000000000
    | 24 => 284519661024543 / 4000000000000
    | 25 => 1156556626005503 / 4000000000000
    | _ => 772526226637777 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-45677844957 / 1000000000000) (-45677782448 / 1000000000000), orderedInterval (44952583106 / 1000000000000) (44952645615 / 1000000000000))
    | 1 => (orderedInterval (59042605235 / 1000000000000) (59042668067 / 1000000000000), orderedInterval (-45776777385 / 1000000000000) (-45776714552 / 1000000000000))
    | 2 => (orderedInterval (-34595124086 / 1000000000000) (-34595124085 / 1000000000000), orderedInterval (-47242063549 / 1000000000000) (-47242063548 / 1000000000000))
    | 3 => (orderedInterval (47736127395 / 1000000000000) (47736128755 / 1000000000000), orderedInterval (-130214666711 / 1000000000000) (-130214665351 / 1000000000000))
    | 4 => (orderedInterval (43598191263 / 1000000000000) (43598199382 / 1000000000000), orderedInterval (-72286511162 / 1000000000000) (-72286503043 / 1000000000000))
    | 5 => (orderedInterval (-24262367837 / 1000000000000) (-24262365737 / 1000000000000), orderedInterval (45027059994 / 1000000000000) (45027062094 / 1000000000000))
    | 6 => (orderedInterval (-56868131970 / 1000000000000) (-56868131968 / 1000000000000), orderedInterval (-17491790245 / 1000000000000) (-17491790244 / 1000000000000))
    | 7 => (orderedInterval (24968942474 / 1000000000000) (24968942475 / 1000000000000), orderedInterval (37981821495 / 1000000000000) (37981821496 / 1000000000000))
    | 8 => (orderedInterval (49774497791 / 1000000000000) (49774497792 / 1000000000000), orderedInterval (18099146717 / 1000000000000) (18099146718 / 1000000000000))
    | 9 => (orderedInterval (9470376516 / 1000000000000) (9470376546 / 1000000000000), orderedInterval (-41741475964 / 1000000000000) (-41741475934 / 1000000000000))
    | 10 => (orderedInterval (25628140021 / 1000000000000) (25628140022 / 1000000000000), orderedInterval (50080129795 / 1000000000000) (50080129796 / 1000000000000))
    | 11 => (orderedInterval (-38101494447 / 1000000000000) (-38101465498 / 1000000000000), orderedInterval (18366312775 / 1000000000000) (18366341723 / 1000000000000))
    | 12 => (orderedInterval (25267982557 / 1000000000000) (25267982558 / 1000000000000), orderedInterval (35658275988 / 1000000000000) (35658275989 / 1000000000000))
    | 13 => (orderedInterval (-22331450054 / 1000000000000) (-22331448809 / 1000000000000), orderedInterval (46753257866 / 1000000000000) (46753259112 / 1000000000000))
    | 14 => (orderedInterval (-2824727441 / 1000000000000) (-2824727437 / 1000000000000), orderedInterval (48540872619 / 1000000000000) (48540872624 / 1000000000000))
    | 15 => (orderedInterval (-40605045392 / 1000000000000) (-40604959242 / 1000000000000), orderedInterval (34534794831 / 1000000000000) (34534880981 / 1000000000000))
    | 16 => (orderedInterval (-53838378122 / 1000000000000) (-53838378121 / 1000000000000), orderedInterval (-17481050172 / 1000000000000) (-17481050171 / 1000000000000))
    | 17 => (orderedInterval (-31576056684 / 1000000000000) (-31576036698 / 1000000000000), orderedInterval (34943831184 / 1000000000000) (34943851171 / 1000000000000))
    | 18 => (orderedInterval (23776967705 / 1000000000000) (23776968675 / 1000000000000), orderedInterval (-58703031408 / 1000000000000) (-58703030438 / 1000000000000))
    | 19 => (orderedInterval (-34473540788 / 1000000000000) (-34473540787 / 1000000000000), orderedInterval (-59313341192 / 1000000000000) (-59313341191 / 1000000000000))
    | 20 => (orderedInterval (-28229962045 / 1000000000000) (-28229962044 / 1000000000000), orderedInterval (-81983401482 / 1000000000000) (-81983401481 / 1000000000000))
    | 21 => (orderedInterval (97485281482 / 1000000000000) (97485310633 / 1000000000000), orderedInterval (-68354522738 / 1000000000000) (-68354493587 / 1000000000000))
    | 22 => (orderedInterval (-71465892235 / 1000000000000) (-71465892228 / 1000000000000), orderedInterval (-7451197369 / 1000000000000) (-7451197362 / 1000000000000))
    | 23 => (orderedInterval (-36808376309 / 1000000000000) (-36808361873 / 1000000000000), orderedInterval (49400349430 / 1000000000000) (49400363867 / 1000000000000))
    | 24 => (orderedInterval (31823227993 / 1000000000000) (31823228980 / 1000000000000), orderedInterval (-89316627574 / 1000000000000) (-89316626587 / 1000000000000))
    | 25 => (orderedInterval (36685931149 / 1000000000000) (36685931150 / 1000000000000), orderedInterval (29192638739 / 1000000000000) (29192638740 / 1000000000000))
    | _ => (orderedInterval (-43601462097 / 1000000000000) (-43601367605 / 1000000000000), orderedInterval (37465419296 / 1000000000000) (37465513788 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-19585017484 / 1000000000000) (-19584992111 / 1000000000000)
      | 1 => orderedInterval (2798745794 / 1000000000000) (2798746274 / 1000000000000)
      | 2 => orderedInterval (432809315 / 1000000000000) (432809325 / 1000000000000)
      | 3 => orderedInterval (-5200289246 / 1000000000000) (-5200285063 / 1000000000000)
      | 4 => orderedInterval (-2553596243 / 1000000000000) (-2553596106 / 1000000000000)
      | 5 => orderedInterval (1803626026 / 1000000000000) (1803627548 / 1000000000000)
      | 6 => orderedInterval (-2769590778 / 1000000000000) (-2769590583 / 1000000000000)
      | 7 => orderedInterval (2642210419 / 1000000000000) (2642212083 / 1000000000000)
      | _ => orderedInterval (5386314024 / 1000000000000) (5386331803 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (14201725304 / 1000000000000) (14201750524 / 1000000000000)
      | 1 => orderedInterval (-6238035257 / 1000000000000) (-6238034827 / 1000000000000)
      | 2 => orderedInterval (-1680442500 / 1000000000000) (-1680442484 / 1000000000000)
      | 3 => orderedInterval (27356330139 / 1000000000000) (27356339706 / 1000000000000)
      | 4 => orderedInterval (4950009651 / 1000000000000) (4950009862 / 1000000000000)
      | 5 => orderedInterval (3506394655 / 1000000000000) (3506397060 / 1000000000000)
      | 6 => orderedInterval (11063283502 / 1000000000000) (11063283698 / 1000000000000)
      | 7 => orderedInterval (-3593451739 / 1000000000000) (-3593450368 / 1000000000000)
      | _ => orderedInterval (-13395577242 / 1000000000000) (-13395555159 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (20594868690 / 1000000000000) (20594893961 / 1000000000000)
      | 1 => orderedInterval (-4705151209 / 1000000000000) (-4705150709 / 1000000000000)
      | 2 => orderedInterval (470619091 / 1000000000000) (470619119 / 1000000000000)
      | 3 => orderedInterval (33499218014 / 1000000000000) (33499239973 / 1000000000000)
      | 4 => orderedInterval (6942572831 / 1000000000000) (6942573158 / 1000000000000)
      | 5 => orderedInterval (-1296084851 / 1000000000000) (-1296080979 / 1000000000000)
      | 6 => orderedInterval (2709856736 / 1000000000000) (2709856934 / 1000000000000)
      | 7 => orderedInterval (-4142702208 / 1000000000000) (-4142700841 / 1000000000000)
      | _ => orderedInterval (-2248547456 / 1000000000000) (-2248519874 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-13095630992 / 1000000000000) (-13095605805 / 1000000000000)
      | 1 => orderedInterval (12854980337 / 1000000000000) (12854981017 / 1000000000000)
      | 2 => orderedInterval (7717216791 / 1000000000000) (7717216841 / 1000000000000)
      | 3 => orderedInterval (-122512909519 / 1000000000000) (-122512859244 / 1000000000000)
      | 4 => orderedInterval (-8213048946 / 1000000000000) (-8213048439 / 1000000000000)
      | 5 => orderedInterval (-8924682347 / 1000000000000) (-8924676042 / 1000000000000)
      | 6 => orderedInterval (-11823150513 / 1000000000000) (-11823150312 / 1000000000000)
      | 7 => orderedInterval (4704203306 / 1000000000000) (4704204747 / 1000000000000)
      | _ => orderedInterval (28810092922 / 1000000000000) (28810127203 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-21858550869 / 1000000000000) (-21858525582 / 1000000000000)
      | 1 => orderedInterval (10426230947 / 1000000000000) (10426231958 / 1000000000000)
      | 2 => orderedInterval (-6475053578 / 1000000000000) (-6475053486 / 1000000000000)
      | 3 => orderedInterval (-184402784632 / 1000000000000) (-184402669182 / 1000000000000)
      | 4 => orderedInterval (-20837658754 / 1000000000000) (-20837657960 / 1000000000000)
      | 5 => orderedInterval (-3208751222 / 1000000000000) (-3208740758 / 1000000000000)
      | 6 => orderedInterval (-2985746119 / 1000000000000) (-2985745913 / 1000000000000)
      | 7 => orderedInterval (4428656791 / 1000000000000) (4428658347 / 1000000000000)
      | _ => orderedInterval (-16593473715 / 1000000000000) (-16593430872 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-17044788173 / 1000000000000) (-17044736830 / 1000000000000)
    | 1 => orderedInterval (36170236513 / 1000000000000) (36170298012 / 1000000000000)
    | 2 => orderedInterval (51824649638 / 1000000000000) (51824730742 / 1000000000000)
    | 3 => orderedInterval (-110482928961 / 1000000000000) (-110482810034 / 1000000000000)
    | _ => orderedInterval (-241507131151 / 1000000000000) (-241506933448 / 1000000000000)

theorem compactCertificate281_stateChecks0 :
    compactCertificate281.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 50 12 (311 / 2)) (orderedInterval (-45677844957 / 1000000000000) (-45677782448 / 1000000000000), orderedInterval (44952583106 / 1000000000000) (44952645615 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 36 12 (458162384797211 / 4000000000000)) (orderedInterval (59042605235 / 1000000000000) (59042668067 / 1000000000000), orderedInterval (-45776777385 / 1000000000000) (-45776714552 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 59 12 (148160301703163 / 800000000000)) (orderedInterval (-34595124086 / 1000000000000) (-34595124085 / 1000000000000), orderedInterval (-47242063549 / 1000000000000) (-47242063548 / 1000000000000))) = true
  rfl'

theorem compactCertificate281_stateChecks1 :
    compactCertificate281.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 11 12 (133690641210577 / 4000000000000)) (orderedInterval (47736127395 / 1000000000000) (47736128755 / 1000000000000), orderedInterval (-130214666711 / 1000000000000) (-130214665351 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 29 12 (359111867435869 / 4000000000000)) (orderedInterval (43598191263 / 1000000000000) (43598199382 / 1000000000000), orderedInterval (-72286511162 / 1000000000000) (-72286503043 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 78 12 (975058577295273 / 4000000000000)) (orderedInterval (-24262367837 / 1000000000000) (-24262365737 / 1000000000000), orderedInterval (45027059994 / 1000000000000) (45027062094 / 1000000000000))) = true
  rfl'

theorem compactCertificate281_stateChecks2 :
    compactCertificate281.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 57 12 (718223734872049 / 4000000000000)) (orderedInterval (-56868131970 / 1000000000000) (-56868131968 / 1000000000000), orderedInterval (-17491790245 / 1000000000000) (-17491790244 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 98 12 (1230688611434677 / 4000000000000)) (orderedInterval (24968942474 / 1000000000000) (24968942475 / 1000000000000), orderedInterval (37981821495 / 1000000000000) (37981821496 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 72 12 (906519661024543 / 4000000000000)) (orderedInterval (49774497791 / 1000000000000) (49774497792 / 1000000000000), orderedInterval (18099146717 / 1000000000000) (18099146718 / 1000000000000))) = true
  rfl'

theorem compactCertificate281_stateChecks3 :
    compactCertificate281.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 111 12 (1390834282004689 / 4000000000000)) (orderedInterval (9470376516 / 1000000000000) (9470376546 / 1000000000000), orderedInterval (-41741475964 / 1000000000000) (-41741475934 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (802998547113481 / 4000000000000)) (orderedInterval (25628140021 / 1000000000000) (25628140022 / 1000000000000), orderedInterval (50080129795 / 1000000000000) (50080129796 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 113 12 (1424935013131229 / 4000000000000)) (orderedInterval (-38101494447 / 1000000000000) (-38101465498 / 1000000000000), orderedInterval (18366312775 / 1000000000000) (18366341723 / 1000000000000))) = true
  rfl'

theorem compactCertificate281_stateChecks4 :
    compactCertificate281.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 106 12 (1331359126975601 / 4000000000000)) (orderedInterval (25267982557 / 1000000000000) (25267982558 / 1000000000000), orderedInterval (35658275988 / 1000000000000) (35658275989 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 76 12 (950120694087233 / 4000000000000)) (orderedInterval (-22331450054 / 1000000000000) (-22331448809 / 1000000000000), orderedInterval (46753257866 / 1000000000000) (46753259112 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 86 12 (1077335602307607 / 4000000000000)) (orderedInterval (-2824727441 / 1000000000000) (-2824727437 / 1000000000000), orderedInterval (48540872619 / 1000000000000) (48540872624 / 1000000000000))) = true
  rfl'

theorem compactCertificate281_stateChecks5 :
    compactCertificate281.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 72 12 (898170107321383 / 4000000000000)) (orderedInterval (-40605045392 / 1000000000000) (-40604959242 / 1000000000000), orderedInterval (34534794831 / 1000000000000) (34534880981 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 63 12 (793560528585043 / 4000000000000)) (orderedInterval (-53838378122 / 1000000000000) (-53838378121 / 1000000000000), orderedInterval (-17481050172 / 1000000000000) (-17481050171 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 92 12 (230004771691257 / 800000000000)) (orderedInterval (-31576056684 / 1000000000000) (-31576036698 / 1000000000000), orderedInterval (34943831184 / 1000000000000) (34943851171 / 1000000000000))) = true
  rfl'

theorem compactCertificate281_stateChecks6 :
    compactCertificate281.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (636205302985979 / 4000000000000)) (orderedInterval (23776967705 / 1000000000000) (23776968675 / 1000000000000), orderedInterval (-58703031408 / 1000000000000) (-58703030438 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 43 12 (539318281122019 / 4000000000000)) (orderedInterval (-34473540788 / 1000000000000) (-34473540787 / 1000000000000), orderedInterval (-59313341192 / 1000000000000) (-59313341191 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 27 12 (337480338975457 / 4000000000000)) (orderedInterval (-28229962045 / 1000000000000) (-28229962044 / 1000000000000), orderedInterval (-81983401482 / 1000000000000) (-81983401481 / 1000000000000))) = true
  rfl'

theorem compactCertificate281_stateChecks7 :
    compactCertificate281.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 14 12 (181498048709919 / 4000000000000)) (orderedInterval (97485281482 / 1000000000000) (97485310633 / 1000000000000), orderedInterval (-68354522738 / 1000000000000) (-68354493587 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 39 12 (492802508646757 / 4000000000000)) (orderedInterval (-71465892235 / 1000000000000) (-71465892228 / 1000000000000), orderedInterval (-7451197369 / 1000000000000) (-7451197362 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (672879694574789 / 4000000000000)) (orderedInterval (-36808376309 / 1000000000000) (-36808361873 / 1000000000000), orderedInterval (49400349430 / 1000000000000) (49400363867 / 1000000000000))) = true
  rfl'

theorem compactCertificate281_stateChecks8 :
    compactCertificate281.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 23 12 (284519661024543 / 4000000000000)) (orderedInterval (31823227993 / 1000000000000) (31823228980 / 1000000000000), orderedInterval (-89316627574 / 1000000000000) (-89316626587 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 92 12 (1156556626005503 / 4000000000000)) (orderedInterval (36685931149 / 1000000000000) (36685931150 / 1000000000000), orderedInterval (29192638739 / 1000000000000) (29192638740 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (772526226637777 / 4000000000000)) (orderedInterval (-43601462097 / 1000000000000) (-43601367605 / 1000000000000), orderedInterval (37465419296 / 1000000000000) (37465513788 / 1000000000000))) = true
  rfl'

theorem compactCertificate281_states : ∀ j,
    BesselStateValid (compactCertificate281.point j) (compactCertificate281.state j) :=
  compactCertificate281.statesValid_of_checks3 compactCertificate281_stateChecks0
    compactCertificate281_stateChecks1 compactCertificate281_stateChecks2
    compactCertificate281_stateChecks3 compactCertificate281_stateChecks4
    compactCertificate281_stateChecks5 compactCertificate281_stateChecks6
    compactCertificate281_stateChecks7 compactCertificate281_stateChecks8

theorem compactCertificate281_chunkChecks0_0 :
    compactCertificate281.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (311 / 2) 0 (IntervalRat.scale (311 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-45677844957 / 1000000000000) (-45677782448 / 1000000000000), orderedInterval (44952583106 / 1000000000000) (44952645615 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (458162384797211 / 4000000000000) 0 (IntervalRat.scale (311 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (59042605235 / 1000000000000) (59042668067 / 1000000000000), orderedInterval (-45776777385 / 1000000000000) (-45776714552 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (148160301703163 / 800000000000) 0 (IntervalRat.scale (311 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-34595124086 / 1000000000000) (-34595124085 / 1000000000000), orderedInterval (-47242063549 / 1000000000000) (-47242063548 / 1000000000000)))) (orderedInterval (-19585017484 / 1000000000000) (-19584992111 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (133690641210577 / 4000000000000) 0 (IntervalRat.scale (311 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (47736127395 / 1000000000000) (47736128755 / 1000000000000), orderedInterval (-130214666711 / 1000000000000) (-130214665351 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (359111867435869 / 4000000000000) 0 (IntervalRat.scale (311 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (43598191263 / 1000000000000) (43598199382 / 1000000000000), orderedInterval (-72286511162 / 1000000000000) (-72286503043 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (975058577295273 / 4000000000000) 0 (IntervalRat.scale (311 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-24262367837 / 1000000000000) (-24262365737 / 1000000000000), orderedInterval (45027059994 / 1000000000000) (45027062094 / 1000000000000)))) (orderedInterval (2798745794 / 1000000000000) (2798746274 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (718223734872049 / 4000000000000) 0 (IntervalRat.scale (311 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-56868131970 / 1000000000000) (-56868131968 / 1000000000000), orderedInterval (-17491790245 / 1000000000000) (-17491790244 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1230688611434677 / 4000000000000) 0 (IntervalRat.scale (311 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (24968942474 / 1000000000000) (24968942475 / 1000000000000), orderedInterval (37981821495 / 1000000000000) (37981821496 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (906519661024543 / 4000000000000) 0 (IntervalRat.scale (311 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (49774497791 / 1000000000000) (49774497792 / 1000000000000), orderedInterval (18099146717 / 1000000000000) (18099146718 / 1000000000000)))) (orderedInterval (432809315 / 1000000000000) (432809325 / 1000000000000))) = true
  rfl'

theorem compactCertificate281_chunkChecks0_1 :
    compactCertificate281.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1390834282004689 / 4000000000000) 0 (IntervalRat.scale (311 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (9470376516 / 1000000000000) (9470376546 / 1000000000000), orderedInterval (-41741475964 / 1000000000000) (-41741475934 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (802998547113481 / 4000000000000) 0 (IntervalRat.scale (311 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (25628140021 / 1000000000000) (25628140022 / 1000000000000), orderedInterval (50080129795 / 1000000000000) (50080129796 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1424935013131229 / 4000000000000) 0 (IntervalRat.scale (311 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-38101494447 / 1000000000000) (-38101465498 / 1000000000000), orderedInterval (18366312775 / 1000000000000) (18366341723 / 1000000000000)))) (orderedInterval (-5200289246 / 1000000000000) (-5200285063 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1331359126975601 / 4000000000000) 0 (IntervalRat.scale (311 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (25267982557 / 1000000000000) (25267982558 / 1000000000000), orderedInterval (35658275988 / 1000000000000) (35658275989 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (950120694087233 / 4000000000000) 0 (IntervalRat.scale (311 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-22331450054 / 1000000000000) (-22331448809 / 1000000000000), orderedInterval (46753257866 / 1000000000000) (46753259112 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (1077335602307607 / 4000000000000) 0 (IntervalRat.scale (311 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-2824727441 / 1000000000000) (-2824727437 / 1000000000000), orderedInterval (48540872619 / 1000000000000) (48540872624 / 1000000000000)))) (orderedInterval (-2553596243 / 1000000000000) (-2553596106 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (898170107321383 / 4000000000000) 0 (IntervalRat.scale (311 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-40605045392 / 1000000000000) (-40604959242 / 1000000000000), orderedInterval (34534794831 / 1000000000000) (34534880981 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (793560528585043 / 4000000000000) 0 (IntervalRat.scale (311 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-53838378122 / 1000000000000) (-53838378121 / 1000000000000), orderedInterval (-17481050172 / 1000000000000) (-17481050171 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (230004771691257 / 800000000000) 0 (IntervalRat.scale (311 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-31576056684 / 1000000000000) (-31576036698 / 1000000000000), orderedInterval (34943831184 / 1000000000000) (34943851171 / 1000000000000)))) (orderedInterval (1803626026 / 1000000000000) (1803627548 / 1000000000000))) = true
  rfl'

theorem compactCertificate281_chunkChecks0_2 :
    compactCertificate281.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (636205302985979 / 4000000000000) 0 (IntervalRat.scale (311 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (23776967705 / 1000000000000) (23776968675 / 1000000000000), orderedInterval (-58703031408 / 1000000000000) (-58703030438 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (539318281122019 / 4000000000000) 0 (IntervalRat.scale (311 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-34473540788 / 1000000000000) (-34473540787 / 1000000000000), orderedInterval (-59313341192 / 1000000000000) (-59313341191 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (337480338975457 / 4000000000000) 0 (IntervalRat.scale (311 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-28229962045 / 1000000000000) (-28229962044 / 1000000000000), orderedInterval (-81983401482 / 1000000000000) (-81983401481 / 1000000000000)))) (orderedInterval (-2769590778 / 1000000000000) (-2769590583 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (181498048709919 / 4000000000000) 0 (IntervalRat.scale (311 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (97485281482 / 1000000000000) (97485310633 / 1000000000000), orderedInterval (-68354522738 / 1000000000000) (-68354493587 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (492802508646757 / 4000000000000) 0 (IntervalRat.scale (311 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-71465892235 / 1000000000000) (-71465892228 / 1000000000000), orderedInterval (-7451197369 / 1000000000000) (-7451197362 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (672879694574789 / 4000000000000) 0 (IntervalRat.scale (311 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-36808376309 / 1000000000000) (-36808361873 / 1000000000000), orderedInterval (49400349430 / 1000000000000) (49400363867 / 1000000000000)))) (orderedInterval (2642210419 / 1000000000000) (2642212083 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (284519661024543 / 4000000000000) 0 (IntervalRat.scale (311 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (31823227993 / 1000000000000) (31823228980 / 1000000000000), orderedInterval (-89316627574 / 1000000000000) (-89316626587 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1156556626005503 / 4000000000000) 0 (IntervalRat.scale (311 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (36685931149 / 1000000000000) (36685931150 / 1000000000000), orderedInterval (29192638739 / 1000000000000) (29192638740 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (772526226637777 / 4000000000000) 0 (IntervalRat.scale (311 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-43601462097 / 1000000000000) (-43601367605 / 1000000000000), orderedInterval (37465419296 / 1000000000000) (37465513788 / 1000000000000)))) (orderedInterval (5386314024 / 1000000000000) (5386331803 / 1000000000000))) = true
  rfl'

theorem compactCertificate281_chunkChecks0 :
    compactCertificate281.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate281.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate281_chunkChecks0_0
    compactCertificate281_chunkChecks0_1 compactCertificate281_chunkChecks0_2

theorem compactCertificate281_chunkChecks1_0 :
    compactCertificate281.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (311 / 2) 1 (IntervalRat.scale (311 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-45677844957 / 1000000000000) (-45677782448 / 1000000000000), orderedInterval (44952583106 / 1000000000000) (44952645615 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (458162384797211 / 4000000000000) 1 (IntervalRat.scale (311 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (59042605235 / 1000000000000) (59042668067 / 1000000000000), orderedInterval (-45776777385 / 1000000000000) (-45776714552 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (148160301703163 / 800000000000) 1 (IntervalRat.scale (311 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-34595124086 / 1000000000000) (-34595124085 / 1000000000000), orderedInterval (-47242063549 / 1000000000000) (-47242063548 / 1000000000000)))) (orderedInterval (14201725304 / 1000000000000) (14201750524 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (133690641210577 / 4000000000000) 1 (IntervalRat.scale (311 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (47736127395 / 1000000000000) (47736128755 / 1000000000000), orderedInterval (-130214666711 / 1000000000000) (-130214665351 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (359111867435869 / 4000000000000) 1 (IntervalRat.scale (311 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (43598191263 / 1000000000000) (43598199382 / 1000000000000), orderedInterval (-72286511162 / 1000000000000) (-72286503043 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (975058577295273 / 4000000000000) 1 (IntervalRat.scale (311 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-24262367837 / 1000000000000) (-24262365737 / 1000000000000), orderedInterval (45027059994 / 1000000000000) (45027062094 / 1000000000000)))) (orderedInterval (-6238035257 / 1000000000000) (-6238034827 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (718223734872049 / 4000000000000) 1 (IntervalRat.scale (311 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-56868131970 / 1000000000000) (-56868131968 / 1000000000000), orderedInterval (-17491790245 / 1000000000000) (-17491790244 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1230688611434677 / 4000000000000) 1 (IntervalRat.scale (311 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (24968942474 / 1000000000000) (24968942475 / 1000000000000), orderedInterval (37981821495 / 1000000000000) (37981821496 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (906519661024543 / 4000000000000) 1 (IntervalRat.scale (311 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (49774497791 / 1000000000000) (49774497792 / 1000000000000), orderedInterval (18099146717 / 1000000000000) (18099146718 / 1000000000000)))) (orderedInterval (-1680442500 / 1000000000000) (-1680442484 / 1000000000000))) = true
  rfl'

theorem compactCertificate281_chunkChecks1_1 :
    compactCertificate281.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1390834282004689 / 4000000000000) 1 (IntervalRat.scale (311 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (9470376516 / 1000000000000) (9470376546 / 1000000000000), orderedInterval (-41741475964 / 1000000000000) (-41741475934 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (802998547113481 / 4000000000000) 1 (IntervalRat.scale (311 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (25628140021 / 1000000000000) (25628140022 / 1000000000000), orderedInterval (50080129795 / 1000000000000) (50080129796 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1424935013131229 / 4000000000000) 1 (IntervalRat.scale (311 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-38101494447 / 1000000000000) (-38101465498 / 1000000000000), orderedInterval (18366312775 / 1000000000000) (18366341723 / 1000000000000)))) (orderedInterval (27356330139 / 1000000000000) (27356339706 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1331359126975601 / 4000000000000) 1 (IntervalRat.scale (311 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (25267982557 / 1000000000000) (25267982558 / 1000000000000), orderedInterval (35658275988 / 1000000000000) (35658275989 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (950120694087233 / 4000000000000) 1 (IntervalRat.scale (311 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-22331450054 / 1000000000000) (-22331448809 / 1000000000000), orderedInterval (46753257866 / 1000000000000) (46753259112 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (1077335602307607 / 4000000000000) 1 (IntervalRat.scale (311 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-2824727441 / 1000000000000) (-2824727437 / 1000000000000), orderedInterval (48540872619 / 1000000000000) (48540872624 / 1000000000000)))) (orderedInterval (4950009651 / 1000000000000) (4950009862 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (898170107321383 / 4000000000000) 1 (IntervalRat.scale (311 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-40605045392 / 1000000000000) (-40604959242 / 1000000000000), orderedInterval (34534794831 / 1000000000000) (34534880981 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (793560528585043 / 4000000000000) 1 (IntervalRat.scale (311 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-53838378122 / 1000000000000) (-53838378121 / 1000000000000), orderedInterval (-17481050172 / 1000000000000) (-17481050171 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (230004771691257 / 800000000000) 1 (IntervalRat.scale (311 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-31576056684 / 1000000000000) (-31576036698 / 1000000000000), orderedInterval (34943831184 / 1000000000000) (34943851171 / 1000000000000)))) (orderedInterval (3506394655 / 1000000000000) (3506397060 / 1000000000000))) = true
  rfl'

theorem compactCertificate281_chunkChecks1_2 :
    compactCertificate281.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (636205302985979 / 4000000000000) 1 (IntervalRat.scale (311 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (23776967705 / 1000000000000) (23776968675 / 1000000000000), orderedInterval (-58703031408 / 1000000000000) (-58703030438 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (539318281122019 / 4000000000000) 1 (IntervalRat.scale (311 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-34473540788 / 1000000000000) (-34473540787 / 1000000000000), orderedInterval (-59313341192 / 1000000000000) (-59313341191 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (337480338975457 / 4000000000000) 1 (IntervalRat.scale (311 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-28229962045 / 1000000000000) (-28229962044 / 1000000000000), orderedInterval (-81983401482 / 1000000000000) (-81983401481 / 1000000000000)))) (orderedInterval (11063283502 / 1000000000000) (11063283698 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (181498048709919 / 4000000000000) 1 (IntervalRat.scale (311 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (97485281482 / 1000000000000) (97485310633 / 1000000000000), orderedInterval (-68354522738 / 1000000000000) (-68354493587 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (492802508646757 / 4000000000000) 1 (IntervalRat.scale (311 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-71465892235 / 1000000000000) (-71465892228 / 1000000000000), orderedInterval (-7451197369 / 1000000000000) (-7451197362 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (672879694574789 / 4000000000000) 1 (IntervalRat.scale (311 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-36808376309 / 1000000000000) (-36808361873 / 1000000000000), orderedInterval (49400349430 / 1000000000000) (49400363867 / 1000000000000)))) (orderedInterval (-3593451739 / 1000000000000) (-3593450368 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (284519661024543 / 4000000000000) 1 (IntervalRat.scale (311 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (31823227993 / 1000000000000) (31823228980 / 1000000000000), orderedInterval (-89316627574 / 1000000000000) (-89316626587 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1156556626005503 / 4000000000000) 1 (IntervalRat.scale (311 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (36685931149 / 1000000000000) (36685931150 / 1000000000000), orderedInterval (29192638739 / 1000000000000) (29192638740 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (772526226637777 / 4000000000000) 1 (IntervalRat.scale (311 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-43601462097 / 1000000000000) (-43601367605 / 1000000000000), orderedInterval (37465419296 / 1000000000000) (37465513788 / 1000000000000)))) (orderedInterval (-13395577242 / 1000000000000) (-13395555159 / 1000000000000))) = true
  rfl'

theorem compactCertificate281_chunkChecks1 :
    compactCertificate281.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate281.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate281_chunkChecks1_0
    compactCertificate281_chunkChecks1_1 compactCertificate281_chunkChecks1_2

theorem compactCertificate281_chunkChecks2_0 :
    compactCertificate281.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (311 / 2) 2 (IntervalRat.scale (311 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-45677844957 / 1000000000000) (-45677782448 / 1000000000000), orderedInterval (44952583106 / 1000000000000) (44952645615 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (458162384797211 / 4000000000000) 2 (IntervalRat.scale (311 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (59042605235 / 1000000000000) (59042668067 / 1000000000000), orderedInterval (-45776777385 / 1000000000000) (-45776714552 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (148160301703163 / 800000000000) 2 (IntervalRat.scale (311 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-34595124086 / 1000000000000) (-34595124085 / 1000000000000), orderedInterval (-47242063549 / 1000000000000) (-47242063548 / 1000000000000)))) (orderedInterval (20594868690 / 1000000000000) (20594893961 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (133690641210577 / 4000000000000) 2 (IntervalRat.scale (311 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (47736127395 / 1000000000000) (47736128755 / 1000000000000), orderedInterval (-130214666711 / 1000000000000) (-130214665351 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (359111867435869 / 4000000000000) 2 (IntervalRat.scale (311 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (43598191263 / 1000000000000) (43598199382 / 1000000000000), orderedInterval (-72286511162 / 1000000000000) (-72286503043 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (975058577295273 / 4000000000000) 2 (IntervalRat.scale (311 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-24262367837 / 1000000000000) (-24262365737 / 1000000000000), orderedInterval (45027059994 / 1000000000000) (45027062094 / 1000000000000)))) (orderedInterval (-4705151209 / 1000000000000) (-4705150709 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (718223734872049 / 4000000000000) 2 (IntervalRat.scale (311 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-56868131970 / 1000000000000) (-56868131968 / 1000000000000), orderedInterval (-17491790245 / 1000000000000) (-17491790244 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1230688611434677 / 4000000000000) 2 (IntervalRat.scale (311 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (24968942474 / 1000000000000) (24968942475 / 1000000000000), orderedInterval (37981821495 / 1000000000000) (37981821496 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (906519661024543 / 4000000000000) 2 (IntervalRat.scale (311 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (49774497791 / 1000000000000) (49774497792 / 1000000000000), orderedInterval (18099146717 / 1000000000000) (18099146718 / 1000000000000)))) (orderedInterval (470619091 / 1000000000000) (470619119 / 1000000000000))) = true
  rfl'

theorem compactCertificate281_chunkChecks2_1 :
    compactCertificate281.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1390834282004689 / 4000000000000) 2 (IntervalRat.scale (311 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (9470376516 / 1000000000000) (9470376546 / 1000000000000), orderedInterval (-41741475964 / 1000000000000) (-41741475934 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (802998547113481 / 4000000000000) 2 (IntervalRat.scale (311 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (25628140021 / 1000000000000) (25628140022 / 1000000000000), orderedInterval (50080129795 / 1000000000000) (50080129796 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1424935013131229 / 4000000000000) 2 (IntervalRat.scale (311 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-38101494447 / 1000000000000) (-38101465498 / 1000000000000), orderedInterval (18366312775 / 1000000000000) (18366341723 / 1000000000000)))) (orderedInterval (33499218014 / 1000000000000) (33499239973 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1331359126975601 / 4000000000000) 2 (IntervalRat.scale (311 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (25267982557 / 1000000000000) (25267982558 / 1000000000000), orderedInterval (35658275988 / 1000000000000) (35658275989 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (950120694087233 / 4000000000000) 2 (IntervalRat.scale (311 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-22331450054 / 1000000000000) (-22331448809 / 1000000000000), orderedInterval (46753257866 / 1000000000000) (46753259112 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (1077335602307607 / 4000000000000) 2 (IntervalRat.scale (311 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-2824727441 / 1000000000000) (-2824727437 / 1000000000000), orderedInterval (48540872619 / 1000000000000) (48540872624 / 1000000000000)))) (orderedInterval (6942572831 / 1000000000000) (6942573158 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (898170107321383 / 4000000000000) 2 (IntervalRat.scale (311 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-40605045392 / 1000000000000) (-40604959242 / 1000000000000), orderedInterval (34534794831 / 1000000000000) (34534880981 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (793560528585043 / 4000000000000) 2 (IntervalRat.scale (311 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-53838378122 / 1000000000000) (-53838378121 / 1000000000000), orderedInterval (-17481050172 / 1000000000000) (-17481050171 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (230004771691257 / 800000000000) 2 (IntervalRat.scale (311 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-31576056684 / 1000000000000) (-31576036698 / 1000000000000), orderedInterval (34943831184 / 1000000000000) (34943851171 / 1000000000000)))) (orderedInterval (-1296084851 / 1000000000000) (-1296080979 / 1000000000000))) = true
  rfl'

theorem compactCertificate281_chunkChecks2_2 :
    compactCertificate281.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (636205302985979 / 4000000000000) 2 (IntervalRat.scale (311 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (23776967705 / 1000000000000) (23776968675 / 1000000000000), orderedInterval (-58703031408 / 1000000000000) (-58703030438 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (539318281122019 / 4000000000000) 2 (IntervalRat.scale (311 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-34473540788 / 1000000000000) (-34473540787 / 1000000000000), orderedInterval (-59313341192 / 1000000000000) (-59313341191 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (337480338975457 / 4000000000000) 2 (IntervalRat.scale (311 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-28229962045 / 1000000000000) (-28229962044 / 1000000000000), orderedInterval (-81983401482 / 1000000000000) (-81983401481 / 1000000000000)))) (orderedInterval (2709856736 / 1000000000000) (2709856934 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (181498048709919 / 4000000000000) 2 (IntervalRat.scale (311 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (97485281482 / 1000000000000) (97485310633 / 1000000000000), orderedInterval (-68354522738 / 1000000000000) (-68354493587 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (492802508646757 / 4000000000000) 2 (IntervalRat.scale (311 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-71465892235 / 1000000000000) (-71465892228 / 1000000000000), orderedInterval (-7451197369 / 1000000000000) (-7451197362 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (672879694574789 / 4000000000000) 2 (IntervalRat.scale (311 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-36808376309 / 1000000000000) (-36808361873 / 1000000000000), orderedInterval (49400349430 / 1000000000000) (49400363867 / 1000000000000)))) (orderedInterval (-4142702208 / 1000000000000) (-4142700841 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (284519661024543 / 4000000000000) 2 (IntervalRat.scale (311 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (31823227993 / 1000000000000) (31823228980 / 1000000000000), orderedInterval (-89316627574 / 1000000000000) (-89316626587 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1156556626005503 / 4000000000000) 2 (IntervalRat.scale (311 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (36685931149 / 1000000000000) (36685931150 / 1000000000000), orderedInterval (29192638739 / 1000000000000) (29192638740 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (772526226637777 / 4000000000000) 2 (IntervalRat.scale (311 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-43601462097 / 1000000000000) (-43601367605 / 1000000000000), orderedInterval (37465419296 / 1000000000000) (37465513788 / 1000000000000)))) (orderedInterval (-2248547456 / 1000000000000) (-2248519874 / 1000000000000))) = true
  rfl'

theorem compactCertificate281_chunkChecks2 :
    compactCertificate281.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate281.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate281_chunkChecks2_0
    compactCertificate281_chunkChecks2_1 compactCertificate281_chunkChecks2_2

theorem compactCertificate281_chunkChecks3_0 :
    compactCertificate281.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (311 / 2) 3 (IntervalRat.scale (311 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-45677844957 / 1000000000000) (-45677782448 / 1000000000000), orderedInterval (44952583106 / 1000000000000) (44952645615 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (458162384797211 / 4000000000000) 3 (IntervalRat.scale (311 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (59042605235 / 1000000000000) (59042668067 / 1000000000000), orderedInterval (-45776777385 / 1000000000000) (-45776714552 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (148160301703163 / 800000000000) 3 (IntervalRat.scale (311 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-34595124086 / 1000000000000) (-34595124085 / 1000000000000), orderedInterval (-47242063549 / 1000000000000) (-47242063548 / 1000000000000)))) (orderedInterval (-13095630992 / 1000000000000) (-13095605805 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (133690641210577 / 4000000000000) 3 (IntervalRat.scale (311 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (47736127395 / 1000000000000) (47736128755 / 1000000000000), orderedInterval (-130214666711 / 1000000000000) (-130214665351 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (359111867435869 / 4000000000000) 3 (IntervalRat.scale (311 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (43598191263 / 1000000000000) (43598199382 / 1000000000000), orderedInterval (-72286511162 / 1000000000000) (-72286503043 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (975058577295273 / 4000000000000) 3 (IntervalRat.scale (311 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-24262367837 / 1000000000000) (-24262365737 / 1000000000000), orderedInterval (45027059994 / 1000000000000) (45027062094 / 1000000000000)))) (orderedInterval (12854980337 / 1000000000000) (12854981017 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (718223734872049 / 4000000000000) 3 (IntervalRat.scale (311 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-56868131970 / 1000000000000) (-56868131968 / 1000000000000), orderedInterval (-17491790245 / 1000000000000) (-17491790244 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1230688611434677 / 4000000000000) 3 (IntervalRat.scale (311 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (24968942474 / 1000000000000) (24968942475 / 1000000000000), orderedInterval (37981821495 / 1000000000000) (37981821496 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (906519661024543 / 4000000000000) 3 (IntervalRat.scale (311 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (49774497791 / 1000000000000) (49774497792 / 1000000000000), orderedInterval (18099146717 / 1000000000000) (18099146718 / 1000000000000)))) (orderedInterval (7717216791 / 1000000000000) (7717216841 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate281_chunkChecks3_1 :
    compactCertificate281.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1390834282004689 / 4000000000000) 3 (IntervalRat.scale (311 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (9470376516 / 1000000000000) (9470376546 / 1000000000000), orderedInterval (-41741475964 / 1000000000000) (-41741475934 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (802998547113481 / 4000000000000) 3 (IntervalRat.scale (311 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (25628140021 / 1000000000000) (25628140022 / 1000000000000), orderedInterval (50080129795 / 1000000000000) (50080129796 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1424935013131229 / 4000000000000) 3 (IntervalRat.scale (311 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-38101494447 / 1000000000000) (-38101465498 / 1000000000000), orderedInterval (18366312775 / 1000000000000) (18366341723 / 1000000000000)))) (orderedInterval (-122512909519 / 1000000000000) (-122512859244 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1331359126975601 / 4000000000000) 3 (IntervalRat.scale (311 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (25267982557 / 1000000000000) (25267982558 / 1000000000000), orderedInterval (35658275988 / 1000000000000) (35658275989 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (950120694087233 / 4000000000000) 3 (IntervalRat.scale (311 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-22331450054 / 1000000000000) (-22331448809 / 1000000000000), orderedInterval (46753257866 / 1000000000000) (46753259112 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (1077335602307607 / 4000000000000) 3 (IntervalRat.scale (311 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-2824727441 / 1000000000000) (-2824727437 / 1000000000000), orderedInterval (48540872619 / 1000000000000) (48540872624 / 1000000000000)))) (orderedInterval (-8213048946 / 1000000000000) (-8213048439 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (898170107321383 / 4000000000000) 3 (IntervalRat.scale (311 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-40605045392 / 1000000000000) (-40604959242 / 1000000000000), orderedInterval (34534794831 / 1000000000000) (34534880981 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (793560528585043 / 4000000000000) 3 (IntervalRat.scale (311 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-53838378122 / 1000000000000) (-53838378121 / 1000000000000), orderedInterval (-17481050172 / 1000000000000) (-17481050171 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (230004771691257 / 800000000000) 3 (IntervalRat.scale (311 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-31576056684 / 1000000000000) (-31576036698 / 1000000000000), orderedInterval (34943831184 / 1000000000000) (34943851171 / 1000000000000)))) (orderedInterval (-8924682347 / 1000000000000) (-8924676042 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate281_chunkChecks3_2 :
    compactCertificate281.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (636205302985979 / 4000000000000) 3 (IntervalRat.scale (311 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (23776967705 / 1000000000000) (23776968675 / 1000000000000), orderedInterval (-58703031408 / 1000000000000) (-58703030438 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (539318281122019 / 4000000000000) 3 (IntervalRat.scale (311 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-34473540788 / 1000000000000) (-34473540787 / 1000000000000), orderedInterval (-59313341192 / 1000000000000) (-59313341191 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (337480338975457 / 4000000000000) 3 (IntervalRat.scale (311 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-28229962045 / 1000000000000) (-28229962044 / 1000000000000), orderedInterval (-81983401482 / 1000000000000) (-81983401481 / 1000000000000)))) (orderedInterval (-11823150513 / 1000000000000) (-11823150312 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (181498048709919 / 4000000000000) 3 (IntervalRat.scale (311 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (97485281482 / 1000000000000) (97485310633 / 1000000000000), orderedInterval (-68354522738 / 1000000000000) (-68354493587 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (492802508646757 / 4000000000000) 3 (IntervalRat.scale (311 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-71465892235 / 1000000000000) (-71465892228 / 1000000000000), orderedInterval (-7451197369 / 1000000000000) (-7451197362 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (672879694574789 / 4000000000000) 3 (IntervalRat.scale (311 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-36808376309 / 1000000000000) (-36808361873 / 1000000000000), orderedInterval (49400349430 / 1000000000000) (49400363867 / 1000000000000)))) (orderedInterval (4704203306 / 1000000000000) (4704204747 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (284519661024543 / 4000000000000) 3 (IntervalRat.scale (311 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (31823227993 / 1000000000000) (31823228980 / 1000000000000), orderedInterval (-89316627574 / 1000000000000) (-89316626587 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1156556626005503 / 4000000000000) 3 (IntervalRat.scale (311 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (36685931149 / 1000000000000) (36685931150 / 1000000000000), orderedInterval (29192638739 / 1000000000000) (29192638740 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (772526226637777 / 4000000000000) 3 (IntervalRat.scale (311 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-43601462097 / 1000000000000) (-43601367605 / 1000000000000), orderedInterval (37465419296 / 1000000000000) (37465513788 / 1000000000000)))) (orderedInterval (28810092922 / 1000000000000) (28810127203 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate281_chunkChecks3 :
    compactCertificate281.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate281.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate281_chunkChecks3_0
    compactCertificate281_chunkChecks3_1 compactCertificate281_chunkChecks3_2

theorem compactCertificate281_chunkChecks4_0 :
    compactCertificate281.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (311 / 2) 4 (IntervalRat.scale (311 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-45677844957 / 1000000000000) (-45677782448 / 1000000000000), orderedInterval (44952583106 / 1000000000000) (44952645615 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (458162384797211 / 4000000000000) 4 (IntervalRat.scale (311 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (59042605235 / 1000000000000) (59042668067 / 1000000000000), orderedInterval (-45776777385 / 1000000000000) (-45776714552 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (148160301703163 / 800000000000) 4 (IntervalRat.scale (311 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-34595124086 / 1000000000000) (-34595124085 / 1000000000000), orderedInterval (-47242063549 / 1000000000000) (-47242063548 / 1000000000000)))) (orderedInterval (-21858550869 / 1000000000000) (-21858525582 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (133690641210577 / 4000000000000) 4 (IntervalRat.scale (311 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (47736127395 / 1000000000000) (47736128755 / 1000000000000), orderedInterval (-130214666711 / 1000000000000) (-130214665351 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (359111867435869 / 4000000000000) 4 (IntervalRat.scale (311 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (43598191263 / 1000000000000) (43598199382 / 1000000000000), orderedInterval (-72286511162 / 1000000000000) (-72286503043 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (975058577295273 / 4000000000000) 4 (IntervalRat.scale (311 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-24262367837 / 1000000000000) (-24262365737 / 1000000000000), orderedInterval (45027059994 / 1000000000000) (45027062094 / 1000000000000)))) (orderedInterval (10426230947 / 1000000000000) (10426231958 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (718223734872049 / 4000000000000) 4 (IntervalRat.scale (311 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-56868131970 / 1000000000000) (-56868131968 / 1000000000000), orderedInterval (-17491790245 / 1000000000000) (-17491790244 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1230688611434677 / 4000000000000) 4 (IntervalRat.scale (311 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (24968942474 / 1000000000000) (24968942475 / 1000000000000), orderedInterval (37981821495 / 1000000000000) (37981821496 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (906519661024543 / 4000000000000) 4 (IntervalRat.scale (311 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (49774497791 / 1000000000000) (49774497792 / 1000000000000), orderedInterval (18099146717 / 1000000000000) (18099146718 / 1000000000000)))) (orderedInterval (-6475053578 / 1000000000000) (-6475053486 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate281_chunkChecks4_1 :
    compactCertificate281.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1390834282004689 / 4000000000000) 4 (IntervalRat.scale (311 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (9470376516 / 1000000000000) (9470376546 / 1000000000000), orderedInterval (-41741475964 / 1000000000000) (-41741475934 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (802998547113481 / 4000000000000) 4 (IntervalRat.scale (311 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (25628140021 / 1000000000000) (25628140022 / 1000000000000), orderedInterval (50080129795 / 1000000000000) (50080129796 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1424935013131229 / 4000000000000) 4 (IntervalRat.scale (311 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-38101494447 / 1000000000000) (-38101465498 / 1000000000000), orderedInterval (18366312775 / 1000000000000) (18366341723 / 1000000000000)))) (orderedInterval (-184402784632 / 1000000000000) (-184402669182 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1331359126975601 / 4000000000000) 4 (IntervalRat.scale (311 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (25267982557 / 1000000000000) (25267982558 / 1000000000000), orderedInterval (35658275988 / 1000000000000) (35658275989 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (950120694087233 / 4000000000000) 4 (IntervalRat.scale (311 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-22331450054 / 1000000000000) (-22331448809 / 1000000000000), orderedInterval (46753257866 / 1000000000000) (46753259112 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (1077335602307607 / 4000000000000) 4 (IntervalRat.scale (311 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-2824727441 / 1000000000000) (-2824727437 / 1000000000000), orderedInterval (48540872619 / 1000000000000) (48540872624 / 1000000000000)))) (orderedInterval (-20837658754 / 1000000000000) (-20837657960 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (898170107321383 / 4000000000000) 4 (IntervalRat.scale (311 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-40605045392 / 1000000000000) (-40604959242 / 1000000000000), orderedInterval (34534794831 / 1000000000000) (34534880981 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (793560528585043 / 4000000000000) 4 (IntervalRat.scale (311 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-53838378122 / 1000000000000) (-53838378121 / 1000000000000), orderedInterval (-17481050172 / 1000000000000) (-17481050171 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (230004771691257 / 800000000000) 4 (IntervalRat.scale (311 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-31576056684 / 1000000000000) (-31576036698 / 1000000000000), orderedInterval (34943831184 / 1000000000000) (34943851171 / 1000000000000)))) (orderedInterval (-3208751222 / 1000000000000) (-3208740758 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate281_chunkChecks4_2 :
    compactCertificate281.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (636205302985979 / 4000000000000) 4 (IntervalRat.scale (311 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (23776967705 / 1000000000000) (23776968675 / 1000000000000), orderedInterval (-58703031408 / 1000000000000) (-58703030438 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (539318281122019 / 4000000000000) 4 (IntervalRat.scale (311 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-34473540788 / 1000000000000) (-34473540787 / 1000000000000), orderedInterval (-59313341192 / 1000000000000) (-59313341191 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (337480338975457 / 4000000000000) 4 (IntervalRat.scale (311 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-28229962045 / 1000000000000) (-28229962044 / 1000000000000), orderedInterval (-81983401482 / 1000000000000) (-81983401481 / 1000000000000)))) (orderedInterval (-2985746119 / 1000000000000) (-2985745913 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (181498048709919 / 4000000000000) 4 (IntervalRat.scale (311 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (97485281482 / 1000000000000) (97485310633 / 1000000000000), orderedInterval (-68354522738 / 1000000000000) (-68354493587 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (492802508646757 / 4000000000000) 4 (IntervalRat.scale (311 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-71465892235 / 1000000000000) (-71465892228 / 1000000000000), orderedInterval (-7451197369 / 1000000000000) (-7451197362 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (672879694574789 / 4000000000000) 4 (IntervalRat.scale (311 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-36808376309 / 1000000000000) (-36808361873 / 1000000000000), orderedInterval (49400349430 / 1000000000000) (49400363867 / 1000000000000)))) (orderedInterval (4428656791 / 1000000000000) (4428658347 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (284519661024543 / 4000000000000) 4 (IntervalRat.scale (311 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (31823227993 / 1000000000000) (31823228980 / 1000000000000), orderedInterval (-89316627574 / 1000000000000) (-89316626587 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1156556626005503 / 4000000000000) 4 (IntervalRat.scale (311 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (36685931149 / 1000000000000) (36685931150 / 1000000000000), orderedInterval (29192638739 / 1000000000000) (29192638740 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (772526226637777 / 4000000000000) 4 (IntervalRat.scale (311 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-43601462097 / 1000000000000) (-43601367605 / 1000000000000), orderedInterval (37465419296 / 1000000000000) (37465513788 / 1000000000000)))) (orderedInterval (-16593473715 / 1000000000000) (-16593430872 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate281_chunkChecks4 :
    compactCertificate281.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate281.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate281_chunkChecks4_0
    compactCertificate281_chunkChecks4_1 compactCertificate281_chunkChecks4_2

theorem compactCertificate281_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate281.chunkCheck r b = true :=
  compactCertificate281.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate281_chunkChecks0
    · exact compactCertificate281_chunkChecks1
    · exact compactCertificate281_chunkChecks2
    · exact compactCertificate281_chunkChecks3
    · exact compactCertificate281_chunkChecks4)

theorem compactCertificate281_coefficient0 :
    compactCertificate281.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate281_coefficient1 :
    compactCertificate281.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate281_coefficient2 :
    compactCertificate281.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate281_coefficient3 :
    compactCertificate281.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate281_coefficient4 :
    compactCertificate281.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate281_coefficients : ∀ r : Fin 5,
    compactCertificate281.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate281_coefficient0
  · exact compactCertificate281_coefficient1
  · exact compactCertificate281_coefficient2
  · exact compactCertificate281_coefficient3
  · exact compactCertificate281_coefficient4

theorem compactCertificate281_lower : (1 : ℚ) ≤ compactCertificate281.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate281, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate281_proves {t : ℝ} (ht : t ∈ compactCertificate281.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate281.proves compactCertificate281_states compactCertificate281_chunks
    compactCertificate281_coefficients compactCertificate281_lower ht

end Erdos232
