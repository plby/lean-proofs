/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate457 : CompactCertificate where
  left := 328
  right := 329
  center := 657 / 2
  grid := fun i =>
    match i.val with
    | 0 => 105
    | 1 => 77
    | 2 => 125
    | 3 => 22
    | 4 => 60
    | 5 => 164
    | 6 => 121
    | 7 => 207
    | 8 => 152
    | 9 => 234
    | 10 => 135
    | 11 => 240
    | 12 => 224
    | 13 => 160
    | 14 => 181
    | 15 => 151
    | 16 => 133
    | 17 => 193
    | 18 => 107
    | 19 => 91
    | 20 => 57
    | 21 => 31
    | 22 => 83
    | 23 => 113
    | 24 => 48
    | 25 => 195
    | _ => 130
  point := fun i =>
    match i.val with
    | 0 => 657 / 2
    | 1 => 967886452770957 / 4000000000000
    | 2 => 312994592343981 / 800000000000
    | 3 => 282426852975399 / 4000000000000
    | 4 => 758638253715003 / 4000000000000
    | 5 => 2059850434993551 / 4000000000000
    | 6 => 1517276507430663 / 4000000000000
    | 7 => 2599879156632099 / 4000000000000
    | 8 => 1915059219592041 / 4000000000000
    | 9 => 2938193322434343 / 4000000000000
    | 10 => 1696366705638447 / 4000000000000
    | 11 => 3010232487547323 / 4000000000000
    | 12 => 2812549666954887 / 4000000000000
    | 13 => 2007168154390071 / 4000000000000
    | 14 => 2275914761145009 / 4000000000000
    | 15 => 1897420451801121 / 4000000000000
    | 16 => 1676428512155541 / 4000000000000
    | 17 => 485894324762559 / 800000000000
    | 18 => 1344009273510573 / 4000000000000
    | 19 => 1139331545650053 / 4000000000000
    | 20 => 712940780407959 / 4000000000000
    | 21 => 383421922837353 / 4000000000000
    | 22 => 1041065106691059 / 4000000000000
    | 23 => 1421485399793043 / 4000000000000
    | 24 => 601059219592041 / 4000000000000
    | 25 => 2443272357831561 / 4000000000000
    | _ => 1631992703861799 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (24206594464 / 1000000000000) (24206597902 / 1000000000000), orderedInterval (-36806416282 / 1000000000000) (-36806412844 / 1000000000000))
    | 1 => (orderedInterval (-38665760669 / 1000000000000) (-38665760668 / 1000000000000), orderedInterval (-33623619417 / 1000000000000) (-33623619416 / 1000000000000))
    | 2 => (orderedInterval (25073555082 / 1000000000000) (25073561350 / 1000000000000), orderedInterval (-31630911557 / 1000000000000) (-31630905289 / 1000000000000))
    | 3 => (orderedInterval (72348104926 / 1000000000000) (72348183558 / 1000000000000), orderedInterval (-62011360255 / 1000000000000) (-62011281623 / 1000000000000))
    | 4 => (orderedInterval (53847540956 / 1000000000000) (53847547407 / 1000000000000), orderedInterval (-21521347921 / 1000000000000) (-21521341469 / 1000000000000))
    | 5 => (orderedInterval (17670495663 / 1000000000000) (17670495664 / 1000000000000), orderedInterval (30380187009 / 1000000000000) (30380187010 / 1000000000000))
    | 6 => (orderedInterval (1168049253 / 1000000000000) (1168049254 / 1000000000000), orderedInterval (-40952235349 / 1000000000000) (-40952235347 / 1000000000000))
    | 7 => (orderedInterval (-13480669537 / 1000000000000) (-13480669536 / 1000000000000), orderedInterval (-28233784734 / 1000000000000) (-28233784733 / 1000000000000))
    | 8 => (orderedInterval (32722139393 / 1000000000000) (32722194153 / 1000000000000), orderedInterval (-16126815997 / 1000000000000) (-16126761237 / 1000000000000))
    | 9 => (orderedInterval (5874038125 / 1000000000000) (5874038126 / 1000000000000), orderedInterval (28843493712 / 1000000000000) (28843493713 / 1000000000000))
    | 10 => (orderedInterval (-26741625845 / 1000000000000) (-26741625844 / 1000000000000), orderedInterval (-28004567427 / 1000000000000) (-28004567426 / 1000000000000))
    | 11 => (orderedInterval (-17343395148 / 1000000000000) (-17343394599 / 1000000000000), orderedInterval (23359921143 / 1000000000000) (23359921691 / 1000000000000))
    | 12 => (orderedInterval (6151306064 / 1000000000000) (6151306065 / 1000000000000), orderedInterval (29450004814 / 1000000000000) (29450004815 / 1000000000000))
    | 13 => (orderedInterval (-2762549044 / 1000000000000) (-2762549043 / 1000000000000), orderedInterval (35514178983 / 1000000000000) (35514178984 / 1000000000000))
    | 14 => (orderedInterval (-30331723633 / 1000000000000) (-30331723631 / 1000000000000), orderedInterval (-14075396286 / 1000000000000) (-14075396284 / 1000000000000))
    | 15 => (orderedInterval (-25231713622 / 1000000000000) (-25231713621 / 1000000000000), orderedInterval (-26533428596 / 1000000000000) (-26533428595 / 1000000000000))
    | 16 => (orderedInterval (-34395432951 / 1000000000000) (-34395377067 / 1000000000000), orderedInterval (18369835666 / 1000000000000) (18369891549 / 1000000000000))
    | 17 => (orderedInterval (-31329070831 / 1000000000000) (-31329055259 / 1000000000000), orderedInterval (8189800188 / 1000000000000) (8189815761 / 1000000000000))
    | 18 => (orderedInterval (-25887434853 / 1000000000000) (-25887434852 / 1000000000000), orderedInterval (-34954761893 / 1000000000000) (-34954761892 / 1000000000000))
    | 19 => (orderedInterval (12477272547 / 1000000000000) (12477272638 / 1000000000000), orderedInterval (-45622174478 / 1000000000000) (-45622174387 / 1000000000000))
    | 20 => (orderedInterval (3040055199 / 1000000000000) (3040055207 / 1000000000000), orderedInterval (-59695780824 / 1000000000000) (-59695780816 / 1000000000000))
    | 21 => (orderedInterval (55537739378 / 1000000000000) (55537794000 / 1000000000000), orderedInterval (-59930444225 / 1000000000000) (-59930389602 / 1000000000000))
    | 22 => (orderedInterval (-14568590096 / 1000000000000) (-14568590095 / 1000000000000), orderedInterval (-47235025447 / 1000000000000) (-47235025446 / 1000000000000))
    | 23 => (orderedInterval (-38743194020 / 1000000000000) (-38743194019 / 1000000000000), orderedInterval (-16986173658 / 1000000000000) (-16986173657 / 1000000000000))
    | 24 => (orderedInterval (16287699399 / 1000000000000) (16287699400 / 1000000000000), orderedInterval (62964721240 / 1000000000000) (62964721241 / 1000000000000))
    | 25 => (orderedInterval (27292156748 / 1000000000000) (27292210136 / 1000000000000), orderedInterval (-17267010255 / 1000000000000) (-17266956867 / 1000000000000))
    | _ => (orderedInterval (14513155302 / 1000000000000) (14513155303 / 1000000000000), orderedInterval (36720732610 / 1000000000000) (36720732611 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (10705701552 / 1000000000000) (10705703306 / 1000000000000)
      | 1 => orderedInterval (-75047972 / 1000000000000) (-75046843 / 1000000000000)
      | 2 => orderedInterval (1206627323 / 1000000000000) (1206628666 / 1000000000000)
      | 3 => orderedInterval (-5490545943 / 1000000000000) (-5490545734 / 1000000000000)
      | 4 => orderedInterval (-218788640 / 1000000000000) (-218788600 / 1000000000000)
      | 5 => orderedInterval (874817652 / 1000000000000) (874821281 / 1000000000000)
      | 6 => orderedInterval (3531961873 / 1000000000000) (3531961961 / 1000000000000)
      | 7 => orderedInterval (2274238319 / 1000000000000) (2274239367 / 1000000000000)
      | _ => orderedInterval (-4846499780 / 1000000000000) (-4846495343 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-17030214223 / 1000000000000) (-17030212396 / 1000000000000)
      | 1 => orderedInterval (-3694677901 / 1000000000000) (-3694677536 / 1000000000000)
      | 2 => orderedInterval (1155011831 / 1000000000000) (1155013792 / 1000000000000)
      | 3 => orderedInterval (-6531375966 / 1000000000000) (-6531375517 / 1000000000000)
      | 4 => orderedInterval (4115297292 / 1000000000000) (4115297356 / 1000000000000)
      | 5 => orderedInterval (-1395944635 / 1000000000000) (-1395939772 / 1000000000000)
      | 6 => orderedInterval (6901164148 / 1000000000000) (6901164229 / 1000000000000)
      | 7 => orderedInterval (2580224340 / 1000000000000) (2580224670 / 1000000000000)
      | _ => orderedInterval (-5769987076 / 1000000000000) (-5769978867 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-11434394541 / 1000000000000) (-11434392621 / 1000000000000)
      | 1 => orderedInterval (2479146302 / 1000000000000) (2479146484 / 1000000000000)
      | 2 => orderedInterval (-3311102694 / 1000000000000) (-3311099819 / 1000000000000)
      | 3 => orderedInterval (21480060965 / 1000000000000) (21480061955 / 1000000000000)
      | 4 => orderedInterval (645309880 / 1000000000000) (645309986 / 1000000000000)
      | 5 => orderedInterval (150020011 / 1000000000000) (150026662 / 1000000000000)
      | 6 => orderedInterval (-3849630953 / 1000000000000) (-3849630876 / 1000000000000)
      | 7 => orderedInterval (-3602877698 / 1000000000000) (-3602877575 / 1000000000000)
      | _ => orderedInterval (11878651411 / 1000000000000) (11878666650 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (17884411610 / 1000000000000) (17884413635 / 1000000000000)
      | 1 => orderedInterval (8456854992 / 1000000000000) (8456855140 / 1000000000000)
      | 2 => orderedInterval (-5528835289 / 1000000000000) (-5528831079 / 1000000000000)
      | 3 => orderedInterval (21774364182 / 1000000000000) (21774366390 / 1000000000000)
      | 4 => orderedInterval (-7128101800 / 1000000000000) (-7128101621 / 1000000000000)
      | 5 => orderedInterval (1779831717 / 1000000000000) (1779841003 / 1000000000000)
      | 6 => orderedInterval (-7341825522 / 1000000000000) (-7341825447 / 1000000000000)
      | 7 => orderedInterval (-2197560846 / 1000000000000) (-2197560784 / 1000000000000)
      | _ => orderedInterval (4091371552 / 1000000000000) (4091399828 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (12340059630 / 1000000000000) (12340061785 / 1000000000000)
      | 1 => orderedInterval (-7420749146 / 1000000000000) (-7420748974 / 1000000000000)
      | 2 => orderedInterval (9974226320 / 1000000000000) (9974232509 / 1000000000000)
      | 3 => orderedInterval (-99637208411 / 1000000000000) (-99637203437 / 1000000000000)
      | 4 => orderedInterval (-2328387250 / 1000000000000) (-2328386940 / 1000000000000)
      | 5 => orderedInterval (-5436516898 / 1000000000000) (-5436503545 / 1000000000000)
      | 6 => orderedInterval (4184556555 / 1000000000000) (4184556628 / 1000000000000)
      | 7 => orderedInterval (4202755762 / 1000000000000) (4202755808 / 1000000000000)
      | _ => orderedInterval (-33057068240 / 1000000000000) (-33057015652 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (7962464384 / 1000000000000) (7962478061 / 1000000000000)
    | 1 => orderedInterval (-19670502190 / 1000000000000) (-19670484041 / 1000000000000)
    | 2 => orderedInterval (14435182683 / 1000000000000) (14435210846 / 1000000000000)
    | 3 => orderedInterval (31790510596 / 1000000000000) (31790557065 / 1000000000000)
    | _ => orderedInterval (-117178331678 / 1000000000000) (-117178251818 / 1000000000000)

theorem compactCertificate457_stateChecks0 :
    compactCertificate457.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 105 12 (657 / 2)) (orderedInterval (24206594464 / 1000000000000) (24206597902 / 1000000000000), orderedInterval (-36806416282 / 1000000000000) (-36806412844 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 77 12 (967886452770957 / 4000000000000)) (orderedInterval (-38665760669 / 1000000000000) (-38665760668 / 1000000000000), orderedInterval (-33623619417 / 1000000000000) (-33623619416 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 125 12 (312994592343981 / 800000000000)) (orderedInterval (25073555082 / 1000000000000) (25073561350 / 1000000000000), orderedInterval (-31630911557 / 1000000000000) (-31630905289 / 1000000000000))) = true
  rfl'

theorem compactCertificate457_stateChecks1 :
    compactCertificate457.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 22 12 (282426852975399 / 4000000000000)) (orderedInterval (72348104926 / 1000000000000) (72348183558 / 1000000000000), orderedInterval (-62011360255 / 1000000000000) (-62011281623 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 60 12 (758638253715003 / 4000000000000)) (orderedInterval (53847540956 / 1000000000000) (53847547407 / 1000000000000), orderedInterval (-21521347921 / 1000000000000) (-21521341469 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 164 12 (2059850434993551 / 4000000000000)) (orderedInterval (17670495663 / 1000000000000) (17670495664 / 1000000000000), orderedInterval (30380187009 / 1000000000000) (30380187010 / 1000000000000))) = true
  rfl'

theorem compactCertificate457_stateChecks2 :
    compactCertificate457.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 121 12 (1517276507430663 / 4000000000000)) (orderedInterval (1168049253 / 1000000000000) (1168049254 / 1000000000000), orderedInterval (-40952235349 / 1000000000000) (-40952235347 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 207 12 (2599879156632099 / 4000000000000)) (orderedInterval (-13480669537 / 1000000000000) (-13480669536 / 1000000000000), orderedInterval (-28233784734 / 1000000000000) (-28233784733 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 152 12 (1915059219592041 / 4000000000000)) (orderedInterval (32722139393 / 1000000000000) (32722194153 / 1000000000000), orderedInterval (-16126815997 / 1000000000000) (-16126761237 / 1000000000000))) = true
  rfl'

theorem compactCertificate457_stateChecks3 :
    compactCertificate457.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 234 12 (2938193322434343 / 4000000000000)) (orderedInterval (5874038125 / 1000000000000) (5874038126 / 1000000000000), orderedInterval (28843493712 / 1000000000000) (28843493713 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 135 12 (1696366705638447 / 4000000000000)) (orderedInterval (-26741625845 / 1000000000000) (-26741625844 / 1000000000000), orderedInterval (-28004567427 / 1000000000000) (-28004567426 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 240 12 (3010232487547323 / 4000000000000)) (orderedInterval (-17343395148 / 1000000000000) (-17343394599 / 1000000000000), orderedInterval (23359921143 / 1000000000000) (23359921691 / 1000000000000))) = true
  rfl'

theorem compactCertificate457_stateChecks4 :
    compactCertificate457.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 224 12 (2812549666954887 / 4000000000000)) (orderedInterval (6151306064 / 1000000000000) (6151306065 / 1000000000000), orderedInterval (29450004814 / 1000000000000) (29450004815 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 160 12 (2007168154390071 / 4000000000000)) (orderedInterval (-2762549044 / 1000000000000) (-2762549043 / 1000000000000), orderedInterval (35514178983 / 1000000000000) (35514178984 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 181 12 (2275914761145009 / 4000000000000)) (orderedInterval (-30331723633 / 1000000000000) (-30331723631 / 1000000000000), orderedInterval (-14075396286 / 1000000000000) (-14075396284 / 1000000000000))) = true
  rfl'

theorem compactCertificate457_stateChecks5 :
    compactCertificate457.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 151 12 (1897420451801121 / 4000000000000)) (orderedInterval (-25231713622 / 1000000000000) (-25231713621 / 1000000000000), orderedInterval (-26533428596 / 1000000000000) (-26533428595 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 133 12 (1676428512155541 / 4000000000000)) (orderedInterval (-34395432951 / 1000000000000) (-34395377067 / 1000000000000), orderedInterval (18369835666 / 1000000000000) (18369891549 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 193 12 (485894324762559 / 800000000000)) (orderedInterval (-31329070831 / 1000000000000) (-31329055259 / 1000000000000), orderedInterval (8189800188 / 1000000000000) (8189815761 / 1000000000000))) = true
  rfl'

theorem compactCertificate457_stateChecks6 :
    compactCertificate457.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 107 12 (1344009273510573 / 4000000000000)) (orderedInterval (-25887434853 / 1000000000000) (-25887434852 / 1000000000000), orderedInterval (-34954761893 / 1000000000000) (-34954761892 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 91 12 (1139331545650053 / 4000000000000)) (orderedInterval (12477272547 / 1000000000000) (12477272638 / 1000000000000), orderedInterval (-45622174478 / 1000000000000) (-45622174387 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 57 12 (712940780407959 / 4000000000000)) (orderedInterval (3040055199 / 1000000000000) (3040055207 / 1000000000000), orderedInterval (-59695780824 / 1000000000000) (-59695780816 / 1000000000000))) = true
  rfl'

theorem compactCertificate457_stateChecks7 :
    compactCertificate457.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 31 12 (383421922837353 / 4000000000000)) (orderedInterval (55537739378 / 1000000000000) (55537794000 / 1000000000000), orderedInterval (-59930444225 / 1000000000000) (-59930389602 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 83 12 (1041065106691059 / 4000000000000)) (orderedInterval (-14568590096 / 1000000000000) (-14568590095 / 1000000000000), orderedInterval (-47235025447 / 1000000000000) (-47235025446 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 113 12 (1421485399793043 / 4000000000000)) (orderedInterval (-38743194020 / 1000000000000) (-38743194019 / 1000000000000), orderedInterval (-16986173658 / 1000000000000) (-16986173657 / 1000000000000))) = true
  rfl'

theorem compactCertificate457_stateChecks8 :
    compactCertificate457.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 48 12 (601059219592041 / 4000000000000)) (orderedInterval (16287699399 / 1000000000000) (16287699400 / 1000000000000), orderedInterval (62964721240 / 1000000000000) (62964721241 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 195 12 (2443272357831561 / 4000000000000)) (orderedInterval (27292156748 / 1000000000000) (27292210136 / 1000000000000), orderedInterval (-17267010255 / 1000000000000) (-17266956867 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 130 12 (1631992703861799 / 4000000000000)) (orderedInterval (14513155302 / 1000000000000) (14513155303 / 1000000000000), orderedInterval (36720732610 / 1000000000000) (36720732611 / 1000000000000))) = true
  rfl'

theorem compactCertificate457_states : ∀ j,
    BesselStateValid (compactCertificate457.point j) (compactCertificate457.state j) :=
  compactCertificate457.statesValid_of_checks3 compactCertificate457_stateChecks0
    compactCertificate457_stateChecks1 compactCertificate457_stateChecks2
    compactCertificate457_stateChecks3 compactCertificate457_stateChecks4
    compactCertificate457_stateChecks5 compactCertificate457_stateChecks6
    compactCertificate457_stateChecks7 compactCertificate457_stateChecks8

theorem compactCertificate457_chunkChecks0_0 :
    compactCertificate457.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (657 / 2) 0 (IntervalRat.scale (657 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (24206594464 / 1000000000000) (24206597902 / 1000000000000), orderedInterval (-36806416282 / 1000000000000) (-36806412844 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (967886452770957 / 4000000000000) 0 (IntervalRat.scale (657 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-38665760669 / 1000000000000) (-38665760668 / 1000000000000), orderedInterval (-33623619417 / 1000000000000) (-33623619416 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (312994592343981 / 800000000000) 0 (IntervalRat.scale (657 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (25073555082 / 1000000000000) (25073561350 / 1000000000000), orderedInterval (-31630911557 / 1000000000000) (-31630905289 / 1000000000000)))) (orderedInterval (10705701552 / 1000000000000) (10705703306 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (282426852975399 / 4000000000000) 0 (IntervalRat.scale (657 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (72348104926 / 1000000000000) (72348183558 / 1000000000000), orderedInterval (-62011360255 / 1000000000000) (-62011281623 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (758638253715003 / 4000000000000) 0 (IntervalRat.scale (657 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (53847540956 / 1000000000000) (53847547407 / 1000000000000), orderedInterval (-21521347921 / 1000000000000) (-21521341469 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2059850434993551 / 4000000000000) 0 (IntervalRat.scale (657 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (17670495663 / 1000000000000) (17670495664 / 1000000000000), orderedInterval (30380187009 / 1000000000000) (30380187010 / 1000000000000)))) (orderedInterval (-75047972 / 1000000000000) (-75046843 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1517276507430663 / 4000000000000) 0 (IntervalRat.scale (657 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (1168049253 / 1000000000000) (1168049254 / 1000000000000), orderedInterval (-40952235349 / 1000000000000) (-40952235347 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2599879156632099 / 4000000000000) 0 (IntervalRat.scale (657 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-13480669537 / 1000000000000) (-13480669536 / 1000000000000), orderedInterval (-28233784734 / 1000000000000) (-28233784733 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1915059219592041 / 4000000000000) 0 (IntervalRat.scale (657 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (32722139393 / 1000000000000) (32722194153 / 1000000000000), orderedInterval (-16126815997 / 1000000000000) (-16126761237 / 1000000000000)))) (orderedInterval (1206627323 / 1000000000000) (1206628666 / 1000000000000))) = true
  rfl'

theorem compactCertificate457_chunkChecks0_1 :
    compactCertificate457.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2938193322434343 / 4000000000000) 0 (IntervalRat.scale (657 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (5874038125 / 1000000000000) (5874038126 / 1000000000000), orderedInterval (28843493712 / 1000000000000) (28843493713 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1696366705638447 / 4000000000000) 0 (IntervalRat.scale (657 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-26741625845 / 1000000000000) (-26741625844 / 1000000000000), orderedInterval (-28004567427 / 1000000000000) (-28004567426 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3010232487547323 / 4000000000000) 0 (IntervalRat.scale (657 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-17343395148 / 1000000000000) (-17343394599 / 1000000000000), orderedInterval (23359921143 / 1000000000000) (23359921691 / 1000000000000)))) (orderedInterval (-5490545943 / 1000000000000) (-5490545734 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2812549666954887 / 4000000000000) 0 (IntervalRat.scale (657 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (6151306064 / 1000000000000) (6151306065 / 1000000000000), orderedInterval (29450004814 / 1000000000000) (29450004815 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2007168154390071 / 4000000000000) 0 (IntervalRat.scale (657 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-2762549044 / 1000000000000) (-2762549043 / 1000000000000), orderedInterval (35514178983 / 1000000000000) (35514178984 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2275914761145009 / 4000000000000) 0 (IntervalRat.scale (657 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-30331723633 / 1000000000000) (-30331723631 / 1000000000000), orderedInterval (-14075396286 / 1000000000000) (-14075396284 / 1000000000000)))) (orderedInterval (-218788640 / 1000000000000) (-218788600 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1897420451801121 / 4000000000000) 0 (IntervalRat.scale (657 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-25231713622 / 1000000000000) (-25231713621 / 1000000000000), orderedInterval (-26533428596 / 1000000000000) (-26533428595 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1676428512155541 / 4000000000000) 0 (IntervalRat.scale (657 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-34395432951 / 1000000000000) (-34395377067 / 1000000000000), orderedInterval (18369835666 / 1000000000000) (18369891549 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (485894324762559 / 800000000000) 0 (IntervalRat.scale (657 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-31329070831 / 1000000000000) (-31329055259 / 1000000000000), orderedInterval (8189800188 / 1000000000000) (8189815761 / 1000000000000)))) (orderedInterval (874817652 / 1000000000000) (874821281 / 1000000000000))) = true
  rfl'

theorem compactCertificate457_chunkChecks0_2 :
    compactCertificate457.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1344009273510573 / 4000000000000) 0 (IntervalRat.scale (657 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-25887434853 / 1000000000000) (-25887434852 / 1000000000000), orderedInterval (-34954761893 / 1000000000000) (-34954761892 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1139331545650053 / 4000000000000) 0 (IntervalRat.scale (657 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (12477272547 / 1000000000000) (12477272638 / 1000000000000), orderedInterval (-45622174478 / 1000000000000) (-45622174387 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (712940780407959 / 4000000000000) 0 (IntervalRat.scale (657 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (3040055199 / 1000000000000) (3040055207 / 1000000000000), orderedInterval (-59695780824 / 1000000000000) (-59695780816 / 1000000000000)))) (orderedInterval (3531961873 / 1000000000000) (3531961961 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (383421922837353 / 4000000000000) 0 (IntervalRat.scale (657 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (55537739378 / 1000000000000) (55537794000 / 1000000000000), orderedInterval (-59930444225 / 1000000000000) (-59930389602 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1041065106691059 / 4000000000000) 0 (IntervalRat.scale (657 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-14568590096 / 1000000000000) (-14568590095 / 1000000000000), orderedInterval (-47235025447 / 1000000000000) (-47235025446 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1421485399793043 / 4000000000000) 0 (IntervalRat.scale (657 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-38743194020 / 1000000000000) (-38743194019 / 1000000000000), orderedInterval (-16986173658 / 1000000000000) (-16986173657 / 1000000000000)))) (orderedInterval (2274238319 / 1000000000000) (2274239367 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (601059219592041 / 4000000000000) 0 (IntervalRat.scale (657 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (16287699399 / 1000000000000) (16287699400 / 1000000000000), orderedInterval (62964721240 / 1000000000000) (62964721241 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2443272357831561 / 4000000000000) 0 (IntervalRat.scale (657 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27292156748 / 1000000000000) (27292210136 / 1000000000000), orderedInterval (-17267010255 / 1000000000000) (-17266956867 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1631992703861799 / 4000000000000) 0 (IntervalRat.scale (657 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (14513155302 / 1000000000000) (14513155303 / 1000000000000), orderedInterval (36720732610 / 1000000000000) (36720732611 / 1000000000000)))) (orderedInterval (-4846499780 / 1000000000000) (-4846495343 / 1000000000000))) = true
  rfl'

theorem compactCertificate457_chunkChecks0 :
    compactCertificate457.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate457.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate457_chunkChecks0_0
    compactCertificate457_chunkChecks0_1 compactCertificate457_chunkChecks0_2

theorem compactCertificate457_chunkChecks1_0 :
    compactCertificate457.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (657 / 2) 1 (IntervalRat.scale (657 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (24206594464 / 1000000000000) (24206597902 / 1000000000000), orderedInterval (-36806416282 / 1000000000000) (-36806412844 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (967886452770957 / 4000000000000) 1 (IntervalRat.scale (657 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-38665760669 / 1000000000000) (-38665760668 / 1000000000000), orderedInterval (-33623619417 / 1000000000000) (-33623619416 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (312994592343981 / 800000000000) 1 (IntervalRat.scale (657 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (25073555082 / 1000000000000) (25073561350 / 1000000000000), orderedInterval (-31630911557 / 1000000000000) (-31630905289 / 1000000000000)))) (orderedInterval (-17030214223 / 1000000000000) (-17030212396 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (282426852975399 / 4000000000000) 1 (IntervalRat.scale (657 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (72348104926 / 1000000000000) (72348183558 / 1000000000000), orderedInterval (-62011360255 / 1000000000000) (-62011281623 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (758638253715003 / 4000000000000) 1 (IntervalRat.scale (657 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (53847540956 / 1000000000000) (53847547407 / 1000000000000), orderedInterval (-21521347921 / 1000000000000) (-21521341469 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2059850434993551 / 4000000000000) 1 (IntervalRat.scale (657 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (17670495663 / 1000000000000) (17670495664 / 1000000000000), orderedInterval (30380187009 / 1000000000000) (30380187010 / 1000000000000)))) (orderedInterval (-3694677901 / 1000000000000) (-3694677536 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1517276507430663 / 4000000000000) 1 (IntervalRat.scale (657 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (1168049253 / 1000000000000) (1168049254 / 1000000000000), orderedInterval (-40952235349 / 1000000000000) (-40952235347 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2599879156632099 / 4000000000000) 1 (IntervalRat.scale (657 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-13480669537 / 1000000000000) (-13480669536 / 1000000000000), orderedInterval (-28233784734 / 1000000000000) (-28233784733 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1915059219592041 / 4000000000000) 1 (IntervalRat.scale (657 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (32722139393 / 1000000000000) (32722194153 / 1000000000000), orderedInterval (-16126815997 / 1000000000000) (-16126761237 / 1000000000000)))) (orderedInterval (1155011831 / 1000000000000) (1155013792 / 1000000000000))) = true
  rfl'

theorem compactCertificate457_chunkChecks1_1 :
    compactCertificate457.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2938193322434343 / 4000000000000) 1 (IntervalRat.scale (657 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (5874038125 / 1000000000000) (5874038126 / 1000000000000), orderedInterval (28843493712 / 1000000000000) (28843493713 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1696366705638447 / 4000000000000) 1 (IntervalRat.scale (657 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-26741625845 / 1000000000000) (-26741625844 / 1000000000000), orderedInterval (-28004567427 / 1000000000000) (-28004567426 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3010232487547323 / 4000000000000) 1 (IntervalRat.scale (657 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-17343395148 / 1000000000000) (-17343394599 / 1000000000000), orderedInterval (23359921143 / 1000000000000) (23359921691 / 1000000000000)))) (orderedInterval (-6531375966 / 1000000000000) (-6531375517 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2812549666954887 / 4000000000000) 1 (IntervalRat.scale (657 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (6151306064 / 1000000000000) (6151306065 / 1000000000000), orderedInterval (29450004814 / 1000000000000) (29450004815 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2007168154390071 / 4000000000000) 1 (IntervalRat.scale (657 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-2762549044 / 1000000000000) (-2762549043 / 1000000000000), orderedInterval (35514178983 / 1000000000000) (35514178984 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2275914761145009 / 4000000000000) 1 (IntervalRat.scale (657 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-30331723633 / 1000000000000) (-30331723631 / 1000000000000), orderedInterval (-14075396286 / 1000000000000) (-14075396284 / 1000000000000)))) (orderedInterval (4115297292 / 1000000000000) (4115297356 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1897420451801121 / 4000000000000) 1 (IntervalRat.scale (657 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-25231713622 / 1000000000000) (-25231713621 / 1000000000000), orderedInterval (-26533428596 / 1000000000000) (-26533428595 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1676428512155541 / 4000000000000) 1 (IntervalRat.scale (657 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-34395432951 / 1000000000000) (-34395377067 / 1000000000000), orderedInterval (18369835666 / 1000000000000) (18369891549 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (485894324762559 / 800000000000) 1 (IntervalRat.scale (657 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-31329070831 / 1000000000000) (-31329055259 / 1000000000000), orderedInterval (8189800188 / 1000000000000) (8189815761 / 1000000000000)))) (orderedInterval (-1395944635 / 1000000000000) (-1395939772 / 1000000000000))) = true
  rfl'

theorem compactCertificate457_chunkChecks1_2 :
    compactCertificate457.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1344009273510573 / 4000000000000) 1 (IntervalRat.scale (657 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-25887434853 / 1000000000000) (-25887434852 / 1000000000000), orderedInterval (-34954761893 / 1000000000000) (-34954761892 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1139331545650053 / 4000000000000) 1 (IntervalRat.scale (657 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (12477272547 / 1000000000000) (12477272638 / 1000000000000), orderedInterval (-45622174478 / 1000000000000) (-45622174387 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (712940780407959 / 4000000000000) 1 (IntervalRat.scale (657 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (3040055199 / 1000000000000) (3040055207 / 1000000000000), orderedInterval (-59695780824 / 1000000000000) (-59695780816 / 1000000000000)))) (orderedInterval (6901164148 / 1000000000000) (6901164229 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (383421922837353 / 4000000000000) 1 (IntervalRat.scale (657 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (55537739378 / 1000000000000) (55537794000 / 1000000000000), orderedInterval (-59930444225 / 1000000000000) (-59930389602 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1041065106691059 / 4000000000000) 1 (IntervalRat.scale (657 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-14568590096 / 1000000000000) (-14568590095 / 1000000000000), orderedInterval (-47235025447 / 1000000000000) (-47235025446 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1421485399793043 / 4000000000000) 1 (IntervalRat.scale (657 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-38743194020 / 1000000000000) (-38743194019 / 1000000000000), orderedInterval (-16986173658 / 1000000000000) (-16986173657 / 1000000000000)))) (orderedInterval (2580224340 / 1000000000000) (2580224670 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (601059219592041 / 4000000000000) 1 (IntervalRat.scale (657 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (16287699399 / 1000000000000) (16287699400 / 1000000000000), orderedInterval (62964721240 / 1000000000000) (62964721241 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2443272357831561 / 4000000000000) 1 (IntervalRat.scale (657 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27292156748 / 1000000000000) (27292210136 / 1000000000000), orderedInterval (-17267010255 / 1000000000000) (-17266956867 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1631992703861799 / 4000000000000) 1 (IntervalRat.scale (657 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (14513155302 / 1000000000000) (14513155303 / 1000000000000), orderedInterval (36720732610 / 1000000000000) (36720732611 / 1000000000000)))) (orderedInterval (-5769987076 / 1000000000000) (-5769978867 / 1000000000000))) = true
  rfl'

theorem compactCertificate457_chunkChecks1 :
    compactCertificate457.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate457.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate457_chunkChecks1_0
    compactCertificate457_chunkChecks1_1 compactCertificate457_chunkChecks1_2

theorem compactCertificate457_chunkChecks2_0 :
    compactCertificate457.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (657 / 2) 2 (IntervalRat.scale (657 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (24206594464 / 1000000000000) (24206597902 / 1000000000000), orderedInterval (-36806416282 / 1000000000000) (-36806412844 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (967886452770957 / 4000000000000) 2 (IntervalRat.scale (657 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-38665760669 / 1000000000000) (-38665760668 / 1000000000000), orderedInterval (-33623619417 / 1000000000000) (-33623619416 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (312994592343981 / 800000000000) 2 (IntervalRat.scale (657 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (25073555082 / 1000000000000) (25073561350 / 1000000000000), orderedInterval (-31630911557 / 1000000000000) (-31630905289 / 1000000000000)))) (orderedInterval (-11434394541 / 1000000000000) (-11434392621 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (282426852975399 / 4000000000000) 2 (IntervalRat.scale (657 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (72348104926 / 1000000000000) (72348183558 / 1000000000000), orderedInterval (-62011360255 / 1000000000000) (-62011281623 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (758638253715003 / 4000000000000) 2 (IntervalRat.scale (657 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (53847540956 / 1000000000000) (53847547407 / 1000000000000), orderedInterval (-21521347921 / 1000000000000) (-21521341469 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2059850434993551 / 4000000000000) 2 (IntervalRat.scale (657 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (17670495663 / 1000000000000) (17670495664 / 1000000000000), orderedInterval (30380187009 / 1000000000000) (30380187010 / 1000000000000)))) (orderedInterval (2479146302 / 1000000000000) (2479146484 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1517276507430663 / 4000000000000) 2 (IntervalRat.scale (657 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (1168049253 / 1000000000000) (1168049254 / 1000000000000), orderedInterval (-40952235349 / 1000000000000) (-40952235347 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2599879156632099 / 4000000000000) 2 (IntervalRat.scale (657 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-13480669537 / 1000000000000) (-13480669536 / 1000000000000), orderedInterval (-28233784734 / 1000000000000) (-28233784733 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1915059219592041 / 4000000000000) 2 (IntervalRat.scale (657 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (32722139393 / 1000000000000) (32722194153 / 1000000000000), orderedInterval (-16126815997 / 1000000000000) (-16126761237 / 1000000000000)))) (orderedInterval (-3311102694 / 1000000000000) (-3311099819 / 1000000000000))) = true
  rfl'

theorem compactCertificate457_chunkChecks2_1 :
    compactCertificate457.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2938193322434343 / 4000000000000) 2 (IntervalRat.scale (657 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (5874038125 / 1000000000000) (5874038126 / 1000000000000), orderedInterval (28843493712 / 1000000000000) (28843493713 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1696366705638447 / 4000000000000) 2 (IntervalRat.scale (657 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-26741625845 / 1000000000000) (-26741625844 / 1000000000000), orderedInterval (-28004567427 / 1000000000000) (-28004567426 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3010232487547323 / 4000000000000) 2 (IntervalRat.scale (657 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-17343395148 / 1000000000000) (-17343394599 / 1000000000000), orderedInterval (23359921143 / 1000000000000) (23359921691 / 1000000000000)))) (orderedInterval (21480060965 / 1000000000000) (21480061955 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2812549666954887 / 4000000000000) 2 (IntervalRat.scale (657 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (6151306064 / 1000000000000) (6151306065 / 1000000000000), orderedInterval (29450004814 / 1000000000000) (29450004815 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2007168154390071 / 4000000000000) 2 (IntervalRat.scale (657 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-2762549044 / 1000000000000) (-2762549043 / 1000000000000), orderedInterval (35514178983 / 1000000000000) (35514178984 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2275914761145009 / 4000000000000) 2 (IntervalRat.scale (657 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-30331723633 / 1000000000000) (-30331723631 / 1000000000000), orderedInterval (-14075396286 / 1000000000000) (-14075396284 / 1000000000000)))) (orderedInterval (645309880 / 1000000000000) (645309986 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1897420451801121 / 4000000000000) 2 (IntervalRat.scale (657 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-25231713622 / 1000000000000) (-25231713621 / 1000000000000), orderedInterval (-26533428596 / 1000000000000) (-26533428595 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1676428512155541 / 4000000000000) 2 (IntervalRat.scale (657 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-34395432951 / 1000000000000) (-34395377067 / 1000000000000), orderedInterval (18369835666 / 1000000000000) (18369891549 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (485894324762559 / 800000000000) 2 (IntervalRat.scale (657 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-31329070831 / 1000000000000) (-31329055259 / 1000000000000), orderedInterval (8189800188 / 1000000000000) (8189815761 / 1000000000000)))) (orderedInterval (150020011 / 1000000000000) (150026662 / 1000000000000))) = true
  rfl'

theorem compactCertificate457_chunkChecks2_2 :
    compactCertificate457.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1344009273510573 / 4000000000000) 2 (IntervalRat.scale (657 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-25887434853 / 1000000000000) (-25887434852 / 1000000000000), orderedInterval (-34954761893 / 1000000000000) (-34954761892 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1139331545650053 / 4000000000000) 2 (IntervalRat.scale (657 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (12477272547 / 1000000000000) (12477272638 / 1000000000000), orderedInterval (-45622174478 / 1000000000000) (-45622174387 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (712940780407959 / 4000000000000) 2 (IntervalRat.scale (657 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (3040055199 / 1000000000000) (3040055207 / 1000000000000), orderedInterval (-59695780824 / 1000000000000) (-59695780816 / 1000000000000)))) (orderedInterval (-3849630953 / 1000000000000) (-3849630876 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (383421922837353 / 4000000000000) 2 (IntervalRat.scale (657 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (55537739378 / 1000000000000) (55537794000 / 1000000000000), orderedInterval (-59930444225 / 1000000000000) (-59930389602 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1041065106691059 / 4000000000000) 2 (IntervalRat.scale (657 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-14568590096 / 1000000000000) (-14568590095 / 1000000000000), orderedInterval (-47235025447 / 1000000000000) (-47235025446 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1421485399793043 / 4000000000000) 2 (IntervalRat.scale (657 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-38743194020 / 1000000000000) (-38743194019 / 1000000000000), orderedInterval (-16986173658 / 1000000000000) (-16986173657 / 1000000000000)))) (orderedInterval (-3602877698 / 1000000000000) (-3602877575 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (601059219592041 / 4000000000000) 2 (IntervalRat.scale (657 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (16287699399 / 1000000000000) (16287699400 / 1000000000000), orderedInterval (62964721240 / 1000000000000) (62964721241 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2443272357831561 / 4000000000000) 2 (IntervalRat.scale (657 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27292156748 / 1000000000000) (27292210136 / 1000000000000), orderedInterval (-17267010255 / 1000000000000) (-17266956867 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1631992703861799 / 4000000000000) 2 (IntervalRat.scale (657 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (14513155302 / 1000000000000) (14513155303 / 1000000000000), orderedInterval (36720732610 / 1000000000000) (36720732611 / 1000000000000)))) (orderedInterval (11878651411 / 1000000000000) (11878666650 / 1000000000000))) = true
  rfl'

theorem compactCertificate457_chunkChecks2 :
    compactCertificate457.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate457.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate457_chunkChecks2_0
    compactCertificate457_chunkChecks2_1 compactCertificate457_chunkChecks2_2

theorem compactCertificate457_chunkChecks3_0 :
    compactCertificate457.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (657 / 2) 3 (IntervalRat.scale (657 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (24206594464 / 1000000000000) (24206597902 / 1000000000000), orderedInterval (-36806416282 / 1000000000000) (-36806412844 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (967886452770957 / 4000000000000) 3 (IntervalRat.scale (657 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-38665760669 / 1000000000000) (-38665760668 / 1000000000000), orderedInterval (-33623619417 / 1000000000000) (-33623619416 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (312994592343981 / 800000000000) 3 (IntervalRat.scale (657 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (25073555082 / 1000000000000) (25073561350 / 1000000000000), orderedInterval (-31630911557 / 1000000000000) (-31630905289 / 1000000000000)))) (orderedInterval (17884411610 / 1000000000000) (17884413635 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (282426852975399 / 4000000000000) 3 (IntervalRat.scale (657 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (72348104926 / 1000000000000) (72348183558 / 1000000000000), orderedInterval (-62011360255 / 1000000000000) (-62011281623 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (758638253715003 / 4000000000000) 3 (IntervalRat.scale (657 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (53847540956 / 1000000000000) (53847547407 / 1000000000000), orderedInterval (-21521347921 / 1000000000000) (-21521341469 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2059850434993551 / 4000000000000) 3 (IntervalRat.scale (657 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (17670495663 / 1000000000000) (17670495664 / 1000000000000), orderedInterval (30380187009 / 1000000000000) (30380187010 / 1000000000000)))) (orderedInterval (8456854992 / 1000000000000) (8456855140 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1517276507430663 / 4000000000000) 3 (IntervalRat.scale (657 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (1168049253 / 1000000000000) (1168049254 / 1000000000000), orderedInterval (-40952235349 / 1000000000000) (-40952235347 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2599879156632099 / 4000000000000) 3 (IntervalRat.scale (657 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-13480669537 / 1000000000000) (-13480669536 / 1000000000000), orderedInterval (-28233784734 / 1000000000000) (-28233784733 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1915059219592041 / 4000000000000) 3 (IntervalRat.scale (657 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (32722139393 / 1000000000000) (32722194153 / 1000000000000), orderedInterval (-16126815997 / 1000000000000) (-16126761237 / 1000000000000)))) (orderedInterval (-5528835289 / 1000000000000) (-5528831079 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate457_chunkChecks3_1 :
    compactCertificate457.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2938193322434343 / 4000000000000) 3 (IntervalRat.scale (657 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (5874038125 / 1000000000000) (5874038126 / 1000000000000), orderedInterval (28843493712 / 1000000000000) (28843493713 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1696366705638447 / 4000000000000) 3 (IntervalRat.scale (657 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-26741625845 / 1000000000000) (-26741625844 / 1000000000000), orderedInterval (-28004567427 / 1000000000000) (-28004567426 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3010232487547323 / 4000000000000) 3 (IntervalRat.scale (657 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-17343395148 / 1000000000000) (-17343394599 / 1000000000000), orderedInterval (23359921143 / 1000000000000) (23359921691 / 1000000000000)))) (orderedInterval (21774364182 / 1000000000000) (21774366390 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2812549666954887 / 4000000000000) 3 (IntervalRat.scale (657 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (6151306064 / 1000000000000) (6151306065 / 1000000000000), orderedInterval (29450004814 / 1000000000000) (29450004815 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2007168154390071 / 4000000000000) 3 (IntervalRat.scale (657 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-2762549044 / 1000000000000) (-2762549043 / 1000000000000), orderedInterval (35514178983 / 1000000000000) (35514178984 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2275914761145009 / 4000000000000) 3 (IntervalRat.scale (657 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-30331723633 / 1000000000000) (-30331723631 / 1000000000000), orderedInterval (-14075396286 / 1000000000000) (-14075396284 / 1000000000000)))) (orderedInterval (-7128101800 / 1000000000000) (-7128101621 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1897420451801121 / 4000000000000) 3 (IntervalRat.scale (657 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-25231713622 / 1000000000000) (-25231713621 / 1000000000000), orderedInterval (-26533428596 / 1000000000000) (-26533428595 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1676428512155541 / 4000000000000) 3 (IntervalRat.scale (657 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-34395432951 / 1000000000000) (-34395377067 / 1000000000000), orderedInterval (18369835666 / 1000000000000) (18369891549 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (485894324762559 / 800000000000) 3 (IntervalRat.scale (657 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-31329070831 / 1000000000000) (-31329055259 / 1000000000000), orderedInterval (8189800188 / 1000000000000) (8189815761 / 1000000000000)))) (orderedInterval (1779831717 / 1000000000000) (1779841003 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate457_chunkChecks3_2 :
    compactCertificate457.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1344009273510573 / 4000000000000) 3 (IntervalRat.scale (657 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-25887434853 / 1000000000000) (-25887434852 / 1000000000000), orderedInterval (-34954761893 / 1000000000000) (-34954761892 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1139331545650053 / 4000000000000) 3 (IntervalRat.scale (657 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (12477272547 / 1000000000000) (12477272638 / 1000000000000), orderedInterval (-45622174478 / 1000000000000) (-45622174387 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (712940780407959 / 4000000000000) 3 (IntervalRat.scale (657 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (3040055199 / 1000000000000) (3040055207 / 1000000000000), orderedInterval (-59695780824 / 1000000000000) (-59695780816 / 1000000000000)))) (orderedInterval (-7341825522 / 1000000000000) (-7341825447 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (383421922837353 / 4000000000000) 3 (IntervalRat.scale (657 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (55537739378 / 1000000000000) (55537794000 / 1000000000000), orderedInterval (-59930444225 / 1000000000000) (-59930389602 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1041065106691059 / 4000000000000) 3 (IntervalRat.scale (657 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-14568590096 / 1000000000000) (-14568590095 / 1000000000000), orderedInterval (-47235025447 / 1000000000000) (-47235025446 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1421485399793043 / 4000000000000) 3 (IntervalRat.scale (657 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-38743194020 / 1000000000000) (-38743194019 / 1000000000000), orderedInterval (-16986173658 / 1000000000000) (-16986173657 / 1000000000000)))) (orderedInterval (-2197560846 / 1000000000000) (-2197560784 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (601059219592041 / 4000000000000) 3 (IntervalRat.scale (657 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (16287699399 / 1000000000000) (16287699400 / 1000000000000), orderedInterval (62964721240 / 1000000000000) (62964721241 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2443272357831561 / 4000000000000) 3 (IntervalRat.scale (657 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27292156748 / 1000000000000) (27292210136 / 1000000000000), orderedInterval (-17267010255 / 1000000000000) (-17266956867 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1631992703861799 / 4000000000000) 3 (IntervalRat.scale (657 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (14513155302 / 1000000000000) (14513155303 / 1000000000000), orderedInterval (36720732610 / 1000000000000) (36720732611 / 1000000000000)))) (orderedInterval (4091371552 / 1000000000000) (4091399828 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate457_chunkChecks3 :
    compactCertificate457.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate457.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate457_chunkChecks3_0
    compactCertificate457_chunkChecks3_1 compactCertificate457_chunkChecks3_2

theorem compactCertificate457_chunkChecks4_0 :
    compactCertificate457.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (657 / 2) 4 (IntervalRat.scale (657 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (24206594464 / 1000000000000) (24206597902 / 1000000000000), orderedInterval (-36806416282 / 1000000000000) (-36806412844 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (967886452770957 / 4000000000000) 4 (IntervalRat.scale (657 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-38665760669 / 1000000000000) (-38665760668 / 1000000000000), orderedInterval (-33623619417 / 1000000000000) (-33623619416 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (312994592343981 / 800000000000) 4 (IntervalRat.scale (657 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (25073555082 / 1000000000000) (25073561350 / 1000000000000), orderedInterval (-31630911557 / 1000000000000) (-31630905289 / 1000000000000)))) (orderedInterval (12340059630 / 1000000000000) (12340061785 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (282426852975399 / 4000000000000) 4 (IntervalRat.scale (657 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (72348104926 / 1000000000000) (72348183558 / 1000000000000), orderedInterval (-62011360255 / 1000000000000) (-62011281623 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (758638253715003 / 4000000000000) 4 (IntervalRat.scale (657 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (53847540956 / 1000000000000) (53847547407 / 1000000000000), orderedInterval (-21521347921 / 1000000000000) (-21521341469 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2059850434993551 / 4000000000000) 4 (IntervalRat.scale (657 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (17670495663 / 1000000000000) (17670495664 / 1000000000000), orderedInterval (30380187009 / 1000000000000) (30380187010 / 1000000000000)))) (orderedInterval (-7420749146 / 1000000000000) (-7420748974 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1517276507430663 / 4000000000000) 4 (IntervalRat.scale (657 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (1168049253 / 1000000000000) (1168049254 / 1000000000000), orderedInterval (-40952235349 / 1000000000000) (-40952235347 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2599879156632099 / 4000000000000) 4 (IntervalRat.scale (657 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-13480669537 / 1000000000000) (-13480669536 / 1000000000000), orderedInterval (-28233784734 / 1000000000000) (-28233784733 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1915059219592041 / 4000000000000) 4 (IntervalRat.scale (657 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (32722139393 / 1000000000000) (32722194153 / 1000000000000), orderedInterval (-16126815997 / 1000000000000) (-16126761237 / 1000000000000)))) (orderedInterval (9974226320 / 1000000000000) (9974232509 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate457_chunkChecks4_1 :
    compactCertificate457.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2938193322434343 / 4000000000000) 4 (IntervalRat.scale (657 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (5874038125 / 1000000000000) (5874038126 / 1000000000000), orderedInterval (28843493712 / 1000000000000) (28843493713 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1696366705638447 / 4000000000000) 4 (IntervalRat.scale (657 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-26741625845 / 1000000000000) (-26741625844 / 1000000000000), orderedInterval (-28004567427 / 1000000000000) (-28004567426 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3010232487547323 / 4000000000000) 4 (IntervalRat.scale (657 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-17343395148 / 1000000000000) (-17343394599 / 1000000000000), orderedInterval (23359921143 / 1000000000000) (23359921691 / 1000000000000)))) (orderedInterval (-99637208411 / 1000000000000) (-99637203437 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2812549666954887 / 4000000000000) 4 (IntervalRat.scale (657 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (6151306064 / 1000000000000) (6151306065 / 1000000000000), orderedInterval (29450004814 / 1000000000000) (29450004815 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2007168154390071 / 4000000000000) 4 (IntervalRat.scale (657 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-2762549044 / 1000000000000) (-2762549043 / 1000000000000), orderedInterval (35514178983 / 1000000000000) (35514178984 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2275914761145009 / 4000000000000) 4 (IntervalRat.scale (657 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-30331723633 / 1000000000000) (-30331723631 / 1000000000000), orderedInterval (-14075396286 / 1000000000000) (-14075396284 / 1000000000000)))) (orderedInterval (-2328387250 / 1000000000000) (-2328386940 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1897420451801121 / 4000000000000) 4 (IntervalRat.scale (657 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-25231713622 / 1000000000000) (-25231713621 / 1000000000000), orderedInterval (-26533428596 / 1000000000000) (-26533428595 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1676428512155541 / 4000000000000) 4 (IntervalRat.scale (657 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (-34395432951 / 1000000000000) (-34395377067 / 1000000000000), orderedInterval (18369835666 / 1000000000000) (18369891549 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (485894324762559 / 800000000000) 4 (IntervalRat.scale (657 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-31329070831 / 1000000000000) (-31329055259 / 1000000000000), orderedInterval (8189800188 / 1000000000000) (8189815761 / 1000000000000)))) (orderedInterval (-5436516898 / 1000000000000) (-5436503545 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate457_chunkChecks4_2 :
    compactCertificate457.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1344009273510573 / 4000000000000) 4 (IntervalRat.scale (657 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-25887434853 / 1000000000000) (-25887434852 / 1000000000000), orderedInterval (-34954761893 / 1000000000000) (-34954761892 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1139331545650053 / 4000000000000) 4 (IntervalRat.scale (657 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (12477272547 / 1000000000000) (12477272638 / 1000000000000), orderedInterval (-45622174478 / 1000000000000) (-45622174387 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (712940780407959 / 4000000000000) 4 (IntervalRat.scale (657 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (3040055199 / 1000000000000) (3040055207 / 1000000000000), orderedInterval (-59695780824 / 1000000000000) (-59695780816 / 1000000000000)))) (orderedInterval (4184556555 / 1000000000000) (4184556628 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (383421922837353 / 4000000000000) 4 (IntervalRat.scale (657 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (55537739378 / 1000000000000) (55537794000 / 1000000000000), orderedInterval (-59930444225 / 1000000000000) (-59930389602 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1041065106691059 / 4000000000000) 4 (IntervalRat.scale (657 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-14568590096 / 1000000000000) (-14568590095 / 1000000000000), orderedInterval (-47235025447 / 1000000000000) (-47235025446 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1421485399793043 / 4000000000000) 4 (IntervalRat.scale (657 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-38743194020 / 1000000000000) (-38743194019 / 1000000000000), orderedInterval (-16986173658 / 1000000000000) (-16986173657 / 1000000000000)))) (orderedInterval (4202755762 / 1000000000000) (4202755808 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (601059219592041 / 4000000000000) 4 (IntervalRat.scale (657 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (16287699399 / 1000000000000) (16287699400 / 1000000000000), orderedInterval (62964721240 / 1000000000000) (62964721241 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2443272357831561 / 4000000000000) 4 (IntervalRat.scale (657 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (27292156748 / 1000000000000) (27292210136 / 1000000000000), orderedInterval (-17267010255 / 1000000000000) (-17266956867 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1631992703861799 / 4000000000000) 4 (IntervalRat.scale (657 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (14513155302 / 1000000000000) (14513155303 / 1000000000000), orderedInterval (36720732610 / 1000000000000) (36720732611 / 1000000000000)))) (orderedInterval (-33057068240 / 1000000000000) (-33057015652 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate457_chunkChecks4 :
    compactCertificate457.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate457.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate457_chunkChecks4_0
    compactCertificate457_chunkChecks4_1 compactCertificate457_chunkChecks4_2

theorem compactCertificate457_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate457.chunkCheck r b = true :=
  compactCertificate457.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate457_chunkChecks0
    · exact compactCertificate457_chunkChecks1
    · exact compactCertificate457_chunkChecks2
    · exact compactCertificate457_chunkChecks3
    · exact compactCertificate457_chunkChecks4)

theorem compactCertificate457_coefficient0 :
    compactCertificate457.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate457_coefficient1 :
    compactCertificate457.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate457_coefficient2 :
    compactCertificate457.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate457_coefficient3 :
    compactCertificate457.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate457_coefficient4 :
    compactCertificate457.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate457_coefficients : ∀ r : Fin 5,
    compactCertificate457.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate457_coefficient0
  · exact compactCertificate457_coefficient1
  · exact compactCertificate457_coefficient2
  · exact compactCertificate457_coefficient3
  · exact compactCertificate457_coefficient4

theorem compactCertificate457_lower : (1 : ℚ) ≤ compactCertificate457.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate457, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate457_proves {t : ℝ} (ht : t ∈ compactCertificate457.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate457.proves compactCertificate457_states compactCertificate457_chunks
    compactCertificate457_coefficients compactCertificate457_lower ht

end Erdos232
