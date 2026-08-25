/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate479 : CompactCertificate where
  left := 350
  right := 351
  center := 701 / 2
  grid := fun i =>
    match i.val with
    | 0 => 112
    | 1 => 82
    | 2 => 133
    | 3 => 24
    | 4 => 64
    | 5 => 175
    | 6 => 129
    | 7 => 221
    | 8 => 163
    | 9 => 250
    | 10 => 144
    | 11 => 256
    | 12 => 239
    | 13 => 171
    | 14 => 193
    | 15 => 161
    | 16 => 142
    | 17 => 206
    | 18 => 114
    | 19 => 97
    | 20 => 61
    | 21 => 33
    | 22 => 88
    | 23 => 121
    | 24 => 51
    | 25 => 208
    | _ => 139
  point := fun i =>
    match i.val with
    | 0 => 701 / 2
    | 1 => 1032706854478601 / 4000000000000
    | 2 => 333956178437033 / 800000000000
    | 3 => 301341284529307 / 4000000000000
    | 4 => 809445077403679 / 4000000000000
    | 5 => 2197800844643043 / 4000000000000
    | 6 => 1618890154808059 / 4000000000000
    | 7 => 2773995873362407 / 4000000000000
    | 8 => 2043312805074613 / 4000000000000
    | 9 => 3134967304454299 / 4000000000000
    | 10 => 1809974217127171 / 4000000000000
    | 11 => 3211831010305439 / 4000000000000
    | 12 => 3000909157588091 / 4000000000000
    | 13 => 2141590374775403 / 4000000000000
    | 14 => 2428335232211037 / 4000000000000
    | 15 => 2024492749943053 / 4000000000000
    | 16 => 1788700741280113 / 4000000000000
    | 17 => 518435192783187 / 800000000000
    | 18 => 1434019026987689 / 4000000000000
    | 19 => 1215633810503329 / 4000000000000
    | 20 => 760687194925387 / 4000000000000
    | 21 => 409100103362229 / 4000000000000
    | 22 => 1110786361933687 / 4000000000000
    | 23 => 1516683813173399 / 4000000000000
    | 24 => 641312805074613 / 4000000000000
    | 25 => 2606900948005973 / 4000000000000
    | _ => 1741289018884507 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-23117743274 / 1000000000000) (-23117740511 / 1000000000000), orderedInterval (35836463485 / 1000000000000) (35836466248 / 1000000000000))
    | 1 => (orderedInterval (48462742465 / 1000000000000) (48462742469 / 1000000000000), orderedInterval (10731483796 / 1000000000000) (10731483799 / 1000000000000))
    | 2 => (orderedInterval (-15153443491 / 1000000000000) (-15153443490 / 1000000000000), orderedInterval (-35973679180 / 1000000000000) (-35973679179 / 1000000000000))
    | 3 => (orderedInterval (60672050061 / 1000000000000) (60672050062 / 1000000000000), orderedInterval (68658240332 / 1000000000000) (68658240333 / 1000000000000))
    | 4 => (orderedInterval (48859852203 / 1000000000000) (48859877999 / 1000000000000), orderedInterval (-27664613163 / 1000000000000) (-27664587367 / 1000000000000))
    | 5 => (orderedInterval (-15009786221 / 1000000000000) (-15009786220 / 1000000000000), orderedInterval (-30537205404 / 1000000000000) (-30537205403 / 1000000000000))
    | 6 => (orderedInterval (-9511264788 / 1000000000000) (-9511264787 / 1000000000000), orderedInterval (-38491693773 / 1000000000000) (-38491693772 / 1000000000000))
    | 7 => (orderedInterval (236026327 / 1000000000000) (236026328 / 1000000000000), orderedInterval (-30297477345 / 1000000000000) (-30297477344 / 1000000000000))
    | 8 => (orderedInterval (15869699499 / 1000000000000) (15869699789 / 1000000000000), orderedInterval (-31549693266 / 1000000000000) (-31549692977 / 1000000000000))
    | 9 => (orderedInterval (-21803988472 / 1000000000000) (-21803982112 / 1000000000000), orderedInterval (18367890098 / 1000000000000) (18367896458 / 1000000000000))
    | 10 => (orderedInterval (29131338555 / 1000000000000) (29131338556 / 1000000000000), orderedInterval (23595749275 / 1000000000000) (23595749276 / 1000000000000))
    | 11 => (orderedInterval (-13615999165 / 1000000000000) (-13615999101 / 1000000000000), orderedInterval (24654940260 / 1000000000000) (24654940324 / 1000000000000))
    | 12 => (orderedInterval (-4982189941 / 1000000000000) (-4982189940 / 1000000000000), orderedInterval (-28697675401 / 1000000000000) (-28697675400 / 1000000000000))
    | 13 => (orderedInterval (29554608200 / 1000000000000) (29554698013 / 1000000000000), orderedInterval (-17792272259 / 1000000000000) (-17792182446 / 1000000000000))
    | 14 => (orderedInterval (-32369110854 / 1000000000000) (-32369110135 / 1000000000000), orderedInterval (-918080259 / 1000000000000) (-918079541 / 1000000000000))
    | 15 => (orderedInterval (-31797065641 / 1000000000000) (-31797065639 / 1000000000000), orderedInterval (-15677879867 / 1000000000000) (-15677879866 / 1000000000000))
    | 16 => (orderedInterval (36226665344 / 1000000000000) (36226674615 / 1000000000000), orderedInterval (-10589206362 / 1000000000000) (-10589197091 / 1000000000000))
    | 17 => (orderedInterval (31215058627 / 1000000000000) (31215062216 / 1000000000000), orderedInterval (-2850911242 / 1000000000000) (-2850907653 / 1000000000000))
    | 18 => (orderedInterval (38433391763 / 1000000000000) (38433391764 / 1000000000000), orderedInterval (17227516367 / 1000000000000) (17227516368 / 1000000000000))
    | 19 => (orderedInterval (1878181294 / 1000000000000) (1878181297 / 1000000000000), orderedInterval (-45733277820 / 1000000000000) (-45733277817 / 1000000000000))
    | 20 => (orderedInterval (36408472954 / 1000000000000) (36408491866 / 1000000000000), orderedInterval (-45062702134 / 1000000000000) (-45062683223 / 1000000000000))
    | 21 => (orderedInterval (45413448709 / 1000000000000) (45413463846 / 1000000000000), orderedInterval (-64737363724 / 1000000000000) (-64737348587 / 1000000000000))
    | 22 => (orderedInterval (43101158531 / 1000000000000) (43101179006 / 1000000000000), orderedInterval (-20929188320 / 1000000000000) (-20929167845 / 1000000000000))
    | 23 => (orderedInterval (7202288349 / 1000000000000) (7202288360 / 1000000000000), orderedInterval (-40346907242 / 1000000000000) (-40346907230 / 1000000000000))
    | 24 => (orderedInterval (-49029237057 / 1000000000000) (-49029237056 / 1000000000000), orderedInterval (-39430661419 / 1000000000000) (-39430661418 / 1000000000000))
    | 25 => (orderedInterval (-25254820711 / 1000000000000) (-25254796429 / 1000000000000), orderedInterval (18431774105 / 1000000000000) (18431798386 / 1000000000000))
    | _ => (orderedInterval (20765354975 / 1000000000000) (20765356696 / 1000000000000), orderedInterval (-32136321611 / 1000000000000) (-32136319890 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-9600706760 / 1000000000000) (-9600705640 / 1000000000000)
      | 1 => orderedInterval (2192750079 / 1000000000000) (2192751064 / 1000000000000)
      | 2 => orderedInterval (376259320 / 1000000000000) (376259347 / 1000000000000)
      | 3 => orderedInterval (4097102249 / 1000000000000) (4097103527 / 1000000000000)
      | 4 => orderedInterval (3048518679 / 1000000000000) (3048527218 / 1000000000000)
      | 5 => orderedInterval (-1641085445 / 1000000000000) (-1641084788 / 1000000000000)
      | 6 => orderedInterval (-5066226183 / 1000000000000) (-5066225478 / 1000000000000)
      | 7 => orderedInterval (-2368370686 / 1000000000000) (-2368369899 / 1000000000000)
      | _ => orderedInterval (-2135910823 / 1000000000000) (-2135908426 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (11763805286 / 1000000000000) (11763806409 / 1000000000000)
      | 1 => orderedInterval (2659832766 / 1000000000000) (2659833358 / 1000000000000)
      | 2 => orderedInterval (737712549 / 1000000000000) (737712594 / 1000000000000)
      | 3 => orderedInterval (2988229972 / 1000000000000) (2988232807 / 1000000000000)
      | 4 => orderedInterval (-1453069051 / 1000000000000) (-1453056003 / 1000000000000)
      | 5 => orderedInterval (376740353 / 1000000000000) (376741249 / 1000000000000)
      | 6 => orderedInterval (-1369013199 / 1000000000000) (-1369012783 / 1000000000000)
      | 7 => orderedInterval (4070080134 / 1000000000000) (4070080623 / 1000000000000)
      | _ => orderedInterval (4590253862 / 1000000000000) (4590258075 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (10145827628 / 1000000000000) (10145828758 / 1000000000000)
      | 1 => orderedInterval (-3194006021 / 1000000000000) (-3194005639 / 1000000000000)
      | 2 => orderedInterval (-788278159 / 1000000000000) (-788278083 / 1000000000000)
      | 3 => orderedInterval (-12819011220 / 1000000000000) (-12819004898 / 1000000000000)
      | 4 => orderedInterval (-7420499510 / 1000000000000) (-7420479533 / 1000000000000)
      | 5 => orderedInterval (1406881009 / 1000000000000) (1406882262 / 1000000000000)
      | 6 => orderedInterval (6163999704 / 1000000000000) (6163999964 / 1000000000000)
      | 7 => orderedInterval (1319562159 / 1000000000000) (1319562514 / 1000000000000)
      | _ => orderedInterval (-1048920611 / 1000000000000) (-1048913066 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-10706836447 / 1000000000000) (-10706835311 / 1000000000000)
      | 1 => orderedInterval (-8151972481 / 1000000000000) (-8151972199 / 1000000000000)
      | 2 => orderedInterval (-4875817026 / 1000000000000) (-4875816893 / 1000000000000)
      | 3 => orderedInterval (-9374045427 / 1000000000000) (-9374031314 / 1000000000000)
      | 4 => orderedInterval (913182387 / 1000000000000) (913212923 / 1000000000000)
      | 5 => orderedInterval (-255974122 / 1000000000000) (-255972325 / 1000000000000)
      | 6 => orderedInterval (1476963798 / 1000000000000) (1476963973 / 1000000000000)
      | 7 => orderedInterval (-4184291766 / 1000000000000) (-4184291487 / 1000000000000)
      | _ => orderedInterval (-1880636935 / 1000000000000) (-1880623278 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-10758136204 / 1000000000000) (-10758135059 / 1000000000000)
      | 1 => orderedInterval (6687103822 / 1000000000000) (6687104081 / 1000000000000)
      | 2 => orderedInterval (1646684596 / 1000000000000) (1646684833 / 1000000000000)
      | 3 => orderedInterval (49593533031 / 1000000000000) (49593564610 / 1000000000000)
      | 4 => orderedInterval (18572899754 / 1000000000000) (18572946530 / 1000000000000)
      | 5 => orderedInterval (2252115595 / 1000000000000) (2252118261 / 1000000000000)
      | 6 => orderedInterval (-6691857609 / 1000000000000) (-6691857480 / 1000000000000)
      | 7 => orderedInterval (-1123463502 / 1000000000000) (-1123463273 / 1000000000000)
      | _ => orderedInterval (15301266176 / 1000000000000) (15301291147 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-11097669570 / 1000000000000) (-11097653075 / 1000000000000)
    | 1 => orderedInterval (24364572672 / 1000000000000) (24364596329 / 1000000000000)
    | 2 => orderedInterval (-6234445021 / 1000000000000) (-6234407721 / 1000000000000)
    | 3 => orderedInterval (-37039428019 / 1000000000000) (-37039365911 / 1000000000000)
    | _ => orderedInterval (75480145659 / 1000000000000) (75480253650 / 1000000000000)

theorem compactCertificate479_stateChecks0 :
    compactCertificate479.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 112 12 (701 / 2)) (orderedInterval (-23117743274 / 1000000000000) (-23117740511 / 1000000000000), orderedInterval (35836463485 / 1000000000000) (35836466248 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 82 12 (1032706854478601 / 4000000000000)) (orderedInterval (48462742465 / 1000000000000) (48462742469 / 1000000000000), orderedInterval (10731483796 / 1000000000000) (10731483799 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 133 12 (333956178437033 / 800000000000)) (orderedInterval (-15153443491 / 1000000000000) (-15153443490 / 1000000000000), orderedInterval (-35973679180 / 1000000000000) (-35973679179 / 1000000000000))) = true
  rfl'

theorem compactCertificate479_stateChecks1 :
    compactCertificate479.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 24 12 (301341284529307 / 4000000000000)) (orderedInterval (60672050061 / 1000000000000) (60672050062 / 1000000000000), orderedInterval (68658240332 / 1000000000000) (68658240333 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (809445077403679 / 4000000000000)) (orderedInterval (48859852203 / 1000000000000) (48859877999 / 1000000000000), orderedInterval (-27664613163 / 1000000000000) (-27664587367 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 175 12 (2197800844643043 / 4000000000000)) (orderedInterval (-15009786221 / 1000000000000) (-15009786220 / 1000000000000), orderedInterval (-30537205404 / 1000000000000) (-30537205403 / 1000000000000))) = true
  rfl'

theorem compactCertificate479_stateChecks2 :
    compactCertificate479.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 129 12 (1618890154808059 / 4000000000000)) (orderedInterval (-9511264788 / 1000000000000) (-9511264787 / 1000000000000), orderedInterval (-38491693773 / 1000000000000) (-38491693772 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 221 12 (2773995873362407 / 4000000000000)) (orderedInterval (236026327 / 1000000000000) (236026328 / 1000000000000), orderedInterval (-30297477345 / 1000000000000) (-30297477344 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 163 12 (2043312805074613 / 4000000000000)) (orderedInterval (15869699499 / 1000000000000) (15869699789 / 1000000000000), orderedInterval (-31549693266 / 1000000000000) (-31549692977 / 1000000000000))) = true
  rfl'

theorem compactCertificate479_stateChecks3 :
    compactCertificate479.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 250 12 (3134967304454299 / 4000000000000)) (orderedInterval (-21803988472 / 1000000000000) (-21803982112 / 1000000000000), orderedInterval (18367890098 / 1000000000000) (18367896458 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 144 12 (1809974217127171 / 4000000000000)) (orderedInterval (29131338555 / 1000000000000) (29131338556 / 1000000000000), orderedInterval (23595749275 / 1000000000000) (23595749276 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 256 12 (3211831010305439 / 4000000000000)) (orderedInterval (-13615999165 / 1000000000000) (-13615999101 / 1000000000000), orderedInterval (24654940260 / 1000000000000) (24654940324 / 1000000000000))) = true
  rfl'

theorem compactCertificate479_stateChecks4 :
    compactCertificate479.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 239 12 (3000909157588091 / 4000000000000)) (orderedInterval (-4982189941 / 1000000000000) (-4982189940 / 1000000000000), orderedInterval (-28697675401 / 1000000000000) (-28697675400 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 171 12 (2141590374775403 / 4000000000000)) (orderedInterval (29554608200 / 1000000000000) (29554698013 / 1000000000000), orderedInterval (-17792272259 / 1000000000000) (-17792182446 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 193 12 (2428335232211037 / 4000000000000)) (orderedInterval (-32369110854 / 1000000000000) (-32369110135 / 1000000000000), orderedInterval (-918080259 / 1000000000000) (-918079541 / 1000000000000))) = true
  rfl'

theorem compactCertificate479_stateChecks5 :
    compactCertificate479.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 161 12 (2024492749943053 / 4000000000000)) (orderedInterval (-31797065641 / 1000000000000) (-31797065639 / 1000000000000), orderedInterval (-15677879867 / 1000000000000) (-15677879866 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 142 12 (1788700741280113 / 4000000000000)) (orderedInterval (36226665344 / 1000000000000) (36226674615 / 1000000000000), orderedInterval (-10589206362 / 1000000000000) (-10589197091 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 206 12 (518435192783187 / 800000000000)) (orderedInterval (31215058627 / 1000000000000) (31215062216 / 1000000000000), orderedInterval (-2850911242 / 1000000000000) (-2850907653 / 1000000000000))) = true
  rfl'

theorem compactCertificate479_stateChecks6 :
    compactCertificate479.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 114 12 (1434019026987689 / 4000000000000)) (orderedInterval (38433391763 / 1000000000000) (38433391764 / 1000000000000), orderedInterval (17227516367 / 1000000000000) (17227516368 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 97 12 (1215633810503329 / 4000000000000)) (orderedInterval (1878181294 / 1000000000000) (1878181297 / 1000000000000), orderedInterval (-45733277820 / 1000000000000) (-45733277817 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 61 12 (760687194925387 / 4000000000000)) (orderedInterval (36408472954 / 1000000000000) (36408491866 / 1000000000000), orderedInterval (-45062702134 / 1000000000000) (-45062683223 / 1000000000000))) = true
  rfl'

theorem compactCertificate479_stateChecks7 :
    compactCertificate479.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 33 12 (409100103362229 / 4000000000000)) (orderedInterval (45413448709 / 1000000000000) (45413463846 / 1000000000000), orderedInterval (-64737363724 / 1000000000000) (-64737348587 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 88 12 (1110786361933687 / 4000000000000)) (orderedInterval (43101158531 / 1000000000000) (43101179006 / 1000000000000), orderedInterval (-20929188320 / 1000000000000) (-20929167845 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 121 12 (1516683813173399 / 4000000000000)) (orderedInterval (7202288349 / 1000000000000) (7202288360 / 1000000000000), orderedInterval (-40346907242 / 1000000000000) (-40346907230 / 1000000000000))) = true
  rfl'

theorem compactCertificate479_stateChecks8 :
    compactCertificate479.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (641312805074613 / 4000000000000)) (orderedInterval (-49029237057 / 1000000000000) (-49029237056 / 1000000000000), orderedInterval (-39430661419 / 1000000000000) (-39430661418 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 208 12 (2606900948005973 / 4000000000000)) (orderedInterval (-25254820711 / 1000000000000) (-25254796429 / 1000000000000), orderedInterval (18431774105 / 1000000000000) (18431798386 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 139 12 (1741289018884507 / 4000000000000)) (orderedInterval (20765354975 / 1000000000000) (20765356696 / 1000000000000), orderedInterval (-32136321611 / 1000000000000) (-32136319890 / 1000000000000))) = true
  rfl'

theorem compactCertificate479_states : ∀ j,
    BesselStateValid (compactCertificate479.point j) (compactCertificate479.state j) :=
  compactCertificate479.statesValid_of_checks3 compactCertificate479_stateChecks0
    compactCertificate479_stateChecks1 compactCertificate479_stateChecks2
    compactCertificate479_stateChecks3 compactCertificate479_stateChecks4
    compactCertificate479_stateChecks5 compactCertificate479_stateChecks6
    compactCertificate479_stateChecks7 compactCertificate479_stateChecks8

theorem compactCertificate479_chunkChecks0_0 :
    compactCertificate479.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (701 / 2) 0 (IntervalRat.scale (701 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-23117743274 / 1000000000000) (-23117740511 / 1000000000000), orderedInterval (35836463485 / 1000000000000) (35836466248 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1032706854478601 / 4000000000000) 0 (IntervalRat.scale (701 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (48462742465 / 1000000000000) (48462742469 / 1000000000000), orderedInterval (10731483796 / 1000000000000) (10731483799 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (333956178437033 / 800000000000) 0 (IntervalRat.scale (701 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-15153443491 / 1000000000000) (-15153443490 / 1000000000000), orderedInterval (-35973679180 / 1000000000000) (-35973679179 / 1000000000000)))) (orderedInterval (-9600706760 / 1000000000000) (-9600705640 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (301341284529307 / 4000000000000) 0 (IntervalRat.scale (701 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (60672050061 / 1000000000000) (60672050062 / 1000000000000), orderedInterval (68658240332 / 1000000000000) (68658240333 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (809445077403679 / 4000000000000) 0 (IntervalRat.scale (701 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (48859852203 / 1000000000000) (48859877999 / 1000000000000), orderedInterval (-27664613163 / 1000000000000) (-27664587367 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2197800844643043 / 4000000000000) 0 (IntervalRat.scale (701 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-15009786221 / 1000000000000) (-15009786220 / 1000000000000), orderedInterval (-30537205404 / 1000000000000) (-30537205403 / 1000000000000)))) (orderedInterval (2192750079 / 1000000000000) (2192751064 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1618890154808059 / 4000000000000) 0 (IntervalRat.scale (701 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-9511264788 / 1000000000000) (-9511264787 / 1000000000000), orderedInterval (-38491693773 / 1000000000000) (-38491693772 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2773995873362407 / 4000000000000) 0 (IntervalRat.scale (701 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (236026327 / 1000000000000) (236026328 / 1000000000000), orderedInterval (-30297477345 / 1000000000000) (-30297477344 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2043312805074613 / 4000000000000) 0 (IntervalRat.scale (701 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (15869699499 / 1000000000000) (15869699789 / 1000000000000), orderedInterval (-31549693266 / 1000000000000) (-31549692977 / 1000000000000)))) (orderedInterval (376259320 / 1000000000000) (376259347 / 1000000000000))) = true
  rfl'

theorem compactCertificate479_chunkChecks0_1 :
    compactCertificate479.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3134967304454299 / 4000000000000) 0 (IntervalRat.scale (701 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-21803988472 / 1000000000000) (-21803982112 / 1000000000000), orderedInterval (18367890098 / 1000000000000) (18367896458 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1809974217127171 / 4000000000000) 0 (IntervalRat.scale (701 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (29131338555 / 1000000000000) (29131338556 / 1000000000000), orderedInterval (23595749275 / 1000000000000) (23595749276 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3211831010305439 / 4000000000000) 0 (IntervalRat.scale (701 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-13615999165 / 1000000000000) (-13615999101 / 1000000000000), orderedInterval (24654940260 / 1000000000000) (24654940324 / 1000000000000)))) (orderedInterval (4097102249 / 1000000000000) (4097103527 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3000909157588091 / 4000000000000) 0 (IntervalRat.scale (701 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-4982189941 / 1000000000000) (-4982189940 / 1000000000000), orderedInterval (-28697675401 / 1000000000000) (-28697675400 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2141590374775403 / 4000000000000) 0 (IntervalRat.scale (701 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (29554608200 / 1000000000000) (29554698013 / 1000000000000), orderedInterval (-17792272259 / 1000000000000) (-17792182446 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2428335232211037 / 4000000000000) 0 (IntervalRat.scale (701 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-32369110854 / 1000000000000) (-32369110135 / 1000000000000), orderedInterval (-918080259 / 1000000000000) (-918079541 / 1000000000000)))) (orderedInterval (3048518679 / 1000000000000) (3048527218 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2024492749943053 / 4000000000000) 0 (IntervalRat.scale (701 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-31797065641 / 1000000000000) (-31797065639 / 1000000000000), orderedInterval (-15677879867 / 1000000000000) (-15677879866 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1788700741280113 / 4000000000000) 0 (IntervalRat.scale (701 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (36226665344 / 1000000000000) (36226674615 / 1000000000000), orderedInterval (-10589206362 / 1000000000000) (-10589197091 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (518435192783187 / 800000000000) 0 (IntervalRat.scale (701 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (31215058627 / 1000000000000) (31215062216 / 1000000000000), orderedInterval (-2850911242 / 1000000000000) (-2850907653 / 1000000000000)))) (orderedInterval (-1641085445 / 1000000000000) (-1641084788 / 1000000000000))) = true
  rfl'

theorem compactCertificate479_chunkChecks0_2 :
    compactCertificate479.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1434019026987689 / 4000000000000) 0 (IntervalRat.scale (701 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (38433391763 / 1000000000000) (38433391764 / 1000000000000), orderedInterval (17227516367 / 1000000000000) (17227516368 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1215633810503329 / 4000000000000) 0 (IntervalRat.scale (701 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (1878181294 / 1000000000000) (1878181297 / 1000000000000), orderedInterval (-45733277820 / 1000000000000) (-45733277817 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (760687194925387 / 4000000000000) 0 (IntervalRat.scale (701 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (36408472954 / 1000000000000) (36408491866 / 1000000000000), orderedInterval (-45062702134 / 1000000000000) (-45062683223 / 1000000000000)))) (orderedInterval (-5066226183 / 1000000000000) (-5066225478 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (409100103362229 / 4000000000000) 0 (IntervalRat.scale (701 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (45413448709 / 1000000000000) (45413463846 / 1000000000000), orderedInterval (-64737363724 / 1000000000000) (-64737348587 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1110786361933687 / 4000000000000) 0 (IntervalRat.scale (701 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (43101158531 / 1000000000000) (43101179006 / 1000000000000), orderedInterval (-20929188320 / 1000000000000) (-20929167845 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1516683813173399 / 4000000000000) 0 (IntervalRat.scale (701 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (7202288349 / 1000000000000) (7202288360 / 1000000000000), orderedInterval (-40346907242 / 1000000000000) (-40346907230 / 1000000000000)))) (orderedInterval (-2368370686 / 1000000000000) (-2368369899 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (641312805074613 / 4000000000000) 0 (IntervalRat.scale (701 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-49029237057 / 1000000000000) (-49029237056 / 1000000000000), orderedInterval (-39430661419 / 1000000000000) (-39430661418 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2606900948005973 / 4000000000000) 0 (IntervalRat.scale (701 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-25254820711 / 1000000000000) (-25254796429 / 1000000000000), orderedInterval (18431774105 / 1000000000000) (18431798386 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1741289018884507 / 4000000000000) 0 (IntervalRat.scale (701 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (20765354975 / 1000000000000) (20765356696 / 1000000000000), orderedInterval (-32136321611 / 1000000000000) (-32136319890 / 1000000000000)))) (orderedInterval (-2135910823 / 1000000000000) (-2135908426 / 1000000000000))) = true
  rfl'

theorem compactCertificate479_chunkChecks0 :
    compactCertificate479.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate479.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate479_chunkChecks0_0
    compactCertificate479_chunkChecks0_1 compactCertificate479_chunkChecks0_2

theorem compactCertificate479_chunkChecks1_0 :
    compactCertificate479.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (701 / 2) 1 (IntervalRat.scale (701 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-23117743274 / 1000000000000) (-23117740511 / 1000000000000), orderedInterval (35836463485 / 1000000000000) (35836466248 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1032706854478601 / 4000000000000) 1 (IntervalRat.scale (701 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (48462742465 / 1000000000000) (48462742469 / 1000000000000), orderedInterval (10731483796 / 1000000000000) (10731483799 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (333956178437033 / 800000000000) 1 (IntervalRat.scale (701 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-15153443491 / 1000000000000) (-15153443490 / 1000000000000), orderedInterval (-35973679180 / 1000000000000) (-35973679179 / 1000000000000)))) (orderedInterval (11763805286 / 1000000000000) (11763806409 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (301341284529307 / 4000000000000) 1 (IntervalRat.scale (701 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (60672050061 / 1000000000000) (60672050062 / 1000000000000), orderedInterval (68658240332 / 1000000000000) (68658240333 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (809445077403679 / 4000000000000) 1 (IntervalRat.scale (701 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (48859852203 / 1000000000000) (48859877999 / 1000000000000), orderedInterval (-27664613163 / 1000000000000) (-27664587367 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2197800844643043 / 4000000000000) 1 (IntervalRat.scale (701 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-15009786221 / 1000000000000) (-15009786220 / 1000000000000), orderedInterval (-30537205404 / 1000000000000) (-30537205403 / 1000000000000)))) (orderedInterval (2659832766 / 1000000000000) (2659833358 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1618890154808059 / 4000000000000) 1 (IntervalRat.scale (701 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-9511264788 / 1000000000000) (-9511264787 / 1000000000000), orderedInterval (-38491693773 / 1000000000000) (-38491693772 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2773995873362407 / 4000000000000) 1 (IntervalRat.scale (701 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (236026327 / 1000000000000) (236026328 / 1000000000000), orderedInterval (-30297477345 / 1000000000000) (-30297477344 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2043312805074613 / 4000000000000) 1 (IntervalRat.scale (701 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (15869699499 / 1000000000000) (15869699789 / 1000000000000), orderedInterval (-31549693266 / 1000000000000) (-31549692977 / 1000000000000)))) (orderedInterval (737712549 / 1000000000000) (737712594 / 1000000000000))) = true
  rfl'

theorem compactCertificate479_chunkChecks1_1 :
    compactCertificate479.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3134967304454299 / 4000000000000) 1 (IntervalRat.scale (701 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-21803988472 / 1000000000000) (-21803982112 / 1000000000000), orderedInterval (18367890098 / 1000000000000) (18367896458 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1809974217127171 / 4000000000000) 1 (IntervalRat.scale (701 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (29131338555 / 1000000000000) (29131338556 / 1000000000000), orderedInterval (23595749275 / 1000000000000) (23595749276 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3211831010305439 / 4000000000000) 1 (IntervalRat.scale (701 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-13615999165 / 1000000000000) (-13615999101 / 1000000000000), orderedInterval (24654940260 / 1000000000000) (24654940324 / 1000000000000)))) (orderedInterval (2988229972 / 1000000000000) (2988232807 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3000909157588091 / 4000000000000) 1 (IntervalRat.scale (701 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-4982189941 / 1000000000000) (-4982189940 / 1000000000000), orderedInterval (-28697675401 / 1000000000000) (-28697675400 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2141590374775403 / 4000000000000) 1 (IntervalRat.scale (701 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (29554608200 / 1000000000000) (29554698013 / 1000000000000), orderedInterval (-17792272259 / 1000000000000) (-17792182446 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2428335232211037 / 4000000000000) 1 (IntervalRat.scale (701 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-32369110854 / 1000000000000) (-32369110135 / 1000000000000), orderedInterval (-918080259 / 1000000000000) (-918079541 / 1000000000000)))) (orderedInterval (-1453069051 / 1000000000000) (-1453056003 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2024492749943053 / 4000000000000) 1 (IntervalRat.scale (701 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-31797065641 / 1000000000000) (-31797065639 / 1000000000000), orderedInterval (-15677879867 / 1000000000000) (-15677879866 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1788700741280113 / 4000000000000) 1 (IntervalRat.scale (701 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (36226665344 / 1000000000000) (36226674615 / 1000000000000), orderedInterval (-10589206362 / 1000000000000) (-10589197091 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (518435192783187 / 800000000000) 1 (IntervalRat.scale (701 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (31215058627 / 1000000000000) (31215062216 / 1000000000000), orderedInterval (-2850911242 / 1000000000000) (-2850907653 / 1000000000000)))) (orderedInterval (376740353 / 1000000000000) (376741249 / 1000000000000))) = true
  rfl'

theorem compactCertificate479_chunkChecks1_2 :
    compactCertificate479.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1434019026987689 / 4000000000000) 1 (IntervalRat.scale (701 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (38433391763 / 1000000000000) (38433391764 / 1000000000000), orderedInterval (17227516367 / 1000000000000) (17227516368 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1215633810503329 / 4000000000000) 1 (IntervalRat.scale (701 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (1878181294 / 1000000000000) (1878181297 / 1000000000000), orderedInterval (-45733277820 / 1000000000000) (-45733277817 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (760687194925387 / 4000000000000) 1 (IntervalRat.scale (701 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (36408472954 / 1000000000000) (36408491866 / 1000000000000), orderedInterval (-45062702134 / 1000000000000) (-45062683223 / 1000000000000)))) (orderedInterval (-1369013199 / 1000000000000) (-1369012783 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (409100103362229 / 4000000000000) 1 (IntervalRat.scale (701 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (45413448709 / 1000000000000) (45413463846 / 1000000000000), orderedInterval (-64737363724 / 1000000000000) (-64737348587 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1110786361933687 / 4000000000000) 1 (IntervalRat.scale (701 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (43101158531 / 1000000000000) (43101179006 / 1000000000000), orderedInterval (-20929188320 / 1000000000000) (-20929167845 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1516683813173399 / 4000000000000) 1 (IntervalRat.scale (701 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (7202288349 / 1000000000000) (7202288360 / 1000000000000), orderedInterval (-40346907242 / 1000000000000) (-40346907230 / 1000000000000)))) (orderedInterval (4070080134 / 1000000000000) (4070080623 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (641312805074613 / 4000000000000) 1 (IntervalRat.scale (701 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-49029237057 / 1000000000000) (-49029237056 / 1000000000000), orderedInterval (-39430661419 / 1000000000000) (-39430661418 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2606900948005973 / 4000000000000) 1 (IntervalRat.scale (701 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-25254820711 / 1000000000000) (-25254796429 / 1000000000000), orderedInterval (18431774105 / 1000000000000) (18431798386 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1741289018884507 / 4000000000000) 1 (IntervalRat.scale (701 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (20765354975 / 1000000000000) (20765356696 / 1000000000000), orderedInterval (-32136321611 / 1000000000000) (-32136319890 / 1000000000000)))) (orderedInterval (4590253862 / 1000000000000) (4590258075 / 1000000000000))) = true
  rfl'

theorem compactCertificate479_chunkChecks1 :
    compactCertificate479.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate479.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate479_chunkChecks1_0
    compactCertificate479_chunkChecks1_1 compactCertificate479_chunkChecks1_2

theorem compactCertificate479_chunkChecks2_0 :
    compactCertificate479.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (701 / 2) 2 (IntervalRat.scale (701 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-23117743274 / 1000000000000) (-23117740511 / 1000000000000), orderedInterval (35836463485 / 1000000000000) (35836466248 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1032706854478601 / 4000000000000) 2 (IntervalRat.scale (701 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (48462742465 / 1000000000000) (48462742469 / 1000000000000), orderedInterval (10731483796 / 1000000000000) (10731483799 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (333956178437033 / 800000000000) 2 (IntervalRat.scale (701 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-15153443491 / 1000000000000) (-15153443490 / 1000000000000), orderedInterval (-35973679180 / 1000000000000) (-35973679179 / 1000000000000)))) (orderedInterval (10145827628 / 1000000000000) (10145828758 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (301341284529307 / 4000000000000) 2 (IntervalRat.scale (701 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (60672050061 / 1000000000000) (60672050062 / 1000000000000), orderedInterval (68658240332 / 1000000000000) (68658240333 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (809445077403679 / 4000000000000) 2 (IntervalRat.scale (701 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (48859852203 / 1000000000000) (48859877999 / 1000000000000), orderedInterval (-27664613163 / 1000000000000) (-27664587367 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2197800844643043 / 4000000000000) 2 (IntervalRat.scale (701 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-15009786221 / 1000000000000) (-15009786220 / 1000000000000), orderedInterval (-30537205404 / 1000000000000) (-30537205403 / 1000000000000)))) (orderedInterval (-3194006021 / 1000000000000) (-3194005639 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1618890154808059 / 4000000000000) 2 (IntervalRat.scale (701 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-9511264788 / 1000000000000) (-9511264787 / 1000000000000), orderedInterval (-38491693773 / 1000000000000) (-38491693772 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2773995873362407 / 4000000000000) 2 (IntervalRat.scale (701 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (236026327 / 1000000000000) (236026328 / 1000000000000), orderedInterval (-30297477345 / 1000000000000) (-30297477344 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2043312805074613 / 4000000000000) 2 (IntervalRat.scale (701 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (15869699499 / 1000000000000) (15869699789 / 1000000000000), orderedInterval (-31549693266 / 1000000000000) (-31549692977 / 1000000000000)))) (orderedInterval (-788278159 / 1000000000000) (-788278083 / 1000000000000))) = true
  rfl'

theorem compactCertificate479_chunkChecks2_1 :
    compactCertificate479.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3134967304454299 / 4000000000000) 2 (IntervalRat.scale (701 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-21803988472 / 1000000000000) (-21803982112 / 1000000000000), orderedInterval (18367890098 / 1000000000000) (18367896458 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1809974217127171 / 4000000000000) 2 (IntervalRat.scale (701 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (29131338555 / 1000000000000) (29131338556 / 1000000000000), orderedInterval (23595749275 / 1000000000000) (23595749276 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3211831010305439 / 4000000000000) 2 (IntervalRat.scale (701 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-13615999165 / 1000000000000) (-13615999101 / 1000000000000), orderedInterval (24654940260 / 1000000000000) (24654940324 / 1000000000000)))) (orderedInterval (-12819011220 / 1000000000000) (-12819004898 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3000909157588091 / 4000000000000) 2 (IntervalRat.scale (701 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-4982189941 / 1000000000000) (-4982189940 / 1000000000000), orderedInterval (-28697675401 / 1000000000000) (-28697675400 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2141590374775403 / 4000000000000) 2 (IntervalRat.scale (701 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (29554608200 / 1000000000000) (29554698013 / 1000000000000), orderedInterval (-17792272259 / 1000000000000) (-17792182446 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2428335232211037 / 4000000000000) 2 (IntervalRat.scale (701 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-32369110854 / 1000000000000) (-32369110135 / 1000000000000), orderedInterval (-918080259 / 1000000000000) (-918079541 / 1000000000000)))) (orderedInterval (-7420499510 / 1000000000000) (-7420479533 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2024492749943053 / 4000000000000) 2 (IntervalRat.scale (701 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-31797065641 / 1000000000000) (-31797065639 / 1000000000000), orderedInterval (-15677879867 / 1000000000000) (-15677879866 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1788700741280113 / 4000000000000) 2 (IntervalRat.scale (701 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (36226665344 / 1000000000000) (36226674615 / 1000000000000), orderedInterval (-10589206362 / 1000000000000) (-10589197091 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (518435192783187 / 800000000000) 2 (IntervalRat.scale (701 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (31215058627 / 1000000000000) (31215062216 / 1000000000000), orderedInterval (-2850911242 / 1000000000000) (-2850907653 / 1000000000000)))) (orderedInterval (1406881009 / 1000000000000) (1406882262 / 1000000000000))) = true
  rfl'

theorem compactCertificate479_chunkChecks2_2 :
    compactCertificate479.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1434019026987689 / 4000000000000) 2 (IntervalRat.scale (701 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (38433391763 / 1000000000000) (38433391764 / 1000000000000), orderedInterval (17227516367 / 1000000000000) (17227516368 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1215633810503329 / 4000000000000) 2 (IntervalRat.scale (701 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (1878181294 / 1000000000000) (1878181297 / 1000000000000), orderedInterval (-45733277820 / 1000000000000) (-45733277817 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (760687194925387 / 4000000000000) 2 (IntervalRat.scale (701 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (36408472954 / 1000000000000) (36408491866 / 1000000000000), orderedInterval (-45062702134 / 1000000000000) (-45062683223 / 1000000000000)))) (orderedInterval (6163999704 / 1000000000000) (6163999964 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (409100103362229 / 4000000000000) 2 (IntervalRat.scale (701 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (45413448709 / 1000000000000) (45413463846 / 1000000000000), orderedInterval (-64737363724 / 1000000000000) (-64737348587 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1110786361933687 / 4000000000000) 2 (IntervalRat.scale (701 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (43101158531 / 1000000000000) (43101179006 / 1000000000000), orderedInterval (-20929188320 / 1000000000000) (-20929167845 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1516683813173399 / 4000000000000) 2 (IntervalRat.scale (701 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (7202288349 / 1000000000000) (7202288360 / 1000000000000), orderedInterval (-40346907242 / 1000000000000) (-40346907230 / 1000000000000)))) (orderedInterval (1319562159 / 1000000000000) (1319562514 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (641312805074613 / 4000000000000) 2 (IntervalRat.scale (701 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-49029237057 / 1000000000000) (-49029237056 / 1000000000000), orderedInterval (-39430661419 / 1000000000000) (-39430661418 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2606900948005973 / 4000000000000) 2 (IntervalRat.scale (701 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-25254820711 / 1000000000000) (-25254796429 / 1000000000000), orderedInterval (18431774105 / 1000000000000) (18431798386 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1741289018884507 / 4000000000000) 2 (IntervalRat.scale (701 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (20765354975 / 1000000000000) (20765356696 / 1000000000000), orderedInterval (-32136321611 / 1000000000000) (-32136319890 / 1000000000000)))) (orderedInterval (-1048920611 / 1000000000000) (-1048913066 / 1000000000000))) = true
  rfl'

theorem compactCertificate479_chunkChecks2 :
    compactCertificate479.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate479.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate479_chunkChecks2_0
    compactCertificate479_chunkChecks2_1 compactCertificate479_chunkChecks2_2

theorem compactCertificate479_chunkChecks3_0 :
    compactCertificate479.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (701 / 2) 3 (IntervalRat.scale (701 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-23117743274 / 1000000000000) (-23117740511 / 1000000000000), orderedInterval (35836463485 / 1000000000000) (35836466248 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1032706854478601 / 4000000000000) 3 (IntervalRat.scale (701 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (48462742465 / 1000000000000) (48462742469 / 1000000000000), orderedInterval (10731483796 / 1000000000000) (10731483799 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (333956178437033 / 800000000000) 3 (IntervalRat.scale (701 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-15153443491 / 1000000000000) (-15153443490 / 1000000000000), orderedInterval (-35973679180 / 1000000000000) (-35973679179 / 1000000000000)))) (orderedInterval (-10706836447 / 1000000000000) (-10706835311 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (301341284529307 / 4000000000000) 3 (IntervalRat.scale (701 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (60672050061 / 1000000000000) (60672050062 / 1000000000000), orderedInterval (68658240332 / 1000000000000) (68658240333 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (809445077403679 / 4000000000000) 3 (IntervalRat.scale (701 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (48859852203 / 1000000000000) (48859877999 / 1000000000000), orderedInterval (-27664613163 / 1000000000000) (-27664587367 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2197800844643043 / 4000000000000) 3 (IntervalRat.scale (701 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-15009786221 / 1000000000000) (-15009786220 / 1000000000000), orderedInterval (-30537205404 / 1000000000000) (-30537205403 / 1000000000000)))) (orderedInterval (-8151972481 / 1000000000000) (-8151972199 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1618890154808059 / 4000000000000) 3 (IntervalRat.scale (701 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-9511264788 / 1000000000000) (-9511264787 / 1000000000000), orderedInterval (-38491693773 / 1000000000000) (-38491693772 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2773995873362407 / 4000000000000) 3 (IntervalRat.scale (701 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (236026327 / 1000000000000) (236026328 / 1000000000000), orderedInterval (-30297477345 / 1000000000000) (-30297477344 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2043312805074613 / 4000000000000) 3 (IntervalRat.scale (701 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (15869699499 / 1000000000000) (15869699789 / 1000000000000), orderedInterval (-31549693266 / 1000000000000) (-31549692977 / 1000000000000)))) (orderedInterval (-4875817026 / 1000000000000) (-4875816893 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate479_chunkChecks3_1 :
    compactCertificate479.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3134967304454299 / 4000000000000) 3 (IntervalRat.scale (701 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-21803988472 / 1000000000000) (-21803982112 / 1000000000000), orderedInterval (18367890098 / 1000000000000) (18367896458 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1809974217127171 / 4000000000000) 3 (IntervalRat.scale (701 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (29131338555 / 1000000000000) (29131338556 / 1000000000000), orderedInterval (23595749275 / 1000000000000) (23595749276 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3211831010305439 / 4000000000000) 3 (IntervalRat.scale (701 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-13615999165 / 1000000000000) (-13615999101 / 1000000000000), orderedInterval (24654940260 / 1000000000000) (24654940324 / 1000000000000)))) (orderedInterval (-9374045427 / 1000000000000) (-9374031314 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3000909157588091 / 4000000000000) 3 (IntervalRat.scale (701 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-4982189941 / 1000000000000) (-4982189940 / 1000000000000), orderedInterval (-28697675401 / 1000000000000) (-28697675400 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2141590374775403 / 4000000000000) 3 (IntervalRat.scale (701 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (29554608200 / 1000000000000) (29554698013 / 1000000000000), orderedInterval (-17792272259 / 1000000000000) (-17792182446 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2428335232211037 / 4000000000000) 3 (IntervalRat.scale (701 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-32369110854 / 1000000000000) (-32369110135 / 1000000000000), orderedInterval (-918080259 / 1000000000000) (-918079541 / 1000000000000)))) (orderedInterval (913182387 / 1000000000000) (913212923 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2024492749943053 / 4000000000000) 3 (IntervalRat.scale (701 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-31797065641 / 1000000000000) (-31797065639 / 1000000000000), orderedInterval (-15677879867 / 1000000000000) (-15677879866 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1788700741280113 / 4000000000000) 3 (IntervalRat.scale (701 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (36226665344 / 1000000000000) (36226674615 / 1000000000000), orderedInterval (-10589206362 / 1000000000000) (-10589197091 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (518435192783187 / 800000000000) 3 (IntervalRat.scale (701 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (31215058627 / 1000000000000) (31215062216 / 1000000000000), orderedInterval (-2850911242 / 1000000000000) (-2850907653 / 1000000000000)))) (orderedInterval (-255974122 / 1000000000000) (-255972325 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate479_chunkChecks3_2 :
    compactCertificate479.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1434019026987689 / 4000000000000) 3 (IntervalRat.scale (701 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (38433391763 / 1000000000000) (38433391764 / 1000000000000), orderedInterval (17227516367 / 1000000000000) (17227516368 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1215633810503329 / 4000000000000) 3 (IntervalRat.scale (701 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (1878181294 / 1000000000000) (1878181297 / 1000000000000), orderedInterval (-45733277820 / 1000000000000) (-45733277817 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (760687194925387 / 4000000000000) 3 (IntervalRat.scale (701 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (36408472954 / 1000000000000) (36408491866 / 1000000000000), orderedInterval (-45062702134 / 1000000000000) (-45062683223 / 1000000000000)))) (orderedInterval (1476963798 / 1000000000000) (1476963973 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (409100103362229 / 4000000000000) 3 (IntervalRat.scale (701 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (45413448709 / 1000000000000) (45413463846 / 1000000000000), orderedInterval (-64737363724 / 1000000000000) (-64737348587 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1110786361933687 / 4000000000000) 3 (IntervalRat.scale (701 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (43101158531 / 1000000000000) (43101179006 / 1000000000000), orderedInterval (-20929188320 / 1000000000000) (-20929167845 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1516683813173399 / 4000000000000) 3 (IntervalRat.scale (701 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (7202288349 / 1000000000000) (7202288360 / 1000000000000), orderedInterval (-40346907242 / 1000000000000) (-40346907230 / 1000000000000)))) (orderedInterval (-4184291766 / 1000000000000) (-4184291487 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (641312805074613 / 4000000000000) 3 (IntervalRat.scale (701 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-49029237057 / 1000000000000) (-49029237056 / 1000000000000), orderedInterval (-39430661419 / 1000000000000) (-39430661418 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2606900948005973 / 4000000000000) 3 (IntervalRat.scale (701 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-25254820711 / 1000000000000) (-25254796429 / 1000000000000), orderedInterval (18431774105 / 1000000000000) (18431798386 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1741289018884507 / 4000000000000) 3 (IntervalRat.scale (701 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (20765354975 / 1000000000000) (20765356696 / 1000000000000), orderedInterval (-32136321611 / 1000000000000) (-32136319890 / 1000000000000)))) (orderedInterval (-1880636935 / 1000000000000) (-1880623278 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate479_chunkChecks3 :
    compactCertificate479.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate479.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate479_chunkChecks3_0
    compactCertificate479_chunkChecks3_1 compactCertificate479_chunkChecks3_2

theorem compactCertificate479_chunkChecks4_0 :
    compactCertificate479.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (701 / 2) 4 (IntervalRat.scale (701 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-23117743274 / 1000000000000) (-23117740511 / 1000000000000), orderedInterval (35836463485 / 1000000000000) (35836466248 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1032706854478601 / 4000000000000) 4 (IntervalRat.scale (701 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (48462742465 / 1000000000000) (48462742469 / 1000000000000), orderedInterval (10731483796 / 1000000000000) (10731483799 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (333956178437033 / 800000000000) 4 (IntervalRat.scale (701 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-15153443491 / 1000000000000) (-15153443490 / 1000000000000), orderedInterval (-35973679180 / 1000000000000) (-35973679179 / 1000000000000)))) (orderedInterval (-10758136204 / 1000000000000) (-10758135059 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (301341284529307 / 4000000000000) 4 (IntervalRat.scale (701 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (60672050061 / 1000000000000) (60672050062 / 1000000000000), orderedInterval (68658240332 / 1000000000000) (68658240333 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (809445077403679 / 4000000000000) 4 (IntervalRat.scale (701 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (48859852203 / 1000000000000) (48859877999 / 1000000000000), orderedInterval (-27664613163 / 1000000000000) (-27664587367 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2197800844643043 / 4000000000000) 4 (IntervalRat.scale (701 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-15009786221 / 1000000000000) (-15009786220 / 1000000000000), orderedInterval (-30537205404 / 1000000000000) (-30537205403 / 1000000000000)))) (orderedInterval (6687103822 / 1000000000000) (6687104081 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1618890154808059 / 4000000000000) 4 (IntervalRat.scale (701 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-9511264788 / 1000000000000) (-9511264787 / 1000000000000), orderedInterval (-38491693773 / 1000000000000) (-38491693772 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2773995873362407 / 4000000000000) 4 (IntervalRat.scale (701 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (236026327 / 1000000000000) (236026328 / 1000000000000), orderedInterval (-30297477345 / 1000000000000) (-30297477344 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2043312805074613 / 4000000000000) 4 (IntervalRat.scale (701 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (15869699499 / 1000000000000) (15869699789 / 1000000000000), orderedInterval (-31549693266 / 1000000000000) (-31549692977 / 1000000000000)))) (orderedInterval (1646684596 / 1000000000000) (1646684833 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate479_chunkChecks4_1 :
    compactCertificate479.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3134967304454299 / 4000000000000) 4 (IntervalRat.scale (701 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-21803988472 / 1000000000000) (-21803982112 / 1000000000000), orderedInterval (18367890098 / 1000000000000) (18367896458 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1809974217127171 / 4000000000000) 4 (IntervalRat.scale (701 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (29131338555 / 1000000000000) (29131338556 / 1000000000000), orderedInterval (23595749275 / 1000000000000) (23595749276 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3211831010305439 / 4000000000000) 4 (IntervalRat.scale (701 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-13615999165 / 1000000000000) (-13615999101 / 1000000000000), orderedInterval (24654940260 / 1000000000000) (24654940324 / 1000000000000)))) (orderedInterval (49593533031 / 1000000000000) (49593564610 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3000909157588091 / 4000000000000) 4 (IntervalRat.scale (701 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-4982189941 / 1000000000000) (-4982189940 / 1000000000000), orderedInterval (-28697675401 / 1000000000000) (-28697675400 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2141590374775403 / 4000000000000) 4 (IntervalRat.scale (701 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (29554608200 / 1000000000000) (29554698013 / 1000000000000), orderedInterval (-17792272259 / 1000000000000) (-17792182446 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2428335232211037 / 4000000000000) 4 (IntervalRat.scale (701 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-32369110854 / 1000000000000) (-32369110135 / 1000000000000), orderedInterval (-918080259 / 1000000000000) (-918079541 / 1000000000000)))) (orderedInterval (18572899754 / 1000000000000) (18572946530 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2024492749943053 / 4000000000000) 4 (IntervalRat.scale (701 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-31797065641 / 1000000000000) (-31797065639 / 1000000000000), orderedInterval (-15677879867 / 1000000000000) (-15677879866 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1788700741280113 / 4000000000000) 4 (IntervalRat.scale (701 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (36226665344 / 1000000000000) (36226674615 / 1000000000000), orderedInterval (-10589206362 / 1000000000000) (-10589197091 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (518435192783187 / 800000000000) 4 (IntervalRat.scale (701 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (31215058627 / 1000000000000) (31215062216 / 1000000000000), orderedInterval (-2850911242 / 1000000000000) (-2850907653 / 1000000000000)))) (orderedInterval (2252115595 / 1000000000000) (2252118261 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate479_chunkChecks4_2 :
    compactCertificate479.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1434019026987689 / 4000000000000) 4 (IntervalRat.scale (701 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (38433391763 / 1000000000000) (38433391764 / 1000000000000), orderedInterval (17227516367 / 1000000000000) (17227516368 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1215633810503329 / 4000000000000) 4 (IntervalRat.scale (701 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (1878181294 / 1000000000000) (1878181297 / 1000000000000), orderedInterval (-45733277820 / 1000000000000) (-45733277817 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (760687194925387 / 4000000000000) 4 (IntervalRat.scale (701 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (36408472954 / 1000000000000) (36408491866 / 1000000000000), orderedInterval (-45062702134 / 1000000000000) (-45062683223 / 1000000000000)))) (orderedInterval (-6691857609 / 1000000000000) (-6691857480 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (409100103362229 / 4000000000000) 4 (IntervalRat.scale (701 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (45413448709 / 1000000000000) (45413463846 / 1000000000000), orderedInterval (-64737363724 / 1000000000000) (-64737348587 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1110786361933687 / 4000000000000) 4 (IntervalRat.scale (701 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (43101158531 / 1000000000000) (43101179006 / 1000000000000), orderedInterval (-20929188320 / 1000000000000) (-20929167845 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1516683813173399 / 4000000000000) 4 (IntervalRat.scale (701 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (7202288349 / 1000000000000) (7202288360 / 1000000000000), orderedInterval (-40346907242 / 1000000000000) (-40346907230 / 1000000000000)))) (orderedInterval (-1123463502 / 1000000000000) (-1123463273 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (641312805074613 / 4000000000000) 4 (IntervalRat.scale (701 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-49029237057 / 1000000000000) (-49029237056 / 1000000000000), orderedInterval (-39430661419 / 1000000000000) (-39430661418 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2606900948005973 / 4000000000000) 4 (IntervalRat.scale (701 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-25254820711 / 1000000000000) (-25254796429 / 1000000000000), orderedInterval (18431774105 / 1000000000000) (18431798386 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1741289018884507 / 4000000000000) 4 (IntervalRat.scale (701 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (20765354975 / 1000000000000) (20765356696 / 1000000000000), orderedInterval (-32136321611 / 1000000000000) (-32136319890 / 1000000000000)))) (orderedInterval (15301266176 / 1000000000000) (15301291147 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate479_chunkChecks4 :
    compactCertificate479.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate479.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate479_chunkChecks4_0
    compactCertificate479_chunkChecks4_1 compactCertificate479_chunkChecks4_2

theorem compactCertificate479_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate479.chunkCheck r b = true :=
  compactCertificate479.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate479_chunkChecks0
    · exact compactCertificate479_chunkChecks1
    · exact compactCertificate479_chunkChecks2
    · exact compactCertificate479_chunkChecks3
    · exact compactCertificate479_chunkChecks4)

theorem compactCertificate479_coefficient0 :
    compactCertificate479.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate479_coefficient1 :
    compactCertificate479.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate479_coefficient2 :
    compactCertificate479.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate479_coefficient3 :
    compactCertificate479.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate479_coefficient4 :
    compactCertificate479.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate479_coefficients : ∀ r : Fin 5,
    compactCertificate479.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate479_coefficient0
  · exact compactCertificate479_coefficient1
  · exact compactCertificate479_coefficient2
  · exact compactCertificate479_coefficient3
  · exact compactCertificate479_coefficient4

theorem compactCertificate479_lower : (1 : ℚ) ≤ compactCertificate479.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate479, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate479_proves {t : ℝ} (ht : t ∈ compactCertificate479.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate479.proves compactCertificate479_states compactCertificate479_chunks
    compactCertificate479_coefficients compactCertificate479_lower ht

end Erdos232
