/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate458 : CompactCertificate where
  left := 329
  right := 330
  center := 659 / 2
  grid := fun i =>
    match i.val with
    | 0 => 105
    | 1 => 77
    | 2 => 125
    | 3 => 23
    | 4 => 61
    | 5 => 165
    | 6 => 121
    | 7 => 208
    | 8 => 153
    | 9 => 235
    | 10 => 135
    | 11 => 240
    | 12 => 225
    | 13 => 160
    | 14 => 182
    | 15 => 152
    | 16 => 134
    | 17 => 194
    | 18 => 107
    | 19 => 91
    | 20 => 57
    | 21 => 31
    | 22 => 83
    | 23 => 114
    | 24 => 48
    | 25 => 195
    | _ => 130
  point := fun i =>
    match i.val with
    | 0 => 659 / 2
    | 1 => 970832834666759 / 4000000000000
    | 2 => 313947391711847 / 800000000000
    | 3 => 283286599864213 / 4000000000000
    | 4 => 760947654791761 / 4000000000000
    | 5 => 2066120908159437 / 4000000000000
    | 6 => 1521895309584181 / 4000000000000
    | 7 => 2607793552847113 / 4000000000000
    | 8 => 1920888928023067 / 4000000000000
    | 9 => 2947137594344341 / 4000000000000
    | 10 => 1701530683433389 / 4000000000000
    | 11 => 3019396056763601 / 4000000000000
    | 12 => 2821111461983669 / 4000000000000
    | 13 => 2013278255316677 / 4000000000000
    | 14 => 2282842964375283 / 4000000000000
    | 15 => 1903196465353027 / 4000000000000
    | 16 => 1681531795297567 / 4000000000000
    | 17 => 487373455127133 / 800000000000
    | 18 => 1348100625941351 / 4000000000000
    | 19 => 1142799830416111 / 4000000000000
    | 20 => 715111071976933 / 4000000000000
    | 21 => 384589112861211 / 4000000000000
    | 22 => 1044234254656633 / 4000000000000
    | 23 => 1425812600401241 / 4000000000000
    | 24 => 602888928023067 / 4000000000000
    | 25 => 2450710021021307 / 4000000000000
    | _ => 1636960718181013 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-17834532883 / 1000000000000) (-17834532882 / 1000000000000), orderedInterval (-40147669713 / 1000000000000) (-40147669712 / 1000000000000))
    | 1 => (orderedInterval (-51205124056 / 1000000000000) (-51205123933 / 1000000000000), orderedInterval (1112370495 / 1000000000000) (1112370618 / 1000000000000))
    | 2 => (orderedInterval (-20021113788 / 1000000000000) (-20021113787 / 1000000000000), orderedInterval (-34922862584 / 1000000000000) (-34922862583 / 1000000000000))
    | 3 => (orderedInterval (57479045908 / 1000000000000) (57479071014 / 1000000000000), orderedInterval (-75806542309 / 1000000000000) (-75806517203 / 1000000000000))
    | 4 => (orderedInterval (33399647645 / 1000000000000) (33399657679 / 1000000000000), orderedInterval (-47320453934 / 1000000000000) (-47320443901 / 1000000000000))
    | 5 => (orderedInterval (30407015926 / 1000000000000) (30407128810 / 1000000000000), orderedInterval (-17576635385 / 1000000000000) (-17576522501 / 1000000000000))
    | 6 => (orderedInterval (-36928238822 / 1000000000000) (-36928238821 / 1000000000000), orderedInterval (-17545023177 / 1000000000000) (-17545023176 / 1000000000000))
    | 7 => (orderedInterval (-20550360412 / 1000000000000) (-20550357894 / 1000000000000), orderedInterval (23556591368 / 1000000000000) (23556593887 / 1000000000000))
    | 8 => (orderedInterval (-12268923993 / 1000000000000) (-12268923992 / 1000000000000), orderedInterval (-34267708371 / 1000000000000) (-34267708369 / 1000000000000))
    | 9 => (orderedInterval (19040877916 / 1000000000000) (19040879248 / 1000000000000), orderedInterval (-22407042476 / 1000000000000) (-22407041143 / 1000000000000))
    | 10 => (orderedInterval (-34278740394 / 1000000000000) (-34278686648 / 1000000000000), orderedInterval (17972093450 / 1000000000000) (17972147196 / 1000000000000))
    | 11 => (orderedInterval (28945171039 / 1000000000000) (28945176822 / 1000000000000), orderedInterval (-2375098989 / 1000000000000) (-2375093206 / 1000000000000))
    | 12 => (orderedInterval (21452903779 / 1000000000000) (21452908138 / 1000000000000), orderedInterval (-21049084172 / 1000000000000) (-21049079813 / 1000000000000))
    | 13 => (orderedInterval (35304974512 / 1000000000000) (35304974621 / 1000000000000), orderedInterval (4254480442 / 1000000000000) (4254480551 / 1000000000000))
    | 14 => (orderedInterval (-9035374480 / 1000000000000) (-9035374468 / 1000000000000), orderedInterval (32161426610 / 1000000000000) (32161426622 / 1000000000000))
    | 15 => (orderedInterval (-29492590869 / 1000000000000) (-29492537960 / 1000000000000), orderedInterval (21668653648 / 1000000000000) (21668706557 / 1000000000000))
    | 16 => (orderedInterval (7526459195 / 1000000000000) (7526459196 / 1000000000000), orderedInterval (38171330704 / 1000000000000) (38171330705 / 1000000000000))
    | 17 => (orderedInterval (16426581782 / 1000000000000) (16426581783 / 1000000000000), orderedInterval (27828001841 / 1000000000000) (27828001842 / 1000000000000))
    | 18 => (orderedInterval (-43289980871 / 1000000000000) (-43289980300 / 1000000000000), orderedInterval (3926084351 / 1000000000000) (3926084923 / 1000000000000))
    | 19 => (orderedInterval (-26653226308 / 1000000000000) (-26653226307 / 1000000000000), orderedInterval (-38913433097 / 1000000000000) (-38913433096 / 1000000000000))
    | 20 => (orderedInterval (-28172671812 / 1000000000000) (-28172671811 / 1000000000000), orderedInterval (-52526001868 / 1000000000000) (-52526001867 / 1000000000000))
    | 21 => (orderedInterval (35978217936 / 1000000000000) (35978221112 / 1000000000000), orderedInterval (-73172848962 / 1000000000000) (-73172845786 / 1000000000000))
    | 22 => (orderedInterval (-43813101791 / 1000000000000) (-43813101790 / 1000000000000), orderedInterval (-22698065253 / 1000000000000) (-22698065252 / 1000000000000))
    | 23 => (orderedInterval (-33192331013 / 1000000000000) (-33192264689 / 1000000000000), orderedInterval (26204799062 / 1000000000000) (26204865385 / 1000000000000))
    | 24 => (orderedInterval (42380453778 / 1000000000000) (42380453779 / 1000000000000), orderedInterval (49131058974 / 1000000000000) (49131058975 / 1000000000000))
    | 25 => (orderedInterval (-24262620922 / 1000000000000) (-24262620921 / 1000000000000), orderedInterval (-21202906018 / 1000000000000) (-21202906017 / 1000000000000))
    | _ => (orderedInterval (39396901288 / 1000000000000) (39396901825 / 1000000000000), orderedInterval (-1918171676 / 1000000000000) (-1918171139 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-8720978712 / 1000000000000) (-8720978687 / 1000000000000)
      | 1 => orderedInterval (-1565759607 / 1000000000000) (-1565750904 / 1000000000000)
      | 2 => orderedInterval (337339564 / 1000000000000) (337339660 / 1000000000000)
      | 3 => orderedInterval (-1808380383 / 1000000000000) (-1808375212 / 1000000000000)
      | 4 => orderedInterval (2996972558 / 1000000000000) (2996972686 / 1000000000000)
      | 5 => orderedInterval (-350699594 / 1000000000000) (-350698950 / 1000000000000)
      | 6 => orderedInterval (7513143093 / 1000000000000) (7513143268 / 1000000000000)
      | 7 => orderedInterval (2873457370 / 1000000000000) (2873462552 / 1000000000000)
      | _ => orderedInterval (-5161400176 / 1000000000000) (-5161399984 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-18346226553 / 1000000000000) (-18346226525 / 1000000000000)
      | 1 => orderedInterval (1138008376 / 1000000000000) (1138021271 / 1000000000000)
      | 2 => orderedInterval (-2644625946 / 1000000000000) (-2644625760 / 1000000000000)
      | 3 => orderedInterval (9848400566 / 1000000000000) (9848408391 / 1000000000000)
      | 4 => orderedInterval (1146019420 / 1000000000000) (1146019668 / 1000000000000)
      | 5 => orderedInterval (-1108241362 / 1000000000000) (-1108240434 / 1000000000000)
      | 6 => orderedInterval (339836407 / 1000000000000) (339836578 / 1000000000000)
      | 7 => orderedInterval (-1370344168 / 1000000000000) (-1370338616 / 1000000000000)
      | _ => orderedInterval (3791743227 / 1000000000000) (3791743481 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (9050059492 / 1000000000000) (9050059523 / 1000000000000)
      | 1 => orderedInterval (4930895213 / 1000000000000) (4930915170 / 1000000000000)
      | 2 => orderedInterval (-1843597966 / 1000000000000) (-1843597603 / 1000000000000)
      | 3 => orderedInterval (-475132305 / 1000000000000) (-475119567 / 1000000000000)
      | 4 => orderedInterval (-6156194064 / 1000000000000) (-6156193573 / 1000000000000)
      | 5 => orderedInterval (-23179040 / 1000000000000) (-23177695 / 1000000000000)
      | 6 => orderedInterval (-8106703008 / 1000000000000) (-8106702839 / 1000000000000)
      | 7 => orderedInterval (-3540230498 / 1000000000000) (-3540224492 / 1000000000000)
      | _ => orderedInterval (4509096228 / 1000000000000) (4509096574 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (19343478718 / 1000000000000) (19343478754 / 1000000000000)
      | 1 => orderedInterval (-4504137730 / 1000000000000) (-4504106589 / 1000000000000)
      | 2 => orderedInterval (8197418214 / 1000000000000) (8197418921 / 1000000000000)
      | 3 => orderedInterval (-43318297358 / 1000000000000) (-43318274949 / 1000000000000)
      | 4 => orderedInterval (-4296032181 / 1000000000000) (-4296031192 / 1000000000000)
      | 5 => orderedInterval (-720396683 / 1000000000000) (-720394734 / 1000000000000)
      | 6 => orderedInterval (-466266215 / 1000000000000) (-466266046 / 1000000000000)
      | 7 => orderedInterval (2263620208 / 1000000000000) (2263626700 / 1000000000000)
      | _ => orderedInterval (-11827328209 / 1000000000000) (-11827327723 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-9690691969 / 1000000000000) (-9690691928 / 1000000000000)
      | 1 => orderedInterval (-12892431298 / 1000000000000) (-12892382463 / 1000000000000)
      | 2 => orderedInterval (8326933061 / 1000000000000) (8326934448 / 1000000000000)
      | 3 => orderedInterval (21958504285 / 1000000000000) (21958546858 / 1000000000000)
      | 4 => orderedInterval (10484658808 / 1000000000000) (10484660832 / 1000000000000)
      | 5 => orderedInterval (2297424706 / 1000000000000) (2297427540 / 1000000000000)
      | 6 => orderedInterval (8352000371 / 1000000000000) (8352000541 / 1000000000000)
      | 7 => orderedInterval (3857038456 / 1000000000000) (3857045495 / 1000000000000)
      | _ => orderedInterval (6102754664 / 1000000000000) (6102755375 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-3886305887 / 1000000000000) (-3886285571 / 1000000000000)
    | 1 => orderedInterval (-7205430033 / 1000000000000) (-7205401946 / 1000000000000)
    | 2 => orderedInterval (-1654985948 / 1000000000000) (-1654944502 / 1000000000000)
    | 3 => orderedInterval (-35327941236 / 1000000000000) (-35327876858 / 1000000000000)
    | _ => orderedInterval (38796191084 / 1000000000000) (38796296698 / 1000000000000)

theorem compactCertificate458_stateChecks0 :
    compactCertificate458.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 105 12 (659 / 2)) (orderedInterval (-17834532883 / 1000000000000) (-17834532882 / 1000000000000), orderedInterval (-40147669713 / 1000000000000) (-40147669712 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 77 12 (970832834666759 / 4000000000000)) (orderedInterval (-51205124056 / 1000000000000) (-51205123933 / 1000000000000), orderedInterval (1112370495 / 1000000000000) (1112370618 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 125 12 (313947391711847 / 800000000000)) (orderedInterval (-20021113788 / 1000000000000) (-20021113787 / 1000000000000), orderedInterval (-34922862584 / 1000000000000) (-34922862583 / 1000000000000))) = true
  rfl'

theorem compactCertificate458_stateChecks1 :
    compactCertificate458.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 23 12 (283286599864213 / 4000000000000)) (orderedInterval (57479045908 / 1000000000000) (57479071014 / 1000000000000), orderedInterval (-75806542309 / 1000000000000) (-75806517203 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 61 12 (760947654791761 / 4000000000000)) (orderedInterval (33399647645 / 1000000000000) (33399657679 / 1000000000000), orderedInterval (-47320453934 / 1000000000000) (-47320443901 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 165 12 (2066120908159437 / 4000000000000)) (orderedInterval (30407015926 / 1000000000000) (30407128810 / 1000000000000), orderedInterval (-17576635385 / 1000000000000) (-17576522501 / 1000000000000))) = true
  rfl'

theorem compactCertificate458_stateChecks2 :
    compactCertificate458.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 121 12 (1521895309584181 / 4000000000000)) (orderedInterval (-36928238822 / 1000000000000) (-36928238821 / 1000000000000), orderedInterval (-17545023177 / 1000000000000) (-17545023176 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 208 12 (2607793552847113 / 4000000000000)) (orderedInterval (-20550360412 / 1000000000000) (-20550357894 / 1000000000000), orderedInterval (23556591368 / 1000000000000) (23556593887 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 153 12 (1920888928023067 / 4000000000000)) (orderedInterval (-12268923993 / 1000000000000) (-12268923992 / 1000000000000), orderedInterval (-34267708371 / 1000000000000) (-34267708369 / 1000000000000))) = true
  rfl'

theorem compactCertificate458_stateChecks3 :
    compactCertificate458.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 235 12 (2947137594344341 / 4000000000000)) (orderedInterval (19040877916 / 1000000000000) (19040879248 / 1000000000000), orderedInterval (-22407042476 / 1000000000000) (-22407041143 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 135 12 (1701530683433389 / 4000000000000)) (orderedInterval (-34278740394 / 1000000000000) (-34278686648 / 1000000000000), orderedInterval (17972093450 / 1000000000000) (17972147196 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 240 12 (3019396056763601 / 4000000000000)) (orderedInterval (28945171039 / 1000000000000) (28945176822 / 1000000000000), orderedInterval (-2375098989 / 1000000000000) (-2375093206 / 1000000000000))) = true
  rfl'

theorem compactCertificate458_stateChecks4 :
    compactCertificate458.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 225 12 (2821111461983669 / 4000000000000)) (orderedInterval (21452903779 / 1000000000000) (21452908138 / 1000000000000), orderedInterval (-21049084172 / 1000000000000) (-21049079813 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 160 12 (2013278255316677 / 4000000000000)) (orderedInterval (35304974512 / 1000000000000) (35304974621 / 1000000000000), orderedInterval (4254480442 / 1000000000000) (4254480551 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 182 12 (2282842964375283 / 4000000000000)) (orderedInterval (-9035374480 / 1000000000000) (-9035374468 / 1000000000000), orderedInterval (32161426610 / 1000000000000) (32161426622 / 1000000000000))) = true
  rfl'

theorem compactCertificate458_stateChecks5 :
    compactCertificate458.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 152 12 (1903196465353027 / 4000000000000)) (orderedInterval (-29492590869 / 1000000000000) (-29492537960 / 1000000000000), orderedInterval (21668653648 / 1000000000000) (21668706557 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 134 12 (1681531795297567 / 4000000000000)) (orderedInterval (7526459195 / 1000000000000) (7526459196 / 1000000000000), orderedInterval (38171330704 / 1000000000000) (38171330705 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 194 12 (487373455127133 / 800000000000)) (orderedInterval (16426581782 / 1000000000000) (16426581783 / 1000000000000), orderedInterval (27828001841 / 1000000000000) (27828001842 / 1000000000000))) = true
  rfl'

theorem compactCertificate458_stateChecks6 :
    compactCertificate458.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 107 12 (1348100625941351 / 4000000000000)) (orderedInterval (-43289980871 / 1000000000000) (-43289980300 / 1000000000000), orderedInterval (3926084351 / 1000000000000) (3926084923 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 91 12 (1142799830416111 / 4000000000000)) (orderedInterval (-26653226308 / 1000000000000) (-26653226307 / 1000000000000), orderedInterval (-38913433097 / 1000000000000) (-38913433096 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 57 12 (715111071976933 / 4000000000000)) (orderedInterval (-28172671812 / 1000000000000) (-28172671811 / 1000000000000), orderedInterval (-52526001868 / 1000000000000) (-52526001867 / 1000000000000))) = true
  rfl'

theorem compactCertificate458_stateChecks7 :
    compactCertificate458.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 31 12 (384589112861211 / 4000000000000)) (orderedInterval (35978217936 / 1000000000000) (35978221112 / 1000000000000), orderedInterval (-73172848962 / 1000000000000) (-73172845786 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 83 12 (1044234254656633 / 4000000000000)) (orderedInterval (-43813101791 / 1000000000000) (-43813101790 / 1000000000000), orderedInterval (-22698065253 / 1000000000000) (-22698065252 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 114 12 (1425812600401241 / 4000000000000)) (orderedInterval (-33192331013 / 1000000000000) (-33192264689 / 1000000000000), orderedInterval (26204799062 / 1000000000000) (26204865385 / 1000000000000))) = true
  rfl'

theorem compactCertificate458_stateChecks8 :
    compactCertificate458.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 48 12 (602888928023067 / 4000000000000)) (orderedInterval (42380453778 / 1000000000000) (42380453779 / 1000000000000), orderedInterval (49131058974 / 1000000000000) (49131058975 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 195 12 (2450710021021307 / 4000000000000)) (orderedInterval (-24262620922 / 1000000000000) (-24262620921 / 1000000000000), orderedInterval (-21202906018 / 1000000000000) (-21202906017 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 130 12 (1636960718181013 / 4000000000000)) (orderedInterval (39396901288 / 1000000000000) (39396901825 / 1000000000000), orderedInterval (-1918171676 / 1000000000000) (-1918171139 / 1000000000000))) = true
  rfl'

theorem compactCertificate458_states : ∀ j,
    BesselStateValid (compactCertificate458.point j) (compactCertificate458.state j) :=
  compactCertificate458.statesValid_of_checks3 compactCertificate458_stateChecks0
    compactCertificate458_stateChecks1 compactCertificate458_stateChecks2
    compactCertificate458_stateChecks3 compactCertificate458_stateChecks4
    compactCertificate458_stateChecks5 compactCertificate458_stateChecks6
    compactCertificate458_stateChecks7 compactCertificate458_stateChecks8

theorem compactCertificate458_chunkChecks0_0 :
    compactCertificate458.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (659 / 2) 0 (IntervalRat.scale (659 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-17834532883 / 1000000000000) (-17834532882 / 1000000000000), orderedInterval (-40147669713 / 1000000000000) (-40147669712 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (970832834666759 / 4000000000000) 0 (IntervalRat.scale (659 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-51205124056 / 1000000000000) (-51205123933 / 1000000000000), orderedInterval (1112370495 / 1000000000000) (1112370618 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (313947391711847 / 800000000000) 0 (IntervalRat.scale (659 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-20021113788 / 1000000000000) (-20021113787 / 1000000000000), orderedInterval (-34922862584 / 1000000000000) (-34922862583 / 1000000000000)))) (orderedInterval (-8720978712 / 1000000000000) (-8720978687 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (283286599864213 / 4000000000000) 0 (IntervalRat.scale (659 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (57479045908 / 1000000000000) (57479071014 / 1000000000000), orderedInterval (-75806542309 / 1000000000000) (-75806517203 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (760947654791761 / 4000000000000) 0 (IntervalRat.scale (659 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (33399647645 / 1000000000000) (33399657679 / 1000000000000), orderedInterval (-47320453934 / 1000000000000) (-47320443901 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2066120908159437 / 4000000000000) 0 (IntervalRat.scale (659 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30407015926 / 1000000000000) (30407128810 / 1000000000000), orderedInterval (-17576635385 / 1000000000000) (-17576522501 / 1000000000000)))) (orderedInterval (-1565759607 / 1000000000000) (-1565750904 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1521895309584181 / 4000000000000) 0 (IntervalRat.scale (659 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-36928238822 / 1000000000000) (-36928238821 / 1000000000000), orderedInterval (-17545023177 / 1000000000000) (-17545023176 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2607793552847113 / 4000000000000) 0 (IntervalRat.scale (659 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-20550360412 / 1000000000000) (-20550357894 / 1000000000000), orderedInterval (23556591368 / 1000000000000) (23556593887 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (1920888928023067 / 4000000000000) 0 (IntervalRat.scale (659 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-12268923993 / 1000000000000) (-12268923992 / 1000000000000), orderedInterval (-34267708371 / 1000000000000) (-34267708369 / 1000000000000)))) (orderedInterval (337339564 / 1000000000000) (337339660 / 1000000000000))) = true
  rfl'

theorem compactCertificate458_chunkChecks0_1 :
    compactCertificate458.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (2947137594344341 / 4000000000000) 0 (IntervalRat.scale (659 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (19040877916 / 1000000000000) (19040879248 / 1000000000000), orderedInterval (-22407042476 / 1000000000000) (-22407041143 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1701530683433389 / 4000000000000) 0 (IntervalRat.scale (659 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-34278740394 / 1000000000000) (-34278686648 / 1000000000000), orderedInterval (17972093450 / 1000000000000) (17972147196 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3019396056763601 / 4000000000000) 0 (IntervalRat.scale (659 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (28945171039 / 1000000000000) (28945176822 / 1000000000000), orderedInterval (-2375098989 / 1000000000000) (-2375093206 / 1000000000000)))) (orderedInterval (-1808380383 / 1000000000000) (-1808375212 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (2821111461983669 / 4000000000000) 0 (IntervalRat.scale (659 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (21452903779 / 1000000000000) (21452908138 / 1000000000000), orderedInterval (-21049084172 / 1000000000000) (-21049079813 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2013278255316677 / 4000000000000) 0 (IntervalRat.scale (659 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (35304974512 / 1000000000000) (35304974621 / 1000000000000), orderedInterval (4254480442 / 1000000000000) (4254480551 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2282842964375283 / 4000000000000) 0 (IntervalRat.scale (659 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-9035374480 / 1000000000000) (-9035374468 / 1000000000000), orderedInterval (32161426610 / 1000000000000) (32161426622 / 1000000000000)))) (orderedInterval (2996972558 / 1000000000000) (2996972686 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (1903196465353027 / 4000000000000) 0 (IntervalRat.scale (659 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-29492590869 / 1000000000000) (-29492537960 / 1000000000000), orderedInterval (21668653648 / 1000000000000) (21668706557 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1681531795297567 / 4000000000000) 0 (IntervalRat.scale (659 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (7526459195 / 1000000000000) (7526459196 / 1000000000000), orderedInterval (38171330704 / 1000000000000) (38171330705 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (487373455127133 / 800000000000) 0 (IntervalRat.scale (659 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16426581782 / 1000000000000) (16426581783 / 1000000000000), orderedInterval (27828001841 / 1000000000000) (27828001842 / 1000000000000)))) (orderedInterval (-350699594 / 1000000000000) (-350698950 / 1000000000000))) = true
  rfl'

theorem compactCertificate458_chunkChecks0_2 :
    compactCertificate458.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1348100625941351 / 4000000000000) 0 (IntervalRat.scale (659 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-43289980871 / 1000000000000) (-43289980300 / 1000000000000), orderedInterval (3926084351 / 1000000000000) (3926084923 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1142799830416111 / 4000000000000) 0 (IntervalRat.scale (659 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-26653226308 / 1000000000000) (-26653226307 / 1000000000000), orderedInterval (-38913433097 / 1000000000000) (-38913433096 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (715111071976933 / 4000000000000) 0 (IntervalRat.scale (659 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-28172671812 / 1000000000000) (-28172671811 / 1000000000000), orderedInterval (-52526001868 / 1000000000000) (-52526001867 / 1000000000000)))) (orderedInterval (7513143093 / 1000000000000) (7513143268 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (384589112861211 / 4000000000000) 0 (IntervalRat.scale (659 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (35978217936 / 1000000000000) (35978221112 / 1000000000000), orderedInterval (-73172848962 / 1000000000000) (-73172845786 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1044234254656633 / 4000000000000) 0 (IntervalRat.scale (659 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-43813101791 / 1000000000000) (-43813101790 / 1000000000000), orderedInterval (-22698065253 / 1000000000000) (-22698065252 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1425812600401241 / 4000000000000) 0 (IntervalRat.scale (659 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-33192331013 / 1000000000000) (-33192264689 / 1000000000000), orderedInterval (26204799062 / 1000000000000) (26204865385 / 1000000000000)))) (orderedInterval (2873457370 / 1000000000000) (2873462552 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (602888928023067 / 4000000000000) 0 (IntervalRat.scale (659 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (42380453778 / 1000000000000) (42380453779 / 1000000000000), orderedInterval (49131058974 / 1000000000000) (49131058975 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2450710021021307 / 4000000000000) 0 (IntervalRat.scale (659 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-24262620922 / 1000000000000) (-24262620921 / 1000000000000), orderedInterval (-21202906018 / 1000000000000) (-21202906017 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1636960718181013 / 4000000000000) 0 (IntervalRat.scale (659 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (39396901288 / 1000000000000) (39396901825 / 1000000000000), orderedInterval (-1918171676 / 1000000000000) (-1918171139 / 1000000000000)))) (orderedInterval (-5161400176 / 1000000000000) (-5161399984 / 1000000000000))) = true
  rfl'

theorem compactCertificate458_chunkChecks0 :
    compactCertificate458.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate458.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate458_chunkChecks0_0
    compactCertificate458_chunkChecks0_1 compactCertificate458_chunkChecks0_2

theorem compactCertificate458_chunkChecks1_0 :
    compactCertificate458.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (659 / 2) 1 (IntervalRat.scale (659 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-17834532883 / 1000000000000) (-17834532882 / 1000000000000), orderedInterval (-40147669713 / 1000000000000) (-40147669712 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (970832834666759 / 4000000000000) 1 (IntervalRat.scale (659 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-51205124056 / 1000000000000) (-51205123933 / 1000000000000), orderedInterval (1112370495 / 1000000000000) (1112370618 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (313947391711847 / 800000000000) 1 (IntervalRat.scale (659 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-20021113788 / 1000000000000) (-20021113787 / 1000000000000), orderedInterval (-34922862584 / 1000000000000) (-34922862583 / 1000000000000)))) (orderedInterval (-18346226553 / 1000000000000) (-18346226525 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (283286599864213 / 4000000000000) 1 (IntervalRat.scale (659 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (57479045908 / 1000000000000) (57479071014 / 1000000000000), orderedInterval (-75806542309 / 1000000000000) (-75806517203 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (760947654791761 / 4000000000000) 1 (IntervalRat.scale (659 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (33399647645 / 1000000000000) (33399657679 / 1000000000000), orderedInterval (-47320453934 / 1000000000000) (-47320443901 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2066120908159437 / 4000000000000) 1 (IntervalRat.scale (659 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30407015926 / 1000000000000) (30407128810 / 1000000000000), orderedInterval (-17576635385 / 1000000000000) (-17576522501 / 1000000000000)))) (orderedInterval (1138008376 / 1000000000000) (1138021271 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1521895309584181 / 4000000000000) 1 (IntervalRat.scale (659 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-36928238822 / 1000000000000) (-36928238821 / 1000000000000), orderedInterval (-17545023177 / 1000000000000) (-17545023176 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2607793552847113 / 4000000000000) 1 (IntervalRat.scale (659 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-20550360412 / 1000000000000) (-20550357894 / 1000000000000), orderedInterval (23556591368 / 1000000000000) (23556593887 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (1920888928023067 / 4000000000000) 1 (IntervalRat.scale (659 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-12268923993 / 1000000000000) (-12268923992 / 1000000000000), orderedInterval (-34267708371 / 1000000000000) (-34267708369 / 1000000000000)))) (orderedInterval (-2644625946 / 1000000000000) (-2644625760 / 1000000000000))) = true
  rfl'

theorem compactCertificate458_chunkChecks1_1 :
    compactCertificate458.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (2947137594344341 / 4000000000000) 1 (IntervalRat.scale (659 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (19040877916 / 1000000000000) (19040879248 / 1000000000000), orderedInterval (-22407042476 / 1000000000000) (-22407041143 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1701530683433389 / 4000000000000) 1 (IntervalRat.scale (659 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-34278740394 / 1000000000000) (-34278686648 / 1000000000000), orderedInterval (17972093450 / 1000000000000) (17972147196 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3019396056763601 / 4000000000000) 1 (IntervalRat.scale (659 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (28945171039 / 1000000000000) (28945176822 / 1000000000000), orderedInterval (-2375098989 / 1000000000000) (-2375093206 / 1000000000000)))) (orderedInterval (9848400566 / 1000000000000) (9848408391 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (2821111461983669 / 4000000000000) 1 (IntervalRat.scale (659 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (21452903779 / 1000000000000) (21452908138 / 1000000000000), orderedInterval (-21049084172 / 1000000000000) (-21049079813 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2013278255316677 / 4000000000000) 1 (IntervalRat.scale (659 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (35304974512 / 1000000000000) (35304974621 / 1000000000000), orderedInterval (4254480442 / 1000000000000) (4254480551 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2282842964375283 / 4000000000000) 1 (IntervalRat.scale (659 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-9035374480 / 1000000000000) (-9035374468 / 1000000000000), orderedInterval (32161426610 / 1000000000000) (32161426622 / 1000000000000)))) (orderedInterval (1146019420 / 1000000000000) (1146019668 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (1903196465353027 / 4000000000000) 1 (IntervalRat.scale (659 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-29492590869 / 1000000000000) (-29492537960 / 1000000000000), orderedInterval (21668653648 / 1000000000000) (21668706557 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1681531795297567 / 4000000000000) 1 (IntervalRat.scale (659 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (7526459195 / 1000000000000) (7526459196 / 1000000000000), orderedInterval (38171330704 / 1000000000000) (38171330705 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (487373455127133 / 800000000000) 1 (IntervalRat.scale (659 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16426581782 / 1000000000000) (16426581783 / 1000000000000), orderedInterval (27828001841 / 1000000000000) (27828001842 / 1000000000000)))) (orderedInterval (-1108241362 / 1000000000000) (-1108240434 / 1000000000000))) = true
  rfl'

theorem compactCertificate458_chunkChecks1_2 :
    compactCertificate458.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1348100625941351 / 4000000000000) 1 (IntervalRat.scale (659 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-43289980871 / 1000000000000) (-43289980300 / 1000000000000), orderedInterval (3926084351 / 1000000000000) (3926084923 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1142799830416111 / 4000000000000) 1 (IntervalRat.scale (659 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-26653226308 / 1000000000000) (-26653226307 / 1000000000000), orderedInterval (-38913433097 / 1000000000000) (-38913433096 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (715111071976933 / 4000000000000) 1 (IntervalRat.scale (659 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-28172671812 / 1000000000000) (-28172671811 / 1000000000000), orderedInterval (-52526001868 / 1000000000000) (-52526001867 / 1000000000000)))) (orderedInterval (339836407 / 1000000000000) (339836578 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (384589112861211 / 4000000000000) 1 (IntervalRat.scale (659 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (35978217936 / 1000000000000) (35978221112 / 1000000000000), orderedInterval (-73172848962 / 1000000000000) (-73172845786 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1044234254656633 / 4000000000000) 1 (IntervalRat.scale (659 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-43813101791 / 1000000000000) (-43813101790 / 1000000000000), orderedInterval (-22698065253 / 1000000000000) (-22698065252 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1425812600401241 / 4000000000000) 1 (IntervalRat.scale (659 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-33192331013 / 1000000000000) (-33192264689 / 1000000000000), orderedInterval (26204799062 / 1000000000000) (26204865385 / 1000000000000)))) (orderedInterval (-1370344168 / 1000000000000) (-1370338616 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (602888928023067 / 4000000000000) 1 (IntervalRat.scale (659 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (42380453778 / 1000000000000) (42380453779 / 1000000000000), orderedInterval (49131058974 / 1000000000000) (49131058975 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2450710021021307 / 4000000000000) 1 (IntervalRat.scale (659 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-24262620922 / 1000000000000) (-24262620921 / 1000000000000), orderedInterval (-21202906018 / 1000000000000) (-21202906017 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1636960718181013 / 4000000000000) 1 (IntervalRat.scale (659 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (39396901288 / 1000000000000) (39396901825 / 1000000000000), orderedInterval (-1918171676 / 1000000000000) (-1918171139 / 1000000000000)))) (orderedInterval (3791743227 / 1000000000000) (3791743481 / 1000000000000))) = true
  rfl'

theorem compactCertificate458_chunkChecks1 :
    compactCertificate458.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate458.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate458_chunkChecks1_0
    compactCertificate458_chunkChecks1_1 compactCertificate458_chunkChecks1_2

theorem compactCertificate458_chunkChecks2_0 :
    compactCertificate458.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (659 / 2) 2 (IntervalRat.scale (659 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-17834532883 / 1000000000000) (-17834532882 / 1000000000000), orderedInterval (-40147669713 / 1000000000000) (-40147669712 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (970832834666759 / 4000000000000) 2 (IntervalRat.scale (659 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-51205124056 / 1000000000000) (-51205123933 / 1000000000000), orderedInterval (1112370495 / 1000000000000) (1112370618 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (313947391711847 / 800000000000) 2 (IntervalRat.scale (659 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-20021113788 / 1000000000000) (-20021113787 / 1000000000000), orderedInterval (-34922862584 / 1000000000000) (-34922862583 / 1000000000000)))) (orderedInterval (9050059492 / 1000000000000) (9050059523 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (283286599864213 / 4000000000000) 2 (IntervalRat.scale (659 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (57479045908 / 1000000000000) (57479071014 / 1000000000000), orderedInterval (-75806542309 / 1000000000000) (-75806517203 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (760947654791761 / 4000000000000) 2 (IntervalRat.scale (659 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (33399647645 / 1000000000000) (33399657679 / 1000000000000), orderedInterval (-47320453934 / 1000000000000) (-47320443901 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2066120908159437 / 4000000000000) 2 (IntervalRat.scale (659 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30407015926 / 1000000000000) (30407128810 / 1000000000000), orderedInterval (-17576635385 / 1000000000000) (-17576522501 / 1000000000000)))) (orderedInterval (4930895213 / 1000000000000) (4930915170 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1521895309584181 / 4000000000000) 2 (IntervalRat.scale (659 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-36928238822 / 1000000000000) (-36928238821 / 1000000000000), orderedInterval (-17545023177 / 1000000000000) (-17545023176 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2607793552847113 / 4000000000000) 2 (IntervalRat.scale (659 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-20550360412 / 1000000000000) (-20550357894 / 1000000000000), orderedInterval (23556591368 / 1000000000000) (23556593887 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (1920888928023067 / 4000000000000) 2 (IntervalRat.scale (659 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-12268923993 / 1000000000000) (-12268923992 / 1000000000000), orderedInterval (-34267708371 / 1000000000000) (-34267708369 / 1000000000000)))) (orderedInterval (-1843597966 / 1000000000000) (-1843597603 / 1000000000000))) = true
  rfl'

theorem compactCertificate458_chunkChecks2_1 :
    compactCertificate458.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (2947137594344341 / 4000000000000) 2 (IntervalRat.scale (659 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (19040877916 / 1000000000000) (19040879248 / 1000000000000), orderedInterval (-22407042476 / 1000000000000) (-22407041143 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1701530683433389 / 4000000000000) 2 (IntervalRat.scale (659 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-34278740394 / 1000000000000) (-34278686648 / 1000000000000), orderedInterval (17972093450 / 1000000000000) (17972147196 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3019396056763601 / 4000000000000) 2 (IntervalRat.scale (659 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (28945171039 / 1000000000000) (28945176822 / 1000000000000), orderedInterval (-2375098989 / 1000000000000) (-2375093206 / 1000000000000)))) (orderedInterval (-475132305 / 1000000000000) (-475119567 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (2821111461983669 / 4000000000000) 2 (IntervalRat.scale (659 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (21452903779 / 1000000000000) (21452908138 / 1000000000000), orderedInterval (-21049084172 / 1000000000000) (-21049079813 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2013278255316677 / 4000000000000) 2 (IntervalRat.scale (659 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (35304974512 / 1000000000000) (35304974621 / 1000000000000), orderedInterval (4254480442 / 1000000000000) (4254480551 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2282842964375283 / 4000000000000) 2 (IntervalRat.scale (659 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-9035374480 / 1000000000000) (-9035374468 / 1000000000000), orderedInterval (32161426610 / 1000000000000) (32161426622 / 1000000000000)))) (orderedInterval (-6156194064 / 1000000000000) (-6156193573 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (1903196465353027 / 4000000000000) 2 (IntervalRat.scale (659 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-29492590869 / 1000000000000) (-29492537960 / 1000000000000), orderedInterval (21668653648 / 1000000000000) (21668706557 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1681531795297567 / 4000000000000) 2 (IntervalRat.scale (659 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (7526459195 / 1000000000000) (7526459196 / 1000000000000), orderedInterval (38171330704 / 1000000000000) (38171330705 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (487373455127133 / 800000000000) 2 (IntervalRat.scale (659 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16426581782 / 1000000000000) (16426581783 / 1000000000000), orderedInterval (27828001841 / 1000000000000) (27828001842 / 1000000000000)))) (orderedInterval (-23179040 / 1000000000000) (-23177695 / 1000000000000))) = true
  rfl'

theorem compactCertificate458_chunkChecks2_2 :
    compactCertificate458.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1348100625941351 / 4000000000000) 2 (IntervalRat.scale (659 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-43289980871 / 1000000000000) (-43289980300 / 1000000000000), orderedInterval (3926084351 / 1000000000000) (3926084923 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1142799830416111 / 4000000000000) 2 (IntervalRat.scale (659 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-26653226308 / 1000000000000) (-26653226307 / 1000000000000), orderedInterval (-38913433097 / 1000000000000) (-38913433096 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (715111071976933 / 4000000000000) 2 (IntervalRat.scale (659 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-28172671812 / 1000000000000) (-28172671811 / 1000000000000), orderedInterval (-52526001868 / 1000000000000) (-52526001867 / 1000000000000)))) (orderedInterval (-8106703008 / 1000000000000) (-8106702839 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (384589112861211 / 4000000000000) 2 (IntervalRat.scale (659 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (35978217936 / 1000000000000) (35978221112 / 1000000000000), orderedInterval (-73172848962 / 1000000000000) (-73172845786 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1044234254656633 / 4000000000000) 2 (IntervalRat.scale (659 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-43813101791 / 1000000000000) (-43813101790 / 1000000000000), orderedInterval (-22698065253 / 1000000000000) (-22698065252 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1425812600401241 / 4000000000000) 2 (IntervalRat.scale (659 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-33192331013 / 1000000000000) (-33192264689 / 1000000000000), orderedInterval (26204799062 / 1000000000000) (26204865385 / 1000000000000)))) (orderedInterval (-3540230498 / 1000000000000) (-3540224492 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (602888928023067 / 4000000000000) 2 (IntervalRat.scale (659 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (42380453778 / 1000000000000) (42380453779 / 1000000000000), orderedInterval (49131058974 / 1000000000000) (49131058975 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2450710021021307 / 4000000000000) 2 (IntervalRat.scale (659 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-24262620922 / 1000000000000) (-24262620921 / 1000000000000), orderedInterval (-21202906018 / 1000000000000) (-21202906017 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1636960718181013 / 4000000000000) 2 (IntervalRat.scale (659 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (39396901288 / 1000000000000) (39396901825 / 1000000000000), orderedInterval (-1918171676 / 1000000000000) (-1918171139 / 1000000000000)))) (orderedInterval (4509096228 / 1000000000000) (4509096574 / 1000000000000))) = true
  rfl'

theorem compactCertificate458_chunkChecks2 :
    compactCertificate458.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate458.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate458_chunkChecks2_0
    compactCertificate458_chunkChecks2_1 compactCertificate458_chunkChecks2_2

theorem compactCertificate458_chunkChecks3_0 :
    compactCertificate458.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (659 / 2) 3 (IntervalRat.scale (659 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-17834532883 / 1000000000000) (-17834532882 / 1000000000000), orderedInterval (-40147669713 / 1000000000000) (-40147669712 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (970832834666759 / 4000000000000) 3 (IntervalRat.scale (659 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-51205124056 / 1000000000000) (-51205123933 / 1000000000000), orderedInterval (1112370495 / 1000000000000) (1112370618 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (313947391711847 / 800000000000) 3 (IntervalRat.scale (659 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-20021113788 / 1000000000000) (-20021113787 / 1000000000000), orderedInterval (-34922862584 / 1000000000000) (-34922862583 / 1000000000000)))) (orderedInterval (19343478718 / 1000000000000) (19343478754 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (283286599864213 / 4000000000000) 3 (IntervalRat.scale (659 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (57479045908 / 1000000000000) (57479071014 / 1000000000000), orderedInterval (-75806542309 / 1000000000000) (-75806517203 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (760947654791761 / 4000000000000) 3 (IntervalRat.scale (659 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (33399647645 / 1000000000000) (33399657679 / 1000000000000), orderedInterval (-47320453934 / 1000000000000) (-47320443901 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2066120908159437 / 4000000000000) 3 (IntervalRat.scale (659 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30407015926 / 1000000000000) (30407128810 / 1000000000000), orderedInterval (-17576635385 / 1000000000000) (-17576522501 / 1000000000000)))) (orderedInterval (-4504137730 / 1000000000000) (-4504106589 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1521895309584181 / 4000000000000) 3 (IntervalRat.scale (659 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-36928238822 / 1000000000000) (-36928238821 / 1000000000000), orderedInterval (-17545023177 / 1000000000000) (-17545023176 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2607793552847113 / 4000000000000) 3 (IntervalRat.scale (659 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-20550360412 / 1000000000000) (-20550357894 / 1000000000000), orderedInterval (23556591368 / 1000000000000) (23556593887 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (1920888928023067 / 4000000000000) 3 (IntervalRat.scale (659 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-12268923993 / 1000000000000) (-12268923992 / 1000000000000), orderedInterval (-34267708371 / 1000000000000) (-34267708369 / 1000000000000)))) (orderedInterval (8197418214 / 1000000000000) (8197418921 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate458_chunkChecks3_1 :
    compactCertificate458.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (2947137594344341 / 4000000000000) 3 (IntervalRat.scale (659 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (19040877916 / 1000000000000) (19040879248 / 1000000000000), orderedInterval (-22407042476 / 1000000000000) (-22407041143 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1701530683433389 / 4000000000000) 3 (IntervalRat.scale (659 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-34278740394 / 1000000000000) (-34278686648 / 1000000000000), orderedInterval (17972093450 / 1000000000000) (17972147196 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3019396056763601 / 4000000000000) 3 (IntervalRat.scale (659 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (28945171039 / 1000000000000) (28945176822 / 1000000000000), orderedInterval (-2375098989 / 1000000000000) (-2375093206 / 1000000000000)))) (orderedInterval (-43318297358 / 1000000000000) (-43318274949 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (2821111461983669 / 4000000000000) 3 (IntervalRat.scale (659 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (21452903779 / 1000000000000) (21452908138 / 1000000000000), orderedInterval (-21049084172 / 1000000000000) (-21049079813 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2013278255316677 / 4000000000000) 3 (IntervalRat.scale (659 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (35304974512 / 1000000000000) (35304974621 / 1000000000000), orderedInterval (4254480442 / 1000000000000) (4254480551 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2282842964375283 / 4000000000000) 3 (IntervalRat.scale (659 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-9035374480 / 1000000000000) (-9035374468 / 1000000000000), orderedInterval (32161426610 / 1000000000000) (32161426622 / 1000000000000)))) (orderedInterval (-4296032181 / 1000000000000) (-4296031192 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (1903196465353027 / 4000000000000) 3 (IntervalRat.scale (659 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-29492590869 / 1000000000000) (-29492537960 / 1000000000000), orderedInterval (21668653648 / 1000000000000) (21668706557 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1681531795297567 / 4000000000000) 3 (IntervalRat.scale (659 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (7526459195 / 1000000000000) (7526459196 / 1000000000000), orderedInterval (38171330704 / 1000000000000) (38171330705 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (487373455127133 / 800000000000) 3 (IntervalRat.scale (659 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16426581782 / 1000000000000) (16426581783 / 1000000000000), orderedInterval (27828001841 / 1000000000000) (27828001842 / 1000000000000)))) (orderedInterval (-720396683 / 1000000000000) (-720394734 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate458_chunkChecks3_2 :
    compactCertificate458.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1348100625941351 / 4000000000000) 3 (IntervalRat.scale (659 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-43289980871 / 1000000000000) (-43289980300 / 1000000000000), orderedInterval (3926084351 / 1000000000000) (3926084923 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1142799830416111 / 4000000000000) 3 (IntervalRat.scale (659 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-26653226308 / 1000000000000) (-26653226307 / 1000000000000), orderedInterval (-38913433097 / 1000000000000) (-38913433096 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (715111071976933 / 4000000000000) 3 (IntervalRat.scale (659 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-28172671812 / 1000000000000) (-28172671811 / 1000000000000), orderedInterval (-52526001868 / 1000000000000) (-52526001867 / 1000000000000)))) (orderedInterval (-466266215 / 1000000000000) (-466266046 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (384589112861211 / 4000000000000) 3 (IntervalRat.scale (659 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (35978217936 / 1000000000000) (35978221112 / 1000000000000), orderedInterval (-73172848962 / 1000000000000) (-73172845786 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1044234254656633 / 4000000000000) 3 (IntervalRat.scale (659 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-43813101791 / 1000000000000) (-43813101790 / 1000000000000), orderedInterval (-22698065253 / 1000000000000) (-22698065252 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1425812600401241 / 4000000000000) 3 (IntervalRat.scale (659 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-33192331013 / 1000000000000) (-33192264689 / 1000000000000), orderedInterval (26204799062 / 1000000000000) (26204865385 / 1000000000000)))) (orderedInterval (2263620208 / 1000000000000) (2263626700 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (602888928023067 / 4000000000000) 3 (IntervalRat.scale (659 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (42380453778 / 1000000000000) (42380453779 / 1000000000000), orderedInterval (49131058974 / 1000000000000) (49131058975 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2450710021021307 / 4000000000000) 3 (IntervalRat.scale (659 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-24262620922 / 1000000000000) (-24262620921 / 1000000000000), orderedInterval (-21202906018 / 1000000000000) (-21202906017 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1636960718181013 / 4000000000000) 3 (IntervalRat.scale (659 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (39396901288 / 1000000000000) (39396901825 / 1000000000000), orderedInterval (-1918171676 / 1000000000000) (-1918171139 / 1000000000000)))) (orderedInterval (-11827328209 / 1000000000000) (-11827327723 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate458_chunkChecks3 :
    compactCertificate458.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate458.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate458_chunkChecks3_0
    compactCertificate458_chunkChecks3_1 compactCertificate458_chunkChecks3_2

theorem compactCertificate458_chunkChecks4_0 :
    compactCertificate458.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (659 / 2) 4 (IntervalRat.scale (659 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-17834532883 / 1000000000000) (-17834532882 / 1000000000000), orderedInterval (-40147669713 / 1000000000000) (-40147669712 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (970832834666759 / 4000000000000) 4 (IntervalRat.scale (659 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-51205124056 / 1000000000000) (-51205123933 / 1000000000000), orderedInterval (1112370495 / 1000000000000) (1112370618 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (313947391711847 / 800000000000) 4 (IntervalRat.scale (659 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-20021113788 / 1000000000000) (-20021113787 / 1000000000000), orderedInterval (-34922862584 / 1000000000000) (-34922862583 / 1000000000000)))) (orderedInterval (-9690691969 / 1000000000000) (-9690691928 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (283286599864213 / 4000000000000) 4 (IntervalRat.scale (659 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (57479045908 / 1000000000000) (57479071014 / 1000000000000), orderedInterval (-75806542309 / 1000000000000) (-75806517203 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (760947654791761 / 4000000000000) 4 (IntervalRat.scale (659 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (33399647645 / 1000000000000) (33399657679 / 1000000000000), orderedInterval (-47320453934 / 1000000000000) (-47320443901 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2066120908159437 / 4000000000000) 4 (IntervalRat.scale (659 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30407015926 / 1000000000000) (30407128810 / 1000000000000), orderedInterval (-17576635385 / 1000000000000) (-17576522501 / 1000000000000)))) (orderedInterval (-12892431298 / 1000000000000) (-12892382463 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1521895309584181 / 4000000000000) 4 (IntervalRat.scale (659 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-36928238822 / 1000000000000) (-36928238821 / 1000000000000), orderedInterval (-17545023177 / 1000000000000) (-17545023176 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2607793552847113 / 4000000000000) 4 (IntervalRat.scale (659 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-20550360412 / 1000000000000) (-20550357894 / 1000000000000), orderedInterval (23556591368 / 1000000000000) (23556593887 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (1920888928023067 / 4000000000000) 4 (IntervalRat.scale (659 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-12268923993 / 1000000000000) (-12268923992 / 1000000000000), orderedInterval (-34267708371 / 1000000000000) (-34267708369 / 1000000000000)))) (orderedInterval (8326933061 / 1000000000000) (8326934448 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate458_chunkChecks4_1 :
    compactCertificate458.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (2947137594344341 / 4000000000000) 4 (IntervalRat.scale (659 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (19040877916 / 1000000000000) (19040879248 / 1000000000000), orderedInterval (-22407042476 / 1000000000000) (-22407041143 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1701530683433389 / 4000000000000) 4 (IntervalRat.scale (659 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-34278740394 / 1000000000000) (-34278686648 / 1000000000000), orderedInterval (17972093450 / 1000000000000) (17972147196 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3019396056763601 / 4000000000000) 4 (IntervalRat.scale (659 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (28945171039 / 1000000000000) (28945176822 / 1000000000000), orderedInterval (-2375098989 / 1000000000000) (-2375093206 / 1000000000000)))) (orderedInterval (21958504285 / 1000000000000) (21958546858 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (2821111461983669 / 4000000000000) 4 (IntervalRat.scale (659 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (21452903779 / 1000000000000) (21452908138 / 1000000000000), orderedInterval (-21049084172 / 1000000000000) (-21049079813 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2013278255316677 / 4000000000000) 4 (IntervalRat.scale (659 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (35304974512 / 1000000000000) (35304974621 / 1000000000000), orderedInterval (4254480442 / 1000000000000) (4254480551 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2282842964375283 / 4000000000000) 4 (IntervalRat.scale (659 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-9035374480 / 1000000000000) (-9035374468 / 1000000000000), orderedInterval (32161426610 / 1000000000000) (32161426622 / 1000000000000)))) (orderedInterval (10484658808 / 1000000000000) (10484660832 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (1903196465353027 / 4000000000000) 4 (IntervalRat.scale (659 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-29492590869 / 1000000000000) (-29492537960 / 1000000000000), orderedInterval (21668653648 / 1000000000000) (21668706557 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1681531795297567 / 4000000000000) 4 (IntervalRat.scale (659 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (7526459195 / 1000000000000) (7526459196 / 1000000000000), orderedInterval (38171330704 / 1000000000000) (38171330705 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (487373455127133 / 800000000000) 4 (IntervalRat.scale (659 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (16426581782 / 1000000000000) (16426581783 / 1000000000000), orderedInterval (27828001841 / 1000000000000) (27828001842 / 1000000000000)))) (orderedInterval (2297424706 / 1000000000000) (2297427540 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate458_chunkChecks4_2 :
    compactCertificate458.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1348100625941351 / 4000000000000) 4 (IntervalRat.scale (659 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-43289980871 / 1000000000000) (-43289980300 / 1000000000000), orderedInterval (3926084351 / 1000000000000) (3926084923 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1142799830416111 / 4000000000000) 4 (IntervalRat.scale (659 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-26653226308 / 1000000000000) (-26653226307 / 1000000000000), orderedInterval (-38913433097 / 1000000000000) (-38913433096 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (715111071976933 / 4000000000000) 4 (IntervalRat.scale (659 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (-28172671812 / 1000000000000) (-28172671811 / 1000000000000), orderedInterval (-52526001868 / 1000000000000) (-52526001867 / 1000000000000)))) (orderedInterval (8352000371 / 1000000000000) (8352000541 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (384589112861211 / 4000000000000) 4 (IntervalRat.scale (659 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (35978217936 / 1000000000000) (35978221112 / 1000000000000), orderedInterval (-73172848962 / 1000000000000) (-73172845786 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1044234254656633 / 4000000000000) 4 (IntervalRat.scale (659 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-43813101791 / 1000000000000) (-43813101790 / 1000000000000), orderedInterval (-22698065253 / 1000000000000) (-22698065252 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1425812600401241 / 4000000000000) 4 (IntervalRat.scale (659 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-33192331013 / 1000000000000) (-33192264689 / 1000000000000), orderedInterval (26204799062 / 1000000000000) (26204865385 / 1000000000000)))) (orderedInterval (3857038456 / 1000000000000) (3857045495 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (602888928023067 / 4000000000000) 4 (IntervalRat.scale (659 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (42380453778 / 1000000000000) (42380453779 / 1000000000000), orderedInterval (49131058974 / 1000000000000) (49131058975 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2450710021021307 / 4000000000000) 4 (IntervalRat.scale (659 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-24262620922 / 1000000000000) (-24262620921 / 1000000000000), orderedInterval (-21202906018 / 1000000000000) (-21202906017 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1636960718181013 / 4000000000000) 4 (IntervalRat.scale (659 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (39396901288 / 1000000000000) (39396901825 / 1000000000000), orderedInterval (-1918171676 / 1000000000000) (-1918171139 / 1000000000000)))) (orderedInterval (6102754664 / 1000000000000) (6102755375 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate458_chunkChecks4 :
    compactCertificate458.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate458.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate458_chunkChecks4_0
    compactCertificate458_chunkChecks4_1 compactCertificate458_chunkChecks4_2

theorem compactCertificate458_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate458.chunkCheck r b = true :=
  compactCertificate458.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate458_chunkChecks0
    · exact compactCertificate458_chunkChecks1
    · exact compactCertificate458_chunkChecks2
    · exact compactCertificate458_chunkChecks3
    · exact compactCertificate458_chunkChecks4)

theorem compactCertificate458_coefficient0 :
    compactCertificate458.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate458_coefficient1 :
    compactCertificate458.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate458_coefficient2 :
    compactCertificate458.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate458_coefficient3 :
    compactCertificate458.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate458_coefficient4 :
    compactCertificate458.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate458_coefficients : ∀ r : Fin 5,
    compactCertificate458.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate458_coefficient0
  · exact compactCertificate458_coefficient1
  · exact compactCertificate458_coefficient2
  · exact compactCertificate458_coefficient3
  · exact compactCertificate458_coefficient4

theorem compactCertificate458_lower : (1 : ℚ) ≤ compactCertificate458.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate458, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate458_proves {t : ℝ} (ht : t ∈ compactCertificate458.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate458.proves compactCertificate458_states compactCertificate458_chunks
    compactCertificate458_coefficients compactCertificate458_lower ht

end Erdos232
