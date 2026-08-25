/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate498 : CompactCertificate where
  left := 369
  right := 370
  center := 739 / 2
  grid := fun i =>
    match i.val with
    | 0 => 118
    | 1 => 87
    | 2 => 140
    | 3 => 25
    | 4 => 68
    | 5 => 184
    | 6 => 136
    | 7 => 233
    | 8 => 172
    | 9 => 263
    | 10 => 152
    | 11 => 270
    | 12 => 252
    | 13 => 180
    | 14 => 204
    | 15 => 170
    | 16 => 150
    | 17 => 218
    | 18 => 120
    | 19 => 102
    | 20 => 64
    | 21 => 34
    | 22 => 93
    | 23 => 127
    | 24 => 54
    | 25 => 219
    | _ => 146
  point := fun i =>
    match i.val with
    | 0 => 739 / 2
    | 1 => 1088688110498839 / 4000000000000
    | 2 => 352059366426487 / 800000000000
    | 3 => 317676475416773 / 4000000000000
    | 4 => 853323697862081 / 4000000000000
    | 5 => 2316939834794877 / 4000000000000
    | 6 => 1706647395724901 / 4000000000000
    | 7 => 2924369401447673 / 4000000000000
    | 8 => 2154077265264107 / 4000000000000
    | 9 => 3304908470744261 / 4000000000000
    | 10 => 1908089795231069 / 4000000000000
    | 11 => 3385938825414721 / 4000000000000
    | 12 => 3163583263134949 / 4000000000000
    | 13 => 2257682292380917 / 4000000000000
    | 14 => 2559971093586243 / 4000000000000
    | 15 => 2134237007429267 / 4000000000000
    | 16 => 1885663120978607 / 4000000000000
    | 17 => 546538669710093 / 800000000000
    | 18 => 1511754723172471 / 4000000000000
    | 19 => 1281531221058431 / 4000000000000
    | 20 => 801922734735893 / 4000000000000
    | 21 => 431276713815531 / 4000000000000
    | 22 => 1171000173279593 / 4000000000000
    | 23 => 1598900624729161 / 4000000000000
    | 24 => 676077265264107 / 4000000000000
    | 25 => 2748216548611147 / 4000000000000
    | _ => 1835681290949573 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-17034181502 / 1000000000000) (-17034181085 / 1000000000000), orderedInterval (37874865948 / 1000000000000) (37874866365 / 1000000000000))
    | 1 => (orderedInterval (17109366971 / 1000000000000) (17109367328 / 1000000000000), orderedInterval (-45267556735 / 1000000000000) (-45267556377 / 1000000000000))
    | 2 => (orderedInterval (32730574988 / 1000000000000) (32730574989 / 1000000000000), orderedInterval (19336200203 / 1000000000000) (19336200204 / 1000000000000))
    | 3 => (orderedInterval (-89149605532 / 1000000000000) (-89149605424 / 1000000000000), orderedInterval (8816104219 / 1000000000000) (8816104327 / 1000000000000))
    | 4 => (orderedInterval (25585531965 / 1000000000000) (25585531966 / 1000000000000), orderedInterval (48205694579 / 1000000000000) (48205694580 / 1000000000000))
    | 5 => (orderedInterval (30582792985 / 1000000000000) (30582843207 / 1000000000000), orderedInterval (-12823334469 / 1000000000000) (-12823284246 / 1000000000000))
    | 6 => (orderedInterval (7308569213 / 1000000000000) (7308569214 / 1000000000000), orderedInterval (37921373319 / 1000000000000) (37921373320 / 1000000000000))
    | 7 => (orderedInterval (3342395302 / 1000000000000) (3342395303 / 1000000000000), orderedInterval (-29321349046 / 1000000000000) (-29321349045 / 1000000000000))
    | 8 => (orderedInterval (-29815014044 / 1000000000000) (-29814909368 / 1000000000000), orderedInterval (17151726869 / 1000000000000) (17151831545 / 1000000000000))
    | 9 => (orderedInterval (-19392979422 / 1000000000000) (-19392979421 / 1000000000000), orderedInterval (-19848440572 / 1000000000000) (-19848440571 / 1000000000000))
    | 10 => (orderedInterval (10288758356 / 1000000000000) (10288758357 / 1000000000000), orderedInterval (35042202785 / 1000000000000) (35042202786 / 1000000000000))
    | 11 => (orderedInterval (-22466435473 / 1000000000000) (-22466424147 / 1000000000000), orderedInterval (15740127986 / 1000000000000) (15740139312 / 1000000000000))
    | 12 => (orderedInterval (-8307309 / 1000000000000) (-8307308 / 1000000000000), orderedInterval (28371384380 / 1000000000000) (28371384381 / 1000000000000))
    | 13 => (orderedInterval (-9311203162 / 1000000000000) (-9311203149 / 1000000000000), orderedInterval (32276177533 / 1000000000000) (32276177546 / 1000000000000))
    | 14 => (orderedInterval (-3365923258 / 1000000000000) (-3365923256 / 1000000000000), orderedInterval (31361846540 / 1000000000000) (31361846542 / 1000000000000))
    | 15 => (orderedInterval (9335397864 / 1000000000000) (9335397865 / 1000000000000), orderedInterval (33247942073 / 1000000000000) (33247942074 / 1000000000000))
    | 16 => (orderedInterval (30146352322 / 1000000000000) (30146352323 / 1000000000000), orderedInterval (20983244011 / 1000000000000) (20983244012 / 1000000000000))
    | 17 => (orderedInterval (-24075269649 / 1000000000000) (-24075254262 / 1000000000000), orderedInterval (18785632189 / 1000000000000) (18785647576 / 1000000000000))
    | 18 => (orderedInterval (40505788463 / 1000000000000) (40505790202 / 1000000000000), orderedInterval (-6666619218 / 1000000000000) (-6666617479 / 1000000000000))
    | 19 => (orderedInterval (29572301267 / 1000000000000) (29572301268 / 1000000000000), orderedInterval (33308593740 / 1000000000000) (33308593741 / 1000000000000))
    | 20 => (orderedInterval (11390056867 / 1000000000000) (11390056868 / 1000000000000), orderedInterval (55159839876 / 1000000000000) (55159839877 / 1000000000000))
    | 21 => (orderedInterval (75013923122 / 1000000000000) (75013923801 / 1000000000000), orderedInterval (-17002202542 / 1000000000000) (-17002201863 / 1000000000000))
    | 22 => (orderedInterval (-45666758377 / 1000000000000) (-45666758371 / 1000000000000), orderedInterval (-9364628259 / 1000000000000) (-9364628253 / 1000000000000))
    | 23 => (orderedInterval (-39871341473 / 1000000000000) (-39871341317 / 1000000000000), orderedInterval (-1658531063 / 1000000000000) (-1658530907 / 1000000000000))
    | 24 => (orderedInterval (9654777135 / 1000000000000) (9654777136 / 1000000000000), orderedInterval (60579617874 / 1000000000000) (60579617875 / 1000000000000))
    | 25 => (orderedInterval (5133040434 / 1000000000000) (5133040435 / 1000000000000), orderedInterval (-30007826013 / 1000000000000) (-30007826011 / 1000000000000))
    | _ => (orderedInterval (31986218643 / 1000000000000) (31986218644 / 1000000000000), orderedInterval (19046382542 / 1000000000000) (19046382543 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-4671659684 / 1000000000000) (-4671659489 / 1000000000000)
      | 1 => orderedInterval (-272740911 / 1000000000000) (-272737294 / 1000000000000)
      | 2 => orderedInterval (-823662919 / 1000000000000) (-823660368 / 1000000000000)
      | 3 => orderedInterval (1014474372 / 1000000000000) (1014476129 / 1000000000000)
      | 4 => orderedInterval (-863310596 / 1000000000000) (-863310550 / 1000000000000)
      | 5 => orderedInterval (-2233795492 / 1000000000000) (-2233795062 / 1000000000000)
      | 6 => orderedInterval (-7779554320 / 1000000000000) (-7779553948 / 1000000000000)
      | 7 => orderedInterval (2706589087 / 1000000000000) (2706589156 / 1000000000000)
      | _ => orderedInterval (-6361099617 / 1000000000000) (-6361099514 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (16052962108 / 1000000000000) (16052962305 / 1000000000000)
      | 1 => orderedInterval (2424665871 / 1000000000000) (2424671519 / 1000000000000)
      | 2 => orderedInterval (2393558304 / 1000000000000) (2393562028 / 1000000000000)
      | 3 => orderedInterval (16364077103 / 1000000000000) (16364081095 / 1000000000000)
      | 4 => orderedInterval (3290991522 / 1000000000000) (3290991596 / 1000000000000)
      | 5 => orderedInterval (-88300091 / 1000000000000) (-88299311 / 1000000000000)
      | 6 => orderedInterval (429948644 / 1000000000000) (429949014 / 1000000000000)
      | 7 => orderedInterval (397439066 / 1000000000000) (397439123 / 1000000000000)
      | _ => orderedInterval (270594320 / 1000000000000) (270594465 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (3897380995 / 1000000000000) (3897381196 / 1000000000000)
      | 1 => orderedInterval (4980105015 / 1000000000000) (4980113874 / 1000000000000)
      | 2 => orderedInterval (1927668597 / 1000000000000) (1927674045 / 1000000000000)
      | 3 => orderedInterval (-1782981451 / 1000000000000) (-1782972339 / 1000000000000)
      | 4 => orderedInterval (1993791829 / 1000000000000) (1993791951 / 1000000000000)
      | 5 => orderedInterval (4690780730 / 1000000000000) (4690782156 / 1000000000000)
      | 6 => orderedInterval (7923825930 / 1000000000000) (7923826304 / 1000000000000)
      | 7 => orderedInterval (-4109529102 / 1000000000000) (-4109529047 / 1000000000000)
      | _ => orderedInterval (10689430236 / 1000000000000) (10689430449 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-16771044243 / 1000000000000) (-16771044037 / 1000000000000)
      | 1 => orderedInterval (-3863024674 / 1000000000000) (-3863010792 / 1000000000000)
      | 2 => orderedInterval (-8293773447 / 1000000000000) (-8293765484 / 1000000000000)
      | 3 => orderedInterval (-71914804606 / 1000000000000) (-71914783798 / 1000000000000)
      | 4 => orderedInterval (-5036360838 / 1000000000000) (-5036360633 / 1000000000000)
      | 5 => orderedInterval (-1715097248 / 1000000000000) (-1715094636 / 1000000000000)
      | 6 => orderedInterval (-219965676 / 1000000000000) (-219965298 / 1000000000000)
      | 7 => orderedInterval (-263257255 / 1000000000000) (-263257198 / 1000000000000)
      | _ => orderedInterval (-8920830367 / 1000000000000) (-8920830039 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-2749473008 / 1000000000000) (-2749472795 / 1000000000000)
      | 1 => orderedInterval (-13002610864 / 1000000000000) (-13002589068 / 1000000000000)
      | 2 => orderedInterval (-4786153289 / 1000000000000) (-4786141616 / 1000000000000)
      | 3 => orderedInterval (687646516 / 1000000000000) (687694138 / 1000000000000)
      | 4 => orderedInterval (-4610076635 / 1000000000000) (-4610076279 / 1000000000000)
      | 5 => orderedInterval (-11296281703 / 1000000000000) (-11296276899 / 1000000000000)
      | 6 => orderedInterval (-8001478424 / 1000000000000) (-8001478040 / 1000000000000)
      | 7 => orderedInterval (4584607952 / 1000000000000) (4584608011 / 1000000000000)
      | _ => orderedInterval (-19224516288 / 1000000000000) (-19224515761 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-19284760080 / 1000000000000) (-19284750940 / 1000000000000)
    | 1 => orderedInterval (41535936847 / 1000000000000) (41535951834 / 1000000000000)
    | 2 => orderedInterval (30210472779 / 1000000000000) (30210498589 / 1000000000000)
    | 3 => orderedInterval (-116998158354 / 1000000000000) (-116998111915 / 1000000000000)
    | _ => orderedInterval (-58398335743 / 1000000000000) (-58398248309 / 1000000000000)

theorem compactCertificate498_stateChecks0 :
    compactCertificate498.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 118 12 (739 / 2)) (orderedInterval (-17034181502 / 1000000000000) (-17034181085 / 1000000000000), orderedInterval (37874865948 / 1000000000000) (37874866365 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 87 12 (1088688110498839 / 4000000000000)) (orderedInterval (17109366971 / 1000000000000) (17109367328 / 1000000000000), orderedInterval (-45267556735 / 1000000000000) (-45267556377 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 140 12 (352059366426487 / 800000000000)) (orderedInterval (32730574988 / 1000000000000) (32730574989 / 1000000000000), orderedInterval (19336200203 / 1000000000000) (19336200204 / 1000000000000))) = true
  rfl'

theorem compactCertificate498_stateChecks1 :
    compactCertificate498.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 25 12 (317676475416773 / 4000000000000)) (orderedInterval (-89149605532 / 1000000000000) (-89149605424 / 1000000000000), orderedInterval (8816104219 / 1000000000000) (8816104327 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 68 12 (853323697862081 / 4000000000000)) (orderedInterval (25585531965 / 1000000000000) (25585531966 / 1000000000000), orderedInterval (48205694579 / 1000000000000) (48205694580 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 184 12 (2316939834794877 / 4000000000000)) (orderedInterval (30582792985 / 1000000000000) (30582843207 / 1000000000000), orderedInterval (-12823334469 / 1000000000000) (-12823284246 / 1000000000000))) = true
  rfl'

theorem compactCertificate498_stateChecks2 :
    compactCertificate498.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 136 12 (1706647395724901 / 4000000000000)) (orderedInterval (7308569213 / 1000000000000) (7308569214 / 1000000000000), orderedInterval (37921373319 / 1000000000000) (37921373320 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 233 12 (2924369401447673 / 4000000000000)) (orderedInterval (3342395302 / 1000000000000) (3342395303 / 1000000000000), orderedInterval (-29321349046 / 1000000000000) (-29321349045 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 172 12 (2154077265264107 / 4000000000000)) (orderedInterval (-29815014044 / 1000000000000) (-29814909368 / 1000000000000), orderedInterval (17151726869 / 1000000000000) (17151831545 / 1000000000000))) = true
  rfl'

theorem compactCertificate498_stateChecks3 :
    compactCertificate498.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 263 12 (3304908470744261 / 4000000000000)) (orderedInterval (-19392979422 / 1000000000000) (-19392979421 / 1000000000000), orderedInterval (-19848440572 / 1000000000000) (-19848440571 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 152 12 (1908089795231069 / 4000000000000)) (orderedInterval (10288758356 / 1000000000000) (10288758357 / 1000000000000), orderedInterval (35042202785 / 1000000000000) (35042202786 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 270 12 (3385938825414721 / 4000000000000)) (orderedInterval (-22466435473 / 1000000000000) (-22466424147 / 1000000000000), orderedInterval (15740127986 / 1000000000000) (15740139312 / 1000000000000))) = true
  rfl'

theorem compactCertificate498_stateChecks4 :
    compactCertificate498.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 252 12 (3163583263134949 / 4000000000000)) (orderedInterval (-8307309 / 1000000000000) (-8307308 / 1000000000000), orderedInterval (28371384380 / 1000000000000) (28371384381 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 180 12 (2257682292380917 / 4000000000000)) (orderedInterval (-9311203162 / 1000000000000) (-9311203149 / 1000000000000), orderedInterval (32276177533 / 1000000000000) (32276177546 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 204 12 (2559971093586243 / 4000000000000)) (orderedInterval (-3365923258 / 1000000000000) (-3365923256 / 1000000000000), orderedInterval (31361846540 / 1000000000000) (31361846542 / 1000000000000))) = true
  rfl'

theorem compactCertificate498_stateChecks5 :
    compactCertificate498.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 170 12 (2134237007429267 / 4000000000000)) (orderedInterval (9335397864 / 1000000000000) (9335397865 / 1000000000000), orderedInterval (33247942073 / 1000000000000) (33247942074 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 150 12 (1885663120978607 / 4000000000000)) (orderedInterval (30146352322 / 1000000000000) (30146352323 / 1000000000000), orderedInterval (20983244011 / 1000000000000) (20983244012 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 218 12 (546538669710093 / 800000000000)) (orderedInterval (-24075269649 / 1000000000000) (-24075254262 / 1000000000000), orderedInterval (18785632189 / 1000000000000) (18785647576 / 1000000000000))) = true
  rfl'

theorem compactCertificate498_stateChecks6 :
    compactCertificate498.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 120 12 (1511754723172471 / 4000000000000)) (orderedInterval (40505788463 / 1000000000000) (40505790202 / 1000000000000), orderedInterval (-6666619218 / 1000000000000) (-6666617479 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 102 12 (1281531221058431 / 4000000000000)) (orderedInterval (29572301267 / 1000000000000) (29572301268 / 1000000000000), orderedInterval (33308593740 / 1000000000000) (33308593741 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (801922734735893 / 4000000000000)) (orderedInterval (11390056867 / 1000000000000) (11390056868 / 1000000000000), orderedInterval (55159839876 / 1000000000000) (55159839877 / 1000000000000))) = true
  rfl'

theorem compactCertificate498_stateChecks7 :
    compactCertificate498.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 34 12 (431276713815531 / 4000000000000)) (orderedInterval (75013923122 / 1000000000000) (75013923801 / 1000000000000), orderedInterval (-17002202542 / 1000000000000) (-17002201863 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 93 12 (1171000173279593 / 4000000000000)) (orderedInterval (-45666758377 / 1000000000000) (-45666758371 / 1000000000000), orderedInterval (-9364628259 / 1000000000000) (-9364628253 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 127 12 (1598900624729161 / 4000000000000)) (orderedInterval (-39871341473 / 1000000000000) (-39871341317 / 1000000000000), orderedInterval (-1658531063 / 1000000000000) (-1658530907 / 1000000000000))) = true
  rfl'

theorem compactCertificate498_stateChecks8 :
    compactCertificate498.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (676077265264107 / 4000000000000)) (orderedInterval (9654777135 / 1000000000000) (9654777136 / 1000000000000), orderedInterval (60579617874 / 1000000000000) (60579617875 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 219 12 (2748216548611147 / 4000000000000)) (orderedInterval (5133040434 / 1000000000000) (5133040435 / 1000000000000), orderedInterval (-30007826013 / 1000000000000) (-30007826011 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 146 12 (1835681290949573 / 4000000000000)) (orderedInterval (31986218643 / 1000000000000) (31986218644 / 1000000000000), orderedInterval (19046382542 / 1000000000000) (19046382543 / 1000000000000))) = true
  rfl'

theorem compactCertificate498_states : ∀ j,
    BesselStateValid (compactCertificate498.point j) (compactCertificate498.state j) :=
  compactCertificate498.statesValid_of_checks3 compactCertificate498_stateChecks0
    compactCertificate498_stateChecks1 compactCertificate498_stateChecks2
    compactCertificate498_stateChecks3 compactCertificate498_stateChecks4
    compactCertificate498_stateChecks5 compactCertificate498_stateChecks6
    compactCertificate498_stateChecks7 compactCertificate498_stateChecks8

theorem compactCertificate498_chunkChecks0_0 :
    compactCertificate498.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (739 / 2) 0 (IntervalRat.scale (739 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-17034181502 / 1000000000000) (-17034181085 / 1000000000000), orderedInterval (37874865948 / 1000000000000) (37874866365 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1088688110498839 / 4000000000000) 0 (IntervalRat.scale (739 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (17109366971 / 1000000000000) (17109367328 / 1000000000000), orderedInterval (-45267556735 / 1000000000000) (-45267556377 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (352059366426487 / 800000000000) 0 (IntervalRat.scale (739 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (32730574988 / 1000000000000) (32730574989 / 1000000000000), orderedInterval (19336200203 / 1000000000000) (19336200204 / 1000000000000)))) (orderedInterval (-4671659684 / 1000000000000) (-4671659489 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (317676475416773 / 4000000000000) 0 (IntervalRat.scale (739 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-89149605532 / 1000000000000) (-89149605424 / 1000000000000), orderedInterval (8816104219 / 1000000000000) (8816104327 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (853323697862081 / 4000000000000) 0 (IntervalRat.scale (739 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (25585531965 / 1000000000000) (25585531966 / 1000000000000), orderedInterval (48205694579 / 1000000000000) (48205694580 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2316939834794877 / 4000000000000) 0 (IntervalRat.scale (739 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30582792985 / 1000000000000) (30582843207 / 1000000000000), orderedInterval (-12823334469 / 1000000000000) (-12823284246 / 1000000000000)))) (orderedInterval (-272740911 / 1000000000000) (-272737294 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1706647395724901 / 4000000000000) 0 (IntervalRat.scale (739 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (7308569213 / 1000000000000) (7308569214 / 1000000000000), orderedInterval (37921373319 / 1000000000000) (37921373320 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (2924369401447673 / 4000000000000) 0 (IntervalRat.scale (739 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (3342395302 / 1000000000000) (3342395303 / 1000000000000), orderedInterval (-29321349046 / 1000000000000) (-29321349045 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2154077265264107 / 4000000000000) 0 (IntervalRat.scale (739 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-29815014044 / 1000000000000) (-29814909368 / 1000000000000), orderedInterval (17151726869 / 1000000000000) (17151831545 / 1000000000000)))) (orderedInterval (-823662919 / 1000000000000) (-823660368 / 1000000000000))) = true
  rfl'

theorem compactCertificate498_chunkChecks0_1 :
    compactCertificate498.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3304908470744261 / 4000000000000) 0 (IntervalRat.scale (739 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-19392979422 / 1000000000000) (-19392979421 / 1000000000000), orderedInterval (-19848440572 / 1000000000000) (-19848440571 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (1908089795231069 / 4000000000000) 0 (IntervalRat.scale (739 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (10288758356 / 1000000000000) (10288758357 / 1000000000000), orderedInterval (35042202785 / 1000000000000) (35042202786 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3385938825414721 / 4000000000000) 0 (IntervalRat.scale (739 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-22466435473 / 1000000000000) (-22466424147 / 1000000000000), orderedInterval (15740127986 / 1000000000000) (15740139312 / 1000000000000)))) (orderedInterval (1014474372 / 1000000000000) (1014476129 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3163583263134949 / 4000000000000) 0 (IntervalRat.scale (739 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-8307309 / 1000000000000) (-8307308 / 1000000000000), orderedInterval (28371384380 / 1000000000000) (28371384381 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2257682292380917 / 4000000000000) 0 (IntervalRat.scale (739 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-9311203162 / 1000000000000) (-9311203149 / 1000000000000), orderedInterval (32276177533 / 1000000000000) (32276177546 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2559971093586243 / 4000000000000) 0 (IntervalRat.scale (739 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-3365923258 / 1000000000000) (-3365923256 / 1000000000000), orderedInterval (31361846540 / 1000000000000) (31361846542 / 1000000000000)))) (orderedInterval (-863310596 / 1000000000000) (-863310550 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2134237007429267 / 4000000000000) 0 (IntervalRat.scale (739 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (9335397864 / 1000000000000) (9335397865 / 1000000000000), orderedInterval (33247942073 / 1000000000000) (33247942074 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (1885663120978607 / 4000000000000) 0 (IntervalRat.scale (739 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (30146352322 / 1000000000000) (30146352323 / 1000000000000), orderedInterval (20983244011 / 1000000000000) (20983244012 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (546538669710093 / 800000000000) 0 (IntervalRat.scale (739 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-24075269649 / 1000000000000) (-24075254262 / 1000000000000), orderedInterval (18785632189 / 1000000000000) (18785647576 / 1000000000000)))) (orderedInterval (-2233795492 / 1000000000000) (-2233795062 / 1000000000000))) = true
  rfl'

theorem compactCertificate498_chunkChecks0_2 :
    compactCertificate498.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1511754723172471 / 4000000000000) 0 (IntervalRat.scale (739 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (40505788463 / 1000000000000) (40505790202 / 1000000000000), orderedInterval (-6666619218 / 1000000000000) (-6666617479 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1281531221058431 / 4000000000000) 0 (IntervalRat.scale (739 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (29572301267 / 1000000000000) (29572301268 / 1000000000000), orderedInterval (33308593740 / 1000000000000) (33308593741 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (801922734735893 / 4000000000000) 0 (IntervalRat.scale (739 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (11390056867 / 1000000000000) (11390056868 / 1000000000000), orderedInterval (55159839876 / 1000000000000) (55159839877 / 1000000000000)))) (orderedInterval (-7779554320 / 1000000000000) (-7779553948 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (431276713815531 / 4000000000000) 0 (IntervalRat.scale (739 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (75013923122 / 1000000000000) (75013923801 / 1000000000000), orderedInterval (-17002202542 / 1000000000000) (-17002201863 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1171000173279593 / 4000000000000) 0 (IntervalRat.scale (739 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-45666758377 / 1000000000000) (-45666758371 / 1000000000000), orderedInterval (-9364628259 / 1000000000000) (-9364628253 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1598900624729161 / 4000000000000) 0 (IntervalRat.scale (739 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-39871341473 / 1000000000000) (-39871341317 / 1000000000000), orderedInterval (-1658531063 / 1000000000000) (-1658530907 / 1000000000000)))) (orderedInterval (2706589087 / 1000000000000) (2706589156 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (676077265264107 / 4000000000000) 0 (IntervalRat.scale (739 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (9654777135 / 1000000000000) (9654777136 / 1000000000000), orderedInterval (60579617874 / 1000000000000) (60579617875 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (2748216548611147 / 4000000000000) 0 (IntervalRat.scale (739 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (5133040434 / 1000000000000) (5133040435 / 1000000000000), orderedInterval (-30007826013 / 1000000000000) (-30007826011 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (1835681290949573 / 4000000000000) 0 (IntervalRat.scale (739 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (31986218643 / 1000000000000) (31986218644 / 1000000000000), orderedInterval (19046382542 / 1000000000000) (19046382543 / 1000000000000)))) (orderedInterval (-6361099617 / 1000000000000) (-6361099514 / 1000000000000))) = true
  rfl'

theorem compactCertificate498_chunkChecks0 :
    compactCertificate498.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate498.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate498_chunkChecks0_0
    compactCertificate498_chunkChecks0_1 compactCertificate498_chunkChecks0_2

theorem compactCertificate498_chunkChecks1_0 :
    compactCertificate498.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (739 / 2) 1 (IntervalRat.scale (739 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-17034181502 / 1000000000000) (-17034181085 / 1000000000000), orderedInterval (37874865948 / 1000000000000) (37874866365 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1088688110498839 / 4000000000000) 1 (IntervalRat.scale (739 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (17109366971 / 1000000000000) (17109367328 / 1000000000000), orderedInterval (-45267556735 / 1000000000000) (-45267556377 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (352059366426487 / 800000000000) 1 (IntervalRat.scale (739 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (32730574988 / 1000000000000) (32730574989 / 1000000000000), orderedInterval (19336200203 / 1000000000000) (19336200204 / 1000000000000)))) (orderedInterval (16052962108 / 1000000000000) (16052962305 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (317676475416773 / 4000000000000) 1 (IntervalRat.scale (739 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-89149605532 / 1000000000000) (-89149605424 / 1000000000000), orderedInterval (8816104219 / 1000000000000) (8816104327 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (853323697862081 / 4000000000000) 1 (IntervalRat.scale (739 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (25585531965 / 1000000000000) (25585531966 / 1000000000000), orderedInterval (48205694579 / 1000000000000) (48205694580 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2316939834794877 / 4000000000000) 1 (IntervalRat.scale (739 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30582792985 / 1000000000000) (30582843207 / 1000000000000), orderedInterval (-12823334469 / 1000000000000) (-12823284246 / 1000000000000)))) (orderedInterval (2424665871 / 1000000000000) (2424671519 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1706647395724901 / 4000000000000) 1 (IntervalRat.scale (739 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (7308569213 / 1000000000000) (7308569214 / 1000000000000), orderedInterval (37921373319 / 1000000000000) (37921373320 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (2924369401447673 / 4000000000000) 1 (IntervalRat.scale (739 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (3342395302 / 1000000000000) (3342395303 / 1000000000000), orderedInterval (-29321349046 / 1000000000000) (-29321349045 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2154077265264107 / 4000000000000) 1 (IntervalRat.scale (739 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-29815014044 / 1000000000000) (-29814909368 / 1000000000000), orderedInterval (17151726869 / 1000000000000) (17151831545 / 1000000000000)))) (orderedInterval (2393558304 / 1000000000000) (2393562028 / 1000000000000))) = true
  rfl'

theorem compactCertificate498_chunkChecks1_1 :
    compactCertificate498.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3304908470744261 / 4000000000000) 1 (IntervalRat.scale (739 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-19392979422 / 1000000000000) (-19392979421 / 1000000000000), orderedInterval (-19848440572 / 1000000000000) (-19848440571 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (1908089795231069 / 4000000000000) 1 (IntervalRat.scale (739 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (10288758356 / 1000000000000) (10288758357 / 1000000000000), orderedInterval (35042202785 / 1000000000000) (35042202786 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3385938825414721 / 4000000000000) 1 (IntervalRat.scale (739 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-22466435473 / 1000000000000) (-22466424147 / 1000000000000), orderedInterval (15740127986 / 1000000000000) (15740139312 / 1000000000000)))) (orderedInterval (16364077103 / 1000000000000) (16364081095 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3163583263134949 / 4000000000000) 1 (IntervalRat.scale (739 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-8307309 / 1000000000000) (-8307308 / 1000000000000), orderedInterval (28371384380 / 1000000000000) (28371384381 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2257682292380917 / 4000000000000) 1 (IntervalRat.scale (739 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-9311203162 / 1000000000000) (-9311203149 / 1000000000000), orderedInterval (32276177533 / 1000000000000) (32276177546 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2559971093586243 / 4000000000000) 1 (IntervalRat.scale (739 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-3365923258 / 1000000000000) (-3365923256 / 1000000000000), orderedInterval (31361846540 / 1000000000000) (31361846542 / 1000000000000)))) (orderedInterval (3290991522 / 1000000000000) (3290991596 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2134237007429267 / 4000000000000) 1 (IntervalRat.scale (739 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (9335397864 / 1000000000000) (9335397865 / 1000000000000), orderedInterval (33247942073 / 1000000000000) (33247942074 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (1885663120978607 / 4000000000000) 1 (IntervalRat.scale (739 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (30146352322 / 1000000000000) (30146352323 / 1000000000000), orderedInterval (20983244011 / 1000000000000) (20983244012 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (546538669710093 / 800000000000) 1 (IntervalRat.scale (739 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-24075269649 / 1000000000000) (-24075254262 / 1000000000000), orderedInterval (18785632189 / 1000000000000) (18785647576 / 1000000000000)))) (orderedInterval (-88300091 / 1000000000000) (-88299311 / 1000000000000))) = true
  rfl'

theorem compactCertificate498_chunkChecks1_2 :
    compactCertificate498.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1511754723172471 / 4000000000000) 1 (IntervalRat.scale (739 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (40505788463 / 1000000000000) (40505790202 / 1000000000000), orderedInterval (-6666619218 / 1000000000000) (-6666617479 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1281531221058431 / 4000000000000) 1 (IntervalRat.scale (739 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (29572301267 / 1000000000000) (29572301268 / 1000000000000), orderedInterval (33308593740 / 1000000000000) (33308593741 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (801922734735893 / 4000000000000) 1 (IntervalRat.scale (739 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (11390056867 / 1000000000000) (11390056868 / 1000000000000), orderedInterval (55159839876 / 1000000000000) (55159839877 / 1000000000000)))) (orderedInterval (429948644 / 1000000000000) (429949014 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (431276713815531 / 4000000000000) 1 (IntervalRat.scale (739 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (75013923122 / 1000000000000) (75013923801 / 1000000000000), orderedInterval (-17002202542 / 1000000000000) (-17002201863 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1171000173279593 / 4000000000000) 1 (IntervalRat.scale (739 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-45666758377 / 1000000000000) (-45666758371 / 1000000000000), orderedInterval (-9364628259 / 1000000000000) (-9364628253 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1598900624729161 / 4000000000000) 1 (IntervalRat.scale (739 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-39871341473 / 1000000000000) (-39871341317 / 1000000000000), orderedInterval (-1658531063 / 1000000000000) (-1658530907 / 1000000000000)))) (orderedInterval (397439066 / 1000000000000) (397439123 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (676077265264107 / 4000000000000) 1 (IntervalRat.scale (739 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (9654777135 / 1000000000000) (9654777136 / 1000000000000), orderedInterval (60579617874 / 1000000000000) (60579617875 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (2748216548611147 / 4000000000000) 1 (IntervalRat.scale (739 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (5133040434 / 1000000000000) (5133040435 / 1000000000000), orderedInterval (-30007826013 / 1000000000000) (-30007826011 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (1835681290949573 / 4000000000000) 1 (IntervalRat.scale (739 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (31986218643 / 1000000000000) (31986218644 / 1000000000000), orderedInterval (19046382542 / 1000000000000) (19046382543 / 1000000000000)))) (orderedInterval (270594320 / 1000000000000) (270594465 / 1000000000000))) = true
  rfl'

theorem compactCertificate498_chunkChecks1 :
    compactCertificate498.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate498.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate498_chunkChecks1_0
    compactCertificate498_chunkChecks1_1 compactCertificate498_chunkChecks1_2

theorem compactCertificate498_chunkChecks2_0 :
    compactCertificate498.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (739 / 2) 2 (IntervalRat.scale (739 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-17034181502 / 1000000000000) (-17034181085 / 1000000000000), orderedInterval (37874865948 / 1000000000000) (37874866365 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1088688110498839 / 4000000000000) 2 (IntervalRat.scale (739 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (17109366971 / 1000000000000) (17109367328 / 1000000000000), orderedInterval (-45267556735 / 1000000000000) (-45267556377 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (352059366426487 / 800000000000) 2 (IntervalRat.scale (739 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (32730574988 / 1000000000000) (32730574989 / 1000000000000), orderedInterval (19336200203 / 1000000000000) (19336200204 / 1000000000000)))) (orderedInterval (3897380995 / 1000000000000) (3897381196 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (317676475416773 / 4000000000000) 2 (IntervalRat.scale (739 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-89149605532 / 1000000000000) (-89149605424 / 1000000000000), orderedInterval (8816104219 / 1000000000000) (8816104327 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (853323697862081 / 4000000000000) 2 (IntervalRat.scale (739 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (25585531965 / 1000000000000) (25585531966 / 1000000000000), orderedInterval (48205694579 / 1000000000000) (48205694580 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2316939834794877 / 4000000000000) 2 (IntervalRat.scale (739 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30582792985 / 1000000000000) (30582843207 / 1000000000000), orderedInterval (-12823334469 / 1000000000000) (-12823284246 / 1000000000000)))) (orderedInterval (4980105015 / 1000000000000) (4980113874 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1706647395724901 / 4000000000000) 2 (IntervalRat.scale (739 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (7308569213 / 1000000000000) (7308569214 / 1000000000000), orderedInterval (37921373319 / 1000000000000) (37921373320 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (2924369401447673 / 4000000000000) 2 (IntervalRat.scale (739 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (3342395302 / 1000000000000) (3342395303 / 1000000000000), orderedInterval (-29321349046 / 1000000000000) (-29321349045 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2154077265264107 / 4000000000000) 2 (IntervalRat.scale (739 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-29815014044 / 1000000000000) (-29814909368 / 1000000000000), orderedInterval (17151726869 / 1000000000000) (17151831545 / 1000000000000)))) (orderedInterval (1927668597 / 1000000000000) (1927674045 / 1000000000000))) = true
  rfl'

theorem compactCertificate498_chunkChecks2_1 :
    compactCertificate498.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3304908470744261 / 4000000000000) 2 (IntervalRat.scale (739 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-19392979422 / 1000000000000) (-19392979421 / 1000000000000), orderedInterval (-19848440572 / 1000000000000) (-19848440571 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (1908089795231069 / 4000000000000) 2 (IntervalRat.scale (739 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (10288758356 / 1000000000000) (10288758357 / 1000000000000), orderedInterval (35042202785 / 1000000000000) (35042202786 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3385938825414721 / 4000000000000) 2 (IntervalRat.scale (739 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-22466435473 / 1000000000000) (-22466424147 / 1000000000000), orderedInterval (15740127986 / 1000000000000) (15740139312 / 1000000000000)))) (orderedInterval (-1782981451 / 1000000000000) (-1782972339 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3163583263134949 / 4000000000000) 2 (IntervalRat.scale (739 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-8307309 / 1000000000000) (-8307308 / 1000000000000), orderedInterval (28371384380 / 1000000000000) (28371384381 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2257682292380917 / 4000000000000) 2 (IntervalRat.scale (739 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-9311203162 / 1000000000000) (-9311203149 / 1000000000000), orderedInterval (32276177533 / 1000000000000) (32276177546 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2559971093586243 / 4000000000000) 2 (IntervalRat.scale (739 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-3365923258 / 1000000000000) (-3365923256 / 1000000000000), orderedInterval (31361846540 / 1000000000000) (31361846542 / 1000000000000)))) (orderedInterval (1993791829 / 1000000000000) (1993791951 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2134237007429267 / 4000000000000) 2 (IntervalRat.scale (739 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (9335397864 / 1000000000000) (9335397865 / 1000000000000), orderedInterval (33247942073 / 1000000000000) (33247942074 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (1885663120978607 / 4000000000000) 2 (IntervalRat.scale (739 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (30146352322 / 1000000000000) (30146352323 / 1000000000000), orderedInterval (20983244011 / 1000000000000) (20983244012 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (546538669710093 / 800000000000) 2 (IntervalRat.scale (739 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-24075269649 / 1000000000000) (-24075254262 / 1000000000000), orderedInterval (18785632189 / 1000000000000) (18785647576 / 1000000000000)))) (orderedInterval (4690780730 / 1000000000000) (4690782156 / 1000000000000))) = true
  rfl'

theorem compactCertificate498_chunkChecks2_2 :
    compactCertificate498.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1511754723172471 / 4000000000000) 2 (IntervalRat.scale (739 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (40505788463 / 1000000000000) (40505790202 / 1000000000000), orderedInterval (-6666619218 / 1000000000000) (-6666617479 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1281531221058431 / 4000000000000) 2 (IntervalRat.scale (739 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (29572301267 / 1000000000000) (29572301268 / 1000000000000), orderedInterval (33308593740 / 1000000000000) (33308593741 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (801922734735893 / 4000000000000) 2 (IntervalRat.scale (739 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (11390056867 / 1000000000000) (11390056868 / 1000000000000), orderedInterval (55159839876 / 1000000000000) (55159839877 / 1000000000000)))) (orderedInterval (7923825930 / 1000000000000) (7923826304 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (431276713815531 / 4000000000000) 2 (IntervalRat.scale (739 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (75013923122 / 1000000000000) (75013923801 / 1000000000000), orderedInterval (-17002202542 / 1000000000000) (-17002201863 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1171000173279593 / 4000000000000) 2 (IntervalRat.scale (739 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-45666758377 / 1000000000000) (-45666758371 / 1000000000000), orderedInterval (-9364628259 / 1000000000000) (-9364628253 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1598900624729161 / 4000000000000) 2 (IntervalRat.scale (739 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-39871341473 / 1000000000000) (-39871341317 / 1000000000000), orderedInterval (-1658531063 / 1000000000000) (-1658530907 / 1000000000000)))) (orderedInterval (-4109529102 / 1000000000000) (-4109529047 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (676077265264107 / 4000000000000) 2 (IntervalRat.scale (739 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (9654777135 / 1000000000000) (9654777136 / 1000000000000), orderedInterval (60579617874 / 1000000000000) (60579617875 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (2748216548611147 / 4000000000000) 2 (IntervalRat.scale (739 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (5133040434 / 1000000000000) (5133040435 / 1000000000000), orderedInterval (-30007826013 / 1000000000000) (-30007826011 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (1835681290949573 / 4000000000000) 2 (IntervalRat.scale (739 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (31986218643 / 1000000000000) (31986218644 / 1000000000000), orderedInterval (19046382542 / 1000000000000) (19046382543 / 1000000000000)))) (orderedInterval (10689430236 / 1000000000000) (10689430449 / 1000000000000))) = true
  rfl'

theorem compactCertificate498_chunkChecks2 :
    compactCertificate498.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate498.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate498_chunkChecks2_0
    compactCertificate498_chunkChecks2_1 compactCertificate498_chunkChecks2_2

theorem compactCertificate498_chunkChecks3_0 :
    compactCertificate498.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (739 / 2) 3 (IntervalRat.scale (739 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-17034181502 / 1000000000000) (-17034181085 / 1000000000000), orderedInterval (37874865948 / 1000000000000) (37874866365 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1088688110498839 / 4000000000000) 3 (IntervalRat.scale (739 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (17109366971 / 1000000000000) (17109367328 / 1000000000000), orderedInterval (-45267556735 / 1000000000000) (-45267556377 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (352059366426487 / 800000000000) 3 (IntervalRat.scale (739 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (32730574988 / 1000000000000) (32730574989 / 1000000000000), orderedInterval (19336200203 / 1000000000000) (19336200204 / 1000000000000)))) (orderedInterval (-16771044243 / 1000000000000) (-16771044037 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (317676475416773 / 4000000000000) 3 (IntervalRat.scale (739 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-89149605532 / 1000000000000) (-89149605424 / 1000000000000), orderedInterval (8816104219 / 1000000000000) (8816104327 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (853323697862081 / 4000000000000) 3 (IntervalRat.scale (739 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (25585531965 / 1000000000000) (25585531966 / 1000000000000), orderedInterval (48205694579 / 1000000000000) (48205694580 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2316939834794877 / 4000000000000) 3 (IntervalRat.scale (739 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30582792985 / 1000000000000) (30582843207 / 1000000000000), orderedInterval (-12823334469 / 1000000000000) (-12823284246 / 1000000000000)))) (orderedInterval (-3863024674 / 1000000000000) (-3863010792 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1706647395724901 / 4000000000000) 3 (IntervalRat.scale (739 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (7308569213 / 1000000000000) (7308569214 / 1000000000000), orderedInterval (37921373319 / 1000000000000) (37921373320 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (2924369401447673 / 4000000000000) 3 (IntervalRat.scale (739 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (3342395302 / 1000000000000) (3342395303 / 1000000000000), orderedInterval (-29321349046 / 1000000000000) (-29321349045 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2154077265264107 / 4000000000000) 3 (IntervalRat.scale (739 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-29815014044 / 1000000000000) (-29814909368 / 1000000000000), orderedInterval (17151726869 / 1000000000000) (17151831545 / 1000000000000)))) (orderedInterval (-8293773447 / 1000000000000) (-8293765484 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate498_chunkChecks3_1 :
    compactCertificate498.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3304908470744261 / 4000000000000) 3 (IntervalRat.scale (739 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-19392979422 / 1000000000000) (-19392979421 / 1000000000000), orderedInterval (-19848440572 / 1000000000000) (-19848440571 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (1908089795231069 / 4000000000000) 3 (IntervalRat.scale (739 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (10288758356 / 1000000000000) (10288758357 / 1000000000000), orderedInterval (35042202785 / 1000000000000) (35042202786 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3385938825414721 / 4000000000000) 3 (IntervalRat.scale (739 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-22466435473 / 1000000000000) (-22466424147 / 1000000000000), orderedInterval (15740127986 / 1000000000000) (15740139312 / 1000000000000)))) (orderedInterval (-71914804606 / 1000000000000) (-71914783798 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3163583263134949 / 4000000000000) 3 (IntervalRat.scale (739 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-8307309 / 1000000000000) (-8307308 / 1000000000000), orderedInterval (28371384380 / 1000000000000) (28371384381 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2257682292380917 / 4000000000000) 3 (IntervalRat.scale (739 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-9311203162 / 1000000000000) (-9311203149 / 1000000000000), orderedInterval (32276177533 / 1000000000000) (32276177546 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2559971093586243 / 4000000000000) 3 (IntervalRat.scale (739 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-3365923258 / 1000000000000) (-3365923256 / 1000000000000), orderedInterval (31361846540 / 1000000000000) (31361846542 / 1000000000000)))) (orderedInterval (-5036360838 / 1000000000000) (-5036360633 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2134237007429267 / 4000000000000) 3 (IntervalRat.scale (739 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (9335397864 / 1000000000000) (9335397865 / 1000000000000), orderedInterval (33247942073 / 1000000000000) (33247942074 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (1885663120978607 / 4000000000000) 3 (IntervalRat.scale (739 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (30146352322 / 1000000000000) (30146352323 / 1000000000000), orderedInterval (20983244011 / 1000000000000) (20983244012 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (546538669710093 / 800000000000) 3 (IntervalRat.scale (739 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-24075269649 / 1000000000000) (-24075254262 / 1000000000000), orderedInterval (18785632189 / 1000000000000) (18785647576 / 1000000000000)))) (orderedInterval (-1715097248 / 1000000000000) (-1715094636 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate498_chunkChecks3_2 :
    compactCertificate498.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1511754723172471 / 4000000000000) 3 (IntervalRat.scale (739 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (40505788463 / 1000000000000) (40505790202 / 1000000000000), orderedInterval (-6666619218 / 1000000000000) (-6666617479 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1281531221058431 / 4000000000000) 3 (IntervalRat.scale (739 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (29572301267 / 1000000000000) (29572301268 / 1000000000000), orderedInterval (33308593740 / 1000000000000) (33308593741 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (801922734735893 / 4000000000000) 3 (IntervalRat.scale (739 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (11390056867 / 1000000000000) (11390056868 / 1000000000000), orderedInterval (55159839876 / 1000000000000) (55159839877 / 1000000000000)))) (orderedInterval (-219965676 / 1000000000000) (-219965298 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (431276713815531 / 4000000000000) 3 (IntervalRat.scale (739 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (75013923122 / 1000000000000) (75013923801 / 1000000000000), orderedInterval (-17002202542 / 1000000000000) (-17002201863 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1171000173279593 / 4000000000000) 3 (IntervalRat.scale (739 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-45666758377 / 1000000000000) (-45666758371 / 1000000000000), orderedInterval (-9364628259 / 1000000000000) (-9364628253 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1598900624729161 / 4000000000000) 3 (IntervalRat.scale (739 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-39871341473 / 1000000000000) (-39871341317 / 1000000000000), orderedInterval (-1658531063 / 1000000000000) (-1658530907 / 1000000000000)))) (orderedInterval (-263257255 / 1000000000000) (-263257198 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (676077265264107 / 4000000000000) 3 (IntervalRat.scale (739 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (9654777135 / 1000000000000) (9654777136 / 1000000000000), orderedInterval (60579617874 / 1000000000000) (60579617875 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (2748216548611147 / 4000000000000) 3 (IntervalRat.scale (739 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (5133040434 / 1000000000000) (5133040435 / 1000000000000), orderedInterval (-30007826013 / 1000000000000) (-30007826011 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (1835681290949573 / 4000000000000) 3 (IntervalRat.scale (739 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (31986218643 / 1000000000000) (31986218644 / 1000000000000), orderedInterval (19046382542 / 1000000000000) (19046382543 / 1000000000000)))) (orderedInterval (-8920830367 / 1000000000000) (-8920830039 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate498_chunkChecks3 :
    compactCertificate498.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate498.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate498_chunkChecks3_0
    compactCertificate498_chunkChecks3_1 compactCertificate498_chunkChecks3_2

theorem compactCertificate498_chunkChecks4_0 :
    compactCertificate498.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (739 / 2) 4 (IntervalRat.scale (739 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-17034181502 / 1000000000000) (-17034181085 / 1000000000000), orderedInterval (37874865948 / 1000000000000) (37874866365 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1088688110498839 / 4000000000000) 4 (IntervalRat.scale (739 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (17109366971 / 1000000000000) (17109367328 / 1000000000000), orderedInterval (-45267556735 / 1000000000000) (-45267556377 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (352059366426487 / 800000000000) 4 (IntervalRat.scale (739 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (32730574988 / 1000000000000) (32730574989 / 1000000000000), orderedInterval (19336200203 / 1000000000000) (19336200204 / 1000000000000)))) (orderedInterval (-2749473008 / 1000000000000) (-2749472795 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (317676475416773 / 4000000000000) 4 (IntervalRat.scale (739 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-89149605532 / 1000000000000) (-89149605424 / 1000000000000), orderedInterval (8816104219 / 1000000000000) (8816104327 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (853323697862081 / 4000000000000) 4 (IntervalRat.scale (739 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (25585531965 / 1000000000000) (25585531966 / 1000000000000), orderedInterval (48205694579 / 1000000000000) (48205694580 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2316939834794877 / 4000000000000) 4 (IntervalRat.scale (739 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (30582792985 / 1000000000000) (30582843207 / 1000000000000), orderedInterval (-12823334469 / 1000000000000) (-12823284246 / 1000000000000)))) (orderedInterval (-13002610864 / 1000000000000) (-13002589068 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1706647395724901 / 4000000000000) 4 (IntervalRat.scale (739 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (7308569213 / 1000000000000) (7308569214 / 1000000000000), orderedInterval (37921373319 / 1000000000000) (37921373320 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (2924369401447673 / 4000000000000) 4 (IntervalRat.scale (739 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (3342395302 / 1000000000000) (3342395303 / 1000000000000), orderedInterval (-29321349046 / 1000000000000) (-29321349045 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2154077265264107 / 4000000000000) 4 (IntervalRat.scale (739 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-29815014044 / 1000000000000) (-29814909368 / 1000000000000), orderedInterval (17151726869 / 1000000000000) (17151831545 / 1000000000000)))) (orderedInterval (-4786153289 / 1000000000000) (-4786141616 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate498_chunkChecks4_1 :
    compactCertificate498.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3304908470744261 / 4000000000000) 4 (IntervalRat.scale (739 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-19392979422 / 1000000000000) (-19392979421 / 1000000000000), orderedInterval (-19848440572 / 1000000000000) (-19848440571 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (1908089795231069 / 4000000000000) 4 (IntervalRat.scale (739 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (10288758356 / 1000000000000) (10288758357 / 1000000000000), orderedInterval (35042202785 / 1000000000000) (35042202786 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3385938825414721 / 4000000000000) 4 (IntervalRat.scale (739 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-22466435473 / 1000000000000) (-22466424147 / 1000000000000), orderedInterval (15740127986 / 1000000000000) (15740139312 / 1000000000000)))) (orderedInterval (687646516 / 1000000000000) (687694138 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3163583263134949 / 4000000000000) 4 (IntervalRat.scale (739 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-8307309 / 1000000000000) (-8307308 / 1000000000000), orderedInterval (28371384380 / 1000000000000) (28371384381 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2257682292380917 / 4000000000000) 4 (IntervalRat.scale (739 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-9311203162 / 1000000000000) (-9311203149 / 1000000000000), orderedInterval (32276177533 / 1000000000000) (32276177546 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2559971093586243 / 4000000000000) 4 (IntervalRat.scale (739 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-3365923258 / 1000000000000) (-3365923256 / 1000000000000), orderedInterval (31361846540 / 1000000000000) (31361846542 / 1000000000000)))) (orderedInterval (-4610076635 / 1000000000000) (-4610076279 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2134237007429267 / 4000000000000) 4 (IntervalRat.scale (739 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (9335397864 / 1000000000000) (9335397865 / 1000000000000), orderedInterval (33247942073 / 1000000000000) (33247942074 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (1885663120978607 / 4000000000000) 4 (IntervalRat.scale (739 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (30146352322 / 1000000000000) (30146352323 / 1000000000000), orderedInterval (20983244011 / 1000000000000) (20983244012 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (546538669710093 / 800000000000) 4 (IntervalRat.scale (739 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-24075269649 / 1000000000000) (-24075254262 / 1000000000000), orderedInterval (18785632189 / 1000000000000) (18785647576 / 1000000000000)))) (orderedInterval (-11296281703 / 1000000000000) (-11296276899 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate498_chunkChecks4_2 :
    compactCertificate498.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1511754723172471 / 4000000000000) 4 (IntervalRat.scale (739 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (40505788463 / 1000000000000) (40505790202 / 1000000000000), orderedInterval (-6666619218 / 1000000000000) (-6666617479 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1281531221058431 / 4000000000000) 4 (IntervalRat.scale (739 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (29572301267 / 1000000000000) (29572301268 / 1000000000000), orderedInterval (33308593740 / 1000000000000) (33308593741 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (801922734735893 / 4000000000000) 4 (IntervalRat.scale (739 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (11390056867 / 1000000000000) (11390056868 / 1000000000000), orderedInterval (55159839876 / 1000000000000) (55159839877 / 1000000000000)))) (orderedInterval (-8001478424 / 1000000000000) (-8001478040 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (431276713815531 / 4000000000000) 4 (IntervalRat.scale (739 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (75013923122 / 1000000000000) (75013923801 / 1000000000000), orderedInterval (-17002202542 / 1000000000000) (-17002201863 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1171000173279593 / 4000000000000) 4 (IntervalRat.scale (739 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-45666758377 / 1000000000000) (-45666758371 / 1000000000000), orderedInterval (-9364628259 / 1000000000000) (-9364628253 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1598900624729161 / 4000000000000) 4 (IntervalRat.scale (739 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-39871341473 / 1000000000000) (-39871341317 / 1000000000000), orderedInterval (-1658531063 / 1000000000000) (-1658530907 / 1000000000000)))) (orderedInterval (4584607952 / 1000000000000) (4584608011 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (676077265264107 / 4000000000000) 4 (IntervalRat.scale (739 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (9654777135 / 1000000000000) (9654777136 / 1000000000000), orderedInterval (60579617874 / 1000000000000) (60579617875 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (2748216548611147 / 4000000000000) 4 (IntervalRat.scale (739 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (5133040434 / 1000000000000) (5133040435 / 1000000000000), orderedInterval (-30007826013 / 1000000000000) (-30007826011 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (1835681290949573 / 4000000000000) 4 (IntervalRat.scale (739 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (31986218643 / 1000000000000) (31986218644 / 1000000000000), orderedInterval (19046382542 / 1000000000000) (19046382543 / 1000000000000)))) (orderedInterval (-19224516288 / 1000000000000) (-19224515761 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate498_chunkChecks4 :
    compactCertificate498.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate498.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate498_chunkChecks4_0
    compactCertificate498_chunkChecks4_1 compactCertificate498_chunkChecks4_2

theorem compactCertificate498_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate498.chunkCheck r b = true :=
  compactCertificate498.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate498_chunkChecks0
    · exact compactCertificate498_chunkChecks1
    · exact compactCertificate498_chunkChecks2
    · exact compactCertificate498_chunkChecks3
    · exact compactCertificate498_chunkChecks4)

theorem compactCertificate498_coefficient0 :
    compactCertificate498.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate498_coefficient1 :
    compactCertificate498.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate498_coefficient2 :
    compactCertificate498.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate498_coefficient3 :
    compactCertificate498.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate498_coefficient4 :
    compactCertificate498.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate498_coefficients : ∀ r : Fin 5,
    compactCertificate498.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate498_coefficient0
  · exact compactCertificate498_coefficient1
  · exact compactCertificate498_coefficient2
  · exact compactCertificate498_coefficient3
  · exact compactCertificate498_coefficient4

theorem compactCertificate498_lower : (1 : ℚ) ≤ compactCertificate498.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate498, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate498_proves {t : ℝ} (ht : t ∈ compactCertificate498.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate498.proves compactCertificate498_states compactCertificate498_chunks
    compactCertificate498_coefficients compactCertificate498_lower ht

end Erdos232
