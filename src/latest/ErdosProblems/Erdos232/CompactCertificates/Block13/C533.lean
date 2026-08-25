/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate533 : CompactCertificate where
  left := 404
  right := 405
  center := 809 / 2
  grid := fun i =>
    match i.val with
    | 0 => 129
    | 1 => 95
    | 2 => 153
    | 3 => 28
    | 4 => 74
    | 5 => 202
    | 6 => 149
    | 7 => 255
    | 8 => 188
    | 9 => 288
    | 10 => 166
    | 11 => 295
    | 12 => 276
    | 13 => 197
    | 14 => 223
    | 15 => 186
    | 16 => 164
    | 17 => 238
    | 18 => 132
    | 19 => 112
    | 20 => 70
    | 21 => 38
    | 22 => 102
    | 23 => 139
    | 24 => 59
    | 25 => 240
    | _ => 160
  point := fun i =>
    match i.val with
    | 0 => 809 / 2
    | 1 => 1191811476851909 / 4000000000000
    | 2 => 385407344301797 / 800000000000
    | 3 => 347767616525263 / 4000000000000
    | 4 => 934152735548611 / 4000000000000
    | 5 => 2536406395600887 / 4000000000000
    | 6 => 1868305471098031 / 4000000000000
    | 7 => 3201373268973163 / 4000000000000
    | 8 => 2358117060350017 / 4000000000000
    | 9 => 3617957987594191 / 4000000000000
    | 10 => 2088829018054039 / 4000000000000
    | 11 => 3706663747984451 / 4000000000000
    | 12 => 3463246089142319 / 4000000000000
    | 13 => 2471535824812127 / 4000000000000
    | 14 => 2802458206645833 / 4000000000000
    | 15 => 2336397481745977 / 4000000000000
    | 16 => 2064278030949517 / 4000000000000
    | 17 => 598308232470183 / 800000000000
    | 18 => 1654952058249701 / 4000000000000
    | 19 => 1402921187870461 / 4000000000000
    | 20 => 877882939649983 / 4000000000000
    | 21 => 472128364650561 / 4000000000000
    | 22 => 1281920352074683 / 4000000000000
    | 23 => 1750352646016091 / 4000000000000
    | 24 => 740117060350017 / 4000000000000
    | 25 => 3008534760252257 / 4000000000000
    | _ => 2009561792122063 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-778975957 / 1000000000000) (-778975956 / 1000000000000), orderedInterval (-39663102555 / 1000000000000) (-39663102554 / 1000000000000))
    | 1 => (orderedInterval (-13064728619 / 1000000000000) (-13064728618 / 1000000000000), orderedInterval (-44317237836 / 1000000000000) (-44317237835 / 1000000000000))
    | 2 => (orderedInterval (-34620667712 / 1000000000000) (-34620653401 / 1000000000000), orderedInterval (11120030247 / 1000000000000) (11120044559 / 1000000000000))
    | 3 => (orderedInterval (-20234626201 / 1000000000000) (-20234625960 / 1000000000000), orderedInterval (83260971971 / 1000000000000) (83260972213 / 1000000000000))
    | 4 => (orderedInterval (50257599745 / 1000000000000) (50257602453 / 1000000000000), orderedInterval (-14254877619 / 1000000000000) (-14254874910 / 1000000000000))
    | 5 => (orderedInterval (8911165961 / 1000000000000) (8911165962 / 1000000000000), orderedInterval (30399594879 / 1000000000000) (30399594880 / 1000000000000))
    | 6 => (orderedInterval (8625226335 / 1000000000000) (8625226349 / 1000000000000), orderedInterval (-35906235626 / 1000000000000) (-35906235612 / 1000000000000))
    | 7 => (orderedInterval (-632621927 / 1000000000000) (-632621926 / 1000000000000), orderedInterval (-28195939695 / 1000000000000) (-28195939694 / 1000000000000))
    | 8 => (orderedInterval (-9867068481 / 1000000000000) (-9867068465 / 1000000000000), orderedInterval (31353534536 / 1000000000000) (31353534552 / 1000000000000))
    | 9 => (orderedInterval (12627653072 / 1000000000000) (12627653073 / 1000000000000), orderedInterval (23325116061 / 1000000000000) (23325116062 / 1000000000000))
    | 10 => (orderedInterval (34796005758 / 1000000000000) (34796005967 / 1000000000000), orderedInterval (2853118194 / 1000000000000) (2853118403 / 1000000000000))
    | 11 => (orderedInterval (-16508952492 / 1000000000000) (-16508952491 / 1000000000000), orderedInterval (-20349255358 / 1000000000000) (-20349255357 / 1000000000000))
    | 12 => (orderedInterval (-12588890203 / 1000000000000) (-12588890175 / 1000000000000), orderedInterval (24024070359 / 1000000000000) (24024070388 / 1000000000000))
    | 13 => (orderedInterval (7148914450 / 1000000000000) (7148914454 / 1000000000000), orderedInterval (-31298210188 / 1000000000000) (-31298210184 / 1000000000000))
    | 14 => (orderedInterval (-22134199462 / 1000000000000) (-22134199461 / 1000000000000), orderedInterval (-20447250277 / 1000000000000) (-20447250276 / 1000000000000))
    | 15 => (orderedInterval (17208656006 / 1000000000000) (17208656007 / 1000000000000), orderedInterval (28159357104 / 1000000000000) (28159357105 / 1000000000000))
    | 16 => (orderedInterval (35053580255 / 1000000000000) (35053581496 / 1000000000000), orderedInterval (-2233728507 / 1000000000000) (-2233727266 / 1000000000000))
    | 17 => (orderedInterval (24090906156 / 1000000000000) (24090906157 / 1000000000000), orderedInterval (16441556747 / 1000000000000) (16441556748 / 1000000000000))
    | 18 => (orderedInterval (-6525011909 / 1000000000000) (-6525011901 / 1000000000000), orderedInterval (38687698169 / 1000000000000) (38687698177 / 1000000000000))
    | 19 => (orderedInterval (-14329951999 / 1000000000000) (-14329951834 / 1000000000000), orderedInterval (40142494427 / 1000000000000) (40142494592 / 1000000000000))
    | 20 => (orderedInterval (18167887089 / 1000000000000) (18167887090 / 1000000000000), orderedInterval (50660072514 / 1000000000000) (50660072515 / 1000000000000))
    | 21 => (orderedInterval (-39265000168 / 1000000000000) (-39264991552 / 1000000000000), orderedInterval (62229975416 / 1000000000000) (62229984032 / 1000000000000))
    | 22 => (orderedInterval (32667242572 / 1000000000000) (32667242573 / 1000000000000), orderedInterval (30269120435 / 1000000000000) (30269120436 / 1000000000000))
    | 23 => (orderedInterval (-37862987994 / 1000000000000) (-37862986453 / 1000000000000), orderedInterval (4650975063 / 1000000000000) (4650976605 / 1000000000000))
    | 24 => (orderedInterval (-26041727318 / 1000000000000) (-26041727317 / 1000000000000), orderedInterval (-52488925898 / 1000000000000) (-52488925897 / 1000000000000))
    | 25 => (orderedInterval (-25426700479 / 1000000000000) (-25426653953 / 1000000000000), orderedInterval (14155561426 / 1000000000000) (14155607952 / 1000000000000))
    | _ => (orderedInterval (17711549763 / 1000000000000) (17711549764 / 1000000000000), orderedInterval (30860886380 / 1000000000000) (30860886381 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-2462076988 / 1000000000000) (-2462076119 / 1000000000000)
      | 1 => orderedInterval (1421032448 / 1000000000000) (1421032599 / 1000000000000)
      | 2 => orderedInterval (-218954998 / 1000000000000) (-218954974 / 1000000000000)
      | 3 => orderedInterval (-2012528742 / 1000000000000) (-2012528566 / 1000000000000)
      | 4 => orderedInterval (1015301930 / 1000000000000) (1015301980 / 1000000000000)
      | 5 => orderedInterval (-1190457768 / 1000000000000) (-1190457658 / 1000000000000)
      | 6 => orderedInterval (2445835167 / 1000000000000) (2445835279 / 1000000000000)
      | 7 => orderedInterval (2885691911 / 1000000000000) (2885692237 / 1000000000000)
      | _ => orderedInterval (-1410369885 / 1000000000000) (-1410365985 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (-15248073063 / 1000000000000) (-15248072031 / 1000000000000)
      | 1 => orderedInterval (-3882425043 / 1000000000000) (-3882424930 / 1000000000000)
      | 2 => orderedInterval (2825109148 / 1000000000000) (2825109188 / 1000000000000)
      | 3 => orderedInterval (-15621698465 / 1000000000000) (-15621698112 / 1000000000000)
      | 4 => orderedInterval (-5270045064 / 1000000000000) (-5270044983 / 1000000000000)
      | 5 => orderedInterval (1410975009 / 1000000000000) (1410975156 / 1000000000000)
      | 6 => orderedInterval (-7402345266 / 1000000000000) (-7402345162 / 1000000000000)
      | 7 => orderedInterval (-1264975220 / 1000000000000) (-1264975001 / 1000000000000)
      | _ => orderedInterval (-9478927983 / 1000000000000) (-9478920783 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (3294259546 / 1000000000000) (3294260777 / 1000000000000)
      | 1 => orderedInterval (944551313 / 1000000000000) (944551423 / 1000000000000)
      | 2 => orderedInterval (423154309 / 1000000000000) (423154381 / 1000000000000)
      | 3 => orderedInterval (19277379342 / 1000000000000) (19277380082 / 1000000000000)
      | 4 => orderedInterval (-2941625754 / 1000000000000) (-2941625621 / 1000000000000)
      | 5 => orderedInterval (738761022 / 1000000000000) (738761222 / 1000000000000)
      | 6 => orderedInterval (-1857091630 / 1000000000000) (-1857091531 / 1000000000000)
      | 7 => orderedInterval (-2989317838 / 1000000000000) (-2989317642 / 1000000000000)
      | _ => orderedInterval (-1973615733 / 1000000000000) (-1973602388 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (14775465919 / 1000000000000) (14775467384 / 1000000000000)
      | 1 => orderedInterval (8431983140 / 1000000000000) (8431983274 / 1000000000000)
      | 2 => orderedInterval (-9083257586 / 1000000000000) (-9083257456 / 1000000000000)
      | 3 => orderedInterval (80615169730 / 1000000000000) (80615171328 / 1000000000000)
      | 4 => orderedInterval (14271591482 / 1000000000000) (14271591708 / 1000000000000)
      | 5 => orderedInterval (-3907085901 / 1000000000000) (-3907085625 / 1000000000000)
      | 6 => orderedInterval (7841663491 / 1000000000000) (7841663586 / 1000000000000)
      | 7 => orderedInterval (828723886 / 1000000000000) (828724085 / 1000000000000)
      | _ => orderedInterval (18536494279 / 1000000000000) (18536519018 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-4505339882 / 1000000000000) (-4505338135 / 1000000000000)
      | 1 => orderedInterval (-3662951298 / 1000000000000) (-3662951110 / 1000000000000)
      | 2 => orderedInterval (-731946834 / 1000000000000) (-731946596 / 1000000000000)
      | 3 => orderedInterval (-113971887203 / 1000000000000) (-113971883686 / 1000000000000)
      | 4 => orderedInterval (9388525121 / 1000000000000) (9388525515 / 1000000000000)
      | 5 => orderedInterval (2776676122 / 1000000000000) (2776676515 / 1000000000000)
      | 6 => orderedInterval (1612834431 / 1000000000000) (1612834524 / 1000000000000)
      | 7 => orderedInterval (3683339474 / 1000000000000) (3683339684 / 1000000000000)
      | _ => orderedInterval (16735587400 / 1000000000000) (16735633369 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (473473075 / 1000000000000) (473478793 / 1000000000000)
    | 1 => orderedInterval (-53932405947 / 1000000000000) (-53932396658 / 1000000000000)
    | 2 => orderedInterval (14916454577 / 1000000000000) (14916470703 / 1000000000000)
    | 3 => orderedInterval (132310748440 / 1000000000000) (132310777302 / 1000000000000)
    | _ => orderedInterval (-88675162669 / 1000000000000) (-88675109920 / 1000000000000)

theorem compactCertificate533_stateChecks0 :
    compactCertificate533.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 129 12 (809 / 2)) (orderedInterval (-778975957 / 1000000000000) (-778975956 / 1000000000000), orderedInterval (-39663102555 / 1000000000000) (-39663102554 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 95 12 (1191811476851909 / 4000000000000)) (orderedInterval (-13064728619 / 1000000000000) (-13064728618 / 1000000000000), orderedInterval (-44317237836 / 1000000000000) (-44317237835 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 153 12 (385407344301797 / 800000000000)) (orderedInterval (-34620667712 / 1000000000000) (-34620653401 / 1000000000000), orderedInterval (11120030247 / 1000000000000) (11120044559 / 1000000000000))) = true
  rfl'

theorem compactCertificate533_stateChecks1 :
    compactCertificate533.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 28 12 (347767616525263 / 4000000000000)) (orderedInterval (-20234626201 / 1000000000000) (-20234625960 / 1000000000000), orderedInterval (83260971971 / 1000000000000) (83260972213 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 74 12 (934152735548611 / 4000000000000)) (orderedInterval (50257599745 / 1000000000000) (50257602453 / 1000000000000), orderedInterval (-14254877619 / 1000000000000) (-14254874910 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 202 12 (2536406395600887 / 4000000000000)) (orderedInterval (8911165961 / 1000000000000) (8911165962 / 1000000000000), orderedInterval (30399594879 / 1000000000000) (30399594880 / 1000000000000))) = true
  rfl'

theorem compactCertificate533_stateChecks2 :
    compactCertificate533.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 149 12 (1868305471098031 / 4000000000000)) (orderedInterval (8625226335 / 1000000000000) (8625226349 / 1000000000000), orderedInterval (-35906235626 / 1000000000000) (-35906235612 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 255 12 (3201373268973163 / 4000000000000)) (orderedInterval (-632621927 / 1000000000000) (-632621926 / 1000000000000), orderedInterval (-28195939695 / 1000000000000) (-28195939694 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 188 12 (2358117060350017 / 4000000000000)) (orderedInterval (-9867068481 / 1000000000000) (-9867068465 / 1000000000000), orderedInterval (31353534536 / 1000000000000) (31353534552 / 1000000000000))) = true
  rfl'

theorem compactCertificate533_stateChecks3 :
    compactCertificate533.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 288 12 (3617957987594191 / 4000000000000)) (orderedInterval (12627653072 / 1000000000000) (12627653073 / 1000000000000), orderedInterval (23325116061 / 1000000000000) (23325116062 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 166 12 (2088829018054039 / 4000000000000)) (orderedInterval (34796005758 / 1000000000000) (34796005967 / 1000000000000), orderedInterval (2853118194 / 1000000000000) (2853118403 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 295 12 (3706663747984451 / 4000000000000)) (orderedInterval (-16508952492 / 1000000000000) (-16508952491 / 1000000000000), orderedInterval (-20349255358 / 1000000000000) (-20349255357 / 1000000000000))) = true
  rfl'

theorem compactCertificate533_stateChecks4 :
    compactCertificate533.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 276 12 (3463246089142319 / 4000000000000)) (orderedInterval (-12588890203 / 1000000000000) (-12588890175 / 1000000000000), orderedInterval (24024070359 / 1000000000000) (24024070388 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 197 12 (2471535824812127 / 4000000000000)) (orderedInterval (7148914450 / 1000000000000) (7148914454 / 1000000000000), orderedInterval (-31298210188 / 1000000000000) (-31298210184 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 223 12 (2802458206645833 / 4000000000000)) (orderedInterval (-22134199462 / 1000000000000) (-22134199461 / 1000000000000), orderedInterval (-20447250277 / 1000000000000) (-20447250276 / 1000000000000))) = true
  rfl'

theorem compactCertificate533_stateChecks5 :
    compactCertificate533.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 186 12 (2336397481745977 / 4000000000000)) (orderedInterval (17208656006 / 1000000000000) (17208656007 / 1000000000000), orderedInterval (28159357104 / 1000000000000) (28159357105 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 164 12 (2064278030949517 / 4000000000000)) (orderedInterval (35053580255 / 1000000000000) (35053581496 / 1000000000000), orderedInterval (-2233728507 / 1000000000000) (-2233727266 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 238 12 (598308232470183 / 800000000000)) (orderedInterval (24090906156 / 1000000000000) (24090906157 / 1000000000000), orderedInterval (16441556747 / 1000000000000) (16441556748 / 1000000000000))) = true
  rfl'

theorem compactCertificate533_stateChecks6 :
    compactCertificate533.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 132 12 (1654952058249701 / 4000000000000)) (orderedInterval (-6525011909 / 1000000000000) (-6525011901 / 1000000000000), orderedInterval (38687698169 / 1000000000000) (38687698177 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 112 12 (1402921187870461 / 4000000000000)) (orderedInterval (-14329951999 / 1000000000000) (-14329951834 / 1000000000000), orderedInterval (40142494427 / 1000000000000) (40142494592 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (877882939649983 / 4000000000000)) (orderedInterval (18167887089 / 1000000000000) (18167887090 / 1000000000000), orderedInterval (50660072514 / 1000000000000) (50660072515 / 1000000000000))) = true
  rfl'

theorem compactCertificate533_stateChecks7 :
    compactCertificate533.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (472128364650561 / 4000000000000)) (orderedInterval (-39265000168 / 1000000000000) (-39264991552 / 1000000000000), orderedInterval (62229975416 / 1000000000000) (62229984032 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 102 12 (1281920352074683 / 4000000000000)) (orderedInterval (32667242572 / 1000000000000) (32667242573 / 1000000000000), orderedInterval (30269120435 / 1000000000000) (30269120436 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 139 12 (1750352646016091 / 4000000000000)) (orderedInterval (-37862987994 / 1000000000000) (-37862986453 / 1000000000000), orderedInterval (4650975063 / 1000000000000) (4650976605 / 1000000000000))) = true
  rfl'

theorem compactCertificate533_stateChecks8 :
    compactCertificate533.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 59 12 (740117060350017 / 4000000000000)) (orderedInterval (-26041727318 / 1000000000000) (-26041727317 / 1000000000000), orderedInterval (-52488925898 / 1000000000000) (-52488925897 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 240 12 (3008534760252257 / 4000000000000)) (orderedInterval (-25426700479 / 1000000000000) (-25426653953 / 1000000000000), orderedInterval (14155561426 / 1000000000000) (14155607952 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 160 12 (2009561792122063 / 4000000000000)) (orderedInterval (17711549763 / 1000000000000) (17711549764 / 1000000000000), orderedInterval (30860886380 / 1000000000000) (30860886381 / 1000000000000))) = true
  rfl'

theorem compactCertificate533_states : ∀ j,
    BesselStateValid (compactCertificate533.point j) (compactCertificate533.state j) :=
  compactCertificate533.statesValid_of_checks3 compactCertificate533_stateChecks0
    compactCertificate533_stateChecks1 compactCertificate533_stateChecks2
    compactCertificate533_stateChecks3 compactCertificate533_stateChecks4
    compactCertificate533_stateChecks5 compactCertificate533_stateChecks6
    compactCertificate533_stateChecks7 compactCertificate533_stateChecks8

theorem compactCertificate533_chunkChecks0_0 :
    compactCertificate533.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (809 / 2) 0 (IntervalRat.scale (809 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-778975957 / 1000000000000) (-778975956 / 1000000000000), orderedInterval (-39663102555 / 1000000000000) (-39663102554 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (1191811476851909 / 4000000000000) 0 (IntervalRat.scale (809 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-13064728619 / 1000000000000) (-13064728618 / 1000000000000), orderedInterval (-44317237836 / 1000000000000) (-44317237835 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (385407344301797 / 800000000000) 0 (IntervalRat.scale (809 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-34620667712 / 1000000000000) (-34620653401 / 1000000000000), orderedInterval (11120030247 / 1000000000000) (11120044559 / 1000000000000)))) (orderedInterval (-2462076988 / 1000000000000) (-2462076119 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (347767616525263 / 4000000000000) 0 (IntervalRat.scale (809 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-20234626201 / 1000000000000) (-20234625960 / 1000000000000), orderedInterval (83260971971 / 1000000000000) (83260972213 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (934152735548611 / 4000000000000) 0 (IntervalRat.scale (809 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (50257599745 / 1000000000000) (50257602453 / 1000000000000), orderedInterval (-14254877619 / 1000000000000) (-14254874910 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (2536406395600887 / 4000000000000) 0 (IntervalRat.scale (809 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (8911165961 / 1000000000000) (8911165962 / 1000000000000), orderedInterval (30399594879 / 1000000000000) (30399594880 / 1000000000000)))) (orderedInterval (1421032448 / 1000000000000) (1421032599 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (1868305471098031 / 4000000000000) 0 (IntervalRat.scale (809 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (8625226335 / 1000000000000) (8625226349 / 1000000000000), orderedInterval (-35906235626 / 1000000000000) (-35906235612 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (3201373268973163 / 4000000000000) 0 (IntervalRat.scale (809 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-632621927 / 1000000000000) (-632621926 / 1000000000000), orderedInterval (-28195939695 / 1000000000000) (-28195939694 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (2358117060350017 / 4000000000000) 0 (IntervalRat.scale (809 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-9867068481 / 1000000000000) (-9867068465 / 1000000000000), orderedInterval (31353534536 / 1000000000000) (31353534552 / 1000000000000)))) (orderedInterval (-218954998 / 1000000000000) (-218954974 / 1000000000000))) = true
  rfl'

theorem compactCertificate533_chunkChecks0_1 :
    compactCertificate533.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (3617957987594191 / 4000000000000) 0 (IntervalRat.scale (809 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (12627653072 / 1000000000000) (12627653073 / 1000000000000), orderedInterval (23325116061 / 1000000000000) (23325116062 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (2088829018054039 / 4000000000000) 0 (IntervalRat.scale (809 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (34796005758 / 1000000000000) (34796005967 / 1000000000000), orderedInterval (2853118194 / 1000000000000) (2853118403 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (3706663747984451 / 4000000000000) 0 (IntervalRat.scale (809 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-16508952492 / 1000000000000) (-16508952491 / 1000000000000), orderedInterval (-20349255358 / 1000000000000) (-20349255357 / 1000000000000)))) (orderedInterval (-2012528742 / 1000000000000) (-2012528566 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (3463246089142319 / 4000000000000) 0 (IntervalRat.scale (809 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-12588890203 / 1000000000000) (-12588890175 / 1000000000000), orderedInterval (24024070359 / 1000000000000) (24024070388 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (2471535824812127 / 4000000000000) 0 (IntervalRat.scale (809 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (7148914450 / 1000000000000) (7148914454 / 1000000000000), orderedInterval (-31298210188 / 1000000000000) (-31298210184 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (2802458206645833 / 4000000000000) 0 (IntervalRat.scale (809 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-22134199462 / 1000000000000) (-22134199461 / 1000000000000), orderedInterval (-20447250277 / 1000000000000) (-20447250276 / 1000000000000)))) (orderedInterval (1015301930 / 1000000000000) (1015301980 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (2336397481745977 / 4000000000000) 0 (IntervalRat.scale (809 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (17208656006 / 1000000000000) (17208656007 / 1000000000000), orderedInterval (28159357104 / 1000000000000) (28159357105 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (2064278030949517 / 4000000000000) 0 (IntervalRat.scale (809 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (35053580255 / 1000000000000) (35053581496 / 1000000000000), orderedInterval (-2233728507 / 1000000000000) (-2233727266 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (598308232470183 / 800000000000) 0 (IntervalRat.scale (809 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (24090906156 / 1000000000000) (24090906157 / 1000000000000), orderedInterval (16441556747 / 1000000000000) (16441556748 / 1000000000000)))) (orderedInterval (-1190457768 / 1000000000000) (-1190457658 / 1000000000000))) = true
  rfl'

theorem compactCertificate533_chunkChecks0_2 :
    compactCertificate533.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (1654952058249701 / 4000000000000) 0 (IntervalRat.scale (809 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-6525011909 / 1000000000000) (-6525011901 / 1000000000000), orderedInterval (38687698169 / 1000000000000) (38687698177 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (1402921187870461 / 4000000000000) 0 (IntervalRat.scale (809 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-14329951999 / 1000000000000) (-14329951834 / 1000000000000), orderedInterval (40142494427 / 1000000000000) (40142494592 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (877882939649983 / 4000000000000) 0 (IntervalRat.scale (809 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (18167887089 / 1000000000000) (18167887090 / 1000000000000), orderedInterval (50660072514 / 1000000000000) (50660072515 / 1000000000000)))) (orderedInterval (2445835167 / 1000000000000) (2445835279 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (472128364650561 / 4000000000000) 0 (IntervalRat.scale (809 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-39265000168 / 1000000000000) (-39264991552 / 1000000000000), orderedInterval (62229975416 / 1000000000000) (62229984032 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (1281920352074683 / 4000000000000) 0 (IntervalRat.scale (809 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (32667242572 / 1000000000000) (32667242573 / 1000000000000), orderedInterval (30269120435 / 1000000000000) (30269120436 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (1750352646016091 / 4000000000000) 0 (IntervalRat.scale (809 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-37862987994 / 1000000000000) (-37862986453 / 1000000000000), orderedInterval (4650975063 / 1000000000000) (4650976605 / 1000000000000)))) (orderedInterval (2885691911 / 1000000000000) (2885692237 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (740117060350017 / 4000000000000) 0 (IntervalRat.scale (809 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-26041727318 / 1000000000000) (-26041727317 / 1000000000000), orderedInterval (-52488925898 / 1000000000000) (-52488925897 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (3008534760252257 / 4000000000000) 0 (IntervalRat.scale (809 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-25426700479 / 1000000000000) (-25426653953 / 1000000000000), orderedInterval (14155561426 / 1000000000000) (14155607952 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (2009561792122063 / 4000000000000) 0 (IntervalRat.scale (809 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (17711549763 / 1000000000000) (17711549764 / 1000000000000), orderedInterval (30860886380 / 1000000000000) (30860886381 / 1000000000000)))) (orderedInterval (-1410369885 / 1000000000000) (-1410365985 / 1000000000000))) = true
  rfl'

theorem compactCertificate533_chunkChecks0 :
    compactCertificate533.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate533.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate533_chunkChecks0_0
    compactCertificate533_chunkChecks0_1 compactCertificate533_chunkChecks0_2

theorem compactCertificate533_chunkChecks1_0 :
    compactCertificate533.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (809 / 2) 1 (IntervalRat.scale (809 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-778975957 / 1000000000000) (-778975956 / 1000000000000), orderedInterval (-39663102555 / 1000000000000) (-39663102554 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (1191811476851909 / 4000000000000) 1 (IntervalRat.scale (809 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-13064728619 / 1000000000000) (-13064728618 / 1000000000000), orderedInterval (-44317237836 / 1000000000000) (-44317237835 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (385407344301797 / 800000000000) 1 (IntervalRat.scale (809 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-34620667712 / 1000000000000) (-34620653401 / 1000000000000), orderedInterval (11120030247 / 1000000000000) (11120044559 / 1000000000000)))) (orderedInterval (-15248073063 / 1000000000000) (-15248072031 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (347767616525263 / 4000000000000) 1 (IntervalRat.scale (809 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-20234626201 / 1000000000000) (-20234625960 / 1000000000000), orderedInterval (83260971971 / 1000000000000) (83260972213 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (934152735548611 / 4000000000000) 1 (IntervalRat.scale (809 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (50257599745 / 1000000000000) (50257602453 / 1000000000000), orderedInterval (-14254877619 / 1000000000000) (-14254874910 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (2536406395600887 / 4000000000000) 1 (IntervalRat.scale (809 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (8911165961 / 1000000000000) (8911165962 / 1000000000000), orderedInterval (30399594879 / 1000000000000) (30399594880 / 1000000000000)))) (orderedInterval (-3882425043 / 1000000000000) (-3882424930 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (1868305471098031 / 4000000000000) 1 (IntervalRat.scale (809 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (8625226335 / 1000000000000) (8625226349 / 1000000000000), orderedInterval (-35906235626 / 1000000000000) (-35906235612 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (3201373268973163 / 4000000000000) 1 (IntervalRat.scale (809 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-632621927 / 1000000000000) (-632621926 / 1000000000000), orderedInterval (-28195939695 / 1000000000000) (-28195939694 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (2358117060350017 / 4000000000000) 1 (IntervalRat.scale (809 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-9867068481 / 1000000000000) (-9867068465 / 1000000000000), orderedInterval (31353534536 / 1000000000000) (31353534552 / 1000000000000)))) (orderedInterval (2825109148 / 1000000000000) (2825109188 / 1000000000000))) = true
  rfl'

theorem compactCertificate533_chunkChecks1_1 :
    compactCertificate533.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (3617957987594191 / 4000000000000) 1 (IntervalRat.scale (809 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (12627653072 / 1000000000000) (12627653073 / 1000000000000), orderedInterval (23325116061 / 1000000000000) (23325116062 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (2088829018054039 / 4000000000000) 1 (IntervalRat.scale (809 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (34796005758 / 1000000000000) (34796005967 / 1000000000000), orderedInterval (2853118194 / 1000000000000) (2853118403 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (3706663747984451 / 4000000000000) 1 (IntervalRat.scale (809 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-16508952492 / 1000000000000) (-16508952491 / 1000000000000), orderedInterval (-20349255358 / 1000000000000) (-20349255357 / 1000000000000)))) (orderedInterval (-15621698465 / 1000000000000) (-15621698112 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (3463246089142319 / 4000000000000) 1 (IntervalRat.scale (809 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-12588890203 / 1000000000000) (-12588890175 / 1000000000000), orderedInterval (24024070359 / 1000000000000) (24024070388 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (2471535824812127 / 4000000000000) 1 (IntervalRat.scale (809 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (7148914450 / 1000000000000) (7148914454 / 1000000000000), orderedInterval (-31298210188 / 1000000000000) (-31298210184 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (2802458206645833 / 4000000000000) 1 (IntervalRat.scale (809 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-22134199462 / 1000000000000) (-22134199461 / 1000000000000), orderedInterval (-20447250277 / 1000000000000) (-20447250276 / 1000000000000)))) (orderedInterval (-5270045064 / 1000000000000) (-5270044983 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (2336397481745977 / 4000000000000) 1 (IntervalRat.scale (809 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (17208656006 / 1000000000000) (17208656007 / 1000000000000), orderedInterval (28159357104 / 1000000000000) (28159357105 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (2064278030949517 / 4000000000000) 1 (IntervalRat.scale (809 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (35053580255 / 1000000000000) (35053581496 / 1000000000000), orderedInterval (-2233728507 / 1000000000000) (-2233727266 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (598308232470183 / 800000000000) 1 (IntervalRat.scale (809 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (24090906156 / 1000000000000) (24090906157 / 1000000000000), orderedInterval (16441556747 / 1000000000000) (16441556748 / 1000000000000)))) (orderedInterval (1410975009 / 1000000000000) (1410975156 / 1000000000000))) = true
  rfl'

theorem compactCertificate533_chunkChecks1_2 :
    compactCertificate533.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (1654952058249701 / 4000000000000) 1 (IntervalRat.scale (809 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-6525011909 / 1000000000000) (-6525011901 / 1000000000000), orderedInterval (38687698169 / 1000000000000) (38687698177 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (1402921187870461 / 4000000000000) 1 (IntervalRat.scale (809 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-14329951999 / 1000000000000) (-14329951834 / 1000000000000), orderedInterval (40142494427 / 1000000000000) (40142494592 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (877882939649983 / 4000000000000) 1 (IntervalRat.scale (809 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (18167887089 / 1000000000000) (18167887090 / 1000000000000), orderedInterval (50660072514 / 1000000000000) (50660072515 / 1000000000000)))) (orderedInterval (-7402345266 / 1000000000000) (-7402345162 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (472128364650561 / 4000000000000) 1 (IntervalRat.scale (809 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-39265000168 / 1000000000000) (-39264991552 / 1000000000000), orderedInterval (62229975416 / 1000000000000) (62229984032 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (1281920352074683 / 4000000000000) 1 (IntervalRat.scale (809 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (32667242572 / 1000000000000) (32667242573 / 1000000000000), orderedInterval (30269120435 / 1000000000000) (30269120436 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (1750352646016091 / 4000000000000) 1 (IntervalRat.scale (809 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-37862987994 / 1000000000000) (-37862986453 / 1000000000000), orderedInterval (4650975063 / 1000000000000) (4650976605 / 1000000000000)))) (orderedInterval (-1264975220 / 1000000000000) (-1264975001 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (740117060350017 / 4000000000000) 1 (IntervalRat.scale (809 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-26041727318 / 1000000000000) (-26041727317 / 1000000000000), orderedInterval (-52488925898 / 1000000000000) (-52488925897 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (3008534760252257 / 4000000000000) 1 (IntervalRat.scale (809 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-25426700479 / 1000000000000) (-25426653953 / 1000000000000), orderedInterval (14155561426 / 1000000000000) (14155607952 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (2009561792122063 / 4000000000000) 1 (IntervalRat.scale (809 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (17711549763 / 1000000000000) (17711549764 / 1000000000000), orderedInterval (30860886380 / 1000000000000) (30860886381 / 1000000000000)))) (orderedInterval (-9478927983 / 1000000000000) (-9478920783 / 1000000000000))) = true
  rfl'

theorem compactCertificate533_chunkChecks1 :
    compactCertificate533.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate533.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate533_chunkChecks1_0
    compactCertificate533_chunkChecks1_1 compactCertificate533_chunkChecks1_2

theorem compactCertificate533_chunkChecks2_0 :
    compactCertificate533.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (809 / 2) 2 (IntervalRat.scale (809 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-778975957 / 1000000000000) (-778975956 / 1000000000000), orderedInterval (-39663102555 / 1000000000000) (-39663102554 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (1191811476851909 / 4000000000000) 2 (IntervalRat.scale (809 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-13064728619 / 1000000000000) (-13064728618 / 1000000000000), orderedInterval (-44317237836 / 1000000000000) (-44317237835 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (385407344301797 / 800000000000) 2 (IntervalRat.scale (809 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-34620667712 / 1000000000000) (-34620653401 / 1000000000000), orderedInterval (11120030247 / 1000000000000) (11120044559 / 1000000000000)))) (orderedInterval (3294259546 / 1000000000000) (3294260777 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (347767616525263 / 4000000000000) 2 (IntervalRat.scale (809 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-20234626201 / 1000000000000) (-20234625960 / 1000000000000), orderedInterval (83260971971 / 1000000000000) (83260972213 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (934152735548611 / 4000000000000) 2 (IntervalRat.scale (809 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (50257599745 / 1000000000000) (50257602453 / 1000000000000), orderedInterval (-14254877619 / 1000000000000) (-14254874910 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (2536406395600887 / 4000000000000) 2 (IntervalRat.scale (809 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (8911165961 / 1000000000000) (8911165962 / 1000000000000), orderedInterval (30399594879 / 1000000000000) (30399594880 / 1000000000000)))) (orderedInterval (944551313 / 1000000000000) (944551423 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (1868305471098031 / 4000000000000) 2 (IntervalRat.scale (809 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (8625226335 / 1000000000000) (8625226349 / 1000000000000), orderedInterval (-35906235626 / 1000000000000) (-35906235612 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (3201373268973163 / 4000000000000) 2 (IntervalRat.scale (809 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-632621927 / 1000000000000) (-632621926 / 1000000000000), orderedInterval (-28195939695 / 1000000000000) (-28195939694 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (2358117060350017 / 4000000000000) 2 (IntervalRat.scale (809 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-9867068481 / 1000000000000) (-9867068465 / 1000000000000), orderedInterval (31353534536 / 1000000000000) (31353534552 / 1000000000000)))) (orderedInterval (423154309 / 1000000000000) (423154381 / 1000000000000))) = true
  rfl'

theorem compactCertificate533_chunkChecks2_1 :
    compactCertificate533.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (3617957987594191 / 4000000000000) 2 (IntervalRat.scale (809 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (12627653072 / 1000000000000) (12627653073 / 1000000000000), orderedInterval (23325116061 / 1000000000000) (23325116062 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (2088829018054039 / 4000000000000) 2 (IntervalRat.scale (809 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (34796005758 / 1000000000000) (34796005967 / 1000000000000), orderedInterval (2853118194 / 1000000000000) (2853118403 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (3706663747984451 / 4000000000000) 2 (IntervalRat.scale (809 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-16508952492 / 1000000000000) (-16508952491 / 1000000000000), orderedInterval (-20349255358 / 1000000000000) (-20349255357 / 1000000000000)))) (orderedInterval (19277379342 / 1000000000000) (19277380082 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (3463246089142319 / 4000000000000) 2 (IntervalRat.scale (809 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-12588890203 / 1000000000000) (-12588890175 / 1000000000000), orderedInterval (24024070359 / 1000000000000) (24024070388 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (2471535824812127 / 4000000000000) 2 (IntervalRat.scale (809 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (7148914450 / 1000000000000) (7148914454 / 1000000000000), orderedInterval (-31298210188 / 1000000000000) (-31298210184 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (2802458206645833 / 4000000000000) 2 (IntervalRat.scale (809 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-22134199462 / 1000000000000) (-22134199461 / 1000000000000), orderedInterval (-20447250277 / 1000000000000) (-20447250276 / 1000000000000)))) (orderedInterval (-2941625754 / 1000000000000) (-2941625621 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (2336397481745977 / 4000000000000) 2 (IntervalRat.scale (809 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (17208656006 / 1000000000000) (17208656007 / 1000000000000), orderedInterval (28159357104 / 1000000000000) (28159357105 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (2064278030949517 / 4000000000000) 2 (IntervalRat.scale (809 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (35053580255 / 1000000000000) (35053581496 / 1000000000000), orderedInterval (-2233728507 / 1000000000000) (-2233727266 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (598308232470183 / 800000000000) 2 (IntervalRat.scale (809 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (24090906156 / 1000000000000) (24090906157 / 1000000000000), orderedInterval (16441556747 / 1000000000000) (16441556748 / 1000000000000)))) (orderedInterval (738761022 / 1000000000000) (738761222 / 1000000000000))) = true
  rfl'

theorem compactCertificate533_chunkChecks2_2 :
    compactCertificate533.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (1654952058249701 / 4000000000000) 2 (IntervalRat.scale (809 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-6525011909 / 1000000000000) (-6525011901 / 1000000000000), orderedInterval (38687698169 / 1000000000000) (38687698177 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (1402921187870461 / 4000000000000) 2 (IntervalRat.scale (809 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-14329951999 / 1000000000000) (-14329951834 / 1000000000000), orderedInterval (40142494427 / 1000000000000) (40142494592 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (877882939649983 / 4000000000000) 2 (IntervalRat.scale (809 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (18167887089 / 1000000000000) (18167887090 / 1000000000000), orderedInterval (50660072514 / 1000000000000) (50660072515 / 1000000000000)))) (orderedInterval (-1857091630 / 1000000000000) (-1857091531 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (472128364650561 / 4000000000000) 2 (IntervalRat.scale (809 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-39265000168 / 1000000000000) (-39264991552 / 1000000000000), orderedInterval (62229975416 / 1000000000000) (62229984032 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (1281920352074683 / 4000000000000) 2 (IntervalRat.scale (809 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (32667242572 / 1000000000000) (32667242573 / 1000000000000), orderedInterval (30269120435 / 1000000000000) (30269120436 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (1750352646016091 / 4000000000000) 2 (IntervalRat.scale (809 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-37862987994 / 1000000000000) (-37862986453 / 1000000000000), orderedInterval (4650975063 / 1000000000000) (4650976605 / 1000000000000)))) (orderedInterval (-2989317838 / 1000000000000) (-2989317642 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (740117060350017 / 4000000000000) 2 (IntervalRat.scale (809 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-26041727318 / 1000000000000) (-26041727317 / 1000000000000), orderedInterval (-52488925898 / 1000000000000) (-52488925897 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (3008534760252257 / 4000000000000) 2 (IntervalRat.scale (809 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-25426700479 / 1000000000000) (-25426653953 / 1000000000000), orderedInterval (14155561426 / 1000000000000) (14155607952 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (2009561792122063 / 4000000000000) 2 (IntervalRat.scale (809 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (17711549763 / 1000000000000) (17711549764 / 1000000000000), orderedInterval (30860886380 / 1000000000000) (30860886381 / 1000000000000)))) (orderedInterval (-1973615733 / 1000000000000) (-1973602388 / 1000000000000))) = true
  rfl'

theorem compactCertificate533_chunkChecks2 :
    compactCertificate533.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate533.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate533_chunkChecks2_0
    compactCertificate533_chunkChecks2_1 compactCertificate533_chunkChecks2_2

theorem compactCertificate533_chunkChecks3_0 :
    compactCertificate533.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (809 / 2) 3 (IntervalRat.scale (809 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-778975957 / 1000000000000) (-778975956 / 1000000000000), orderedInterval (-39663102555 / 1000000000000) (-39663102554 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (1191811476851909 / 4000000000000) 3 (IntervalRat.scale (809 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-13064728619 / 1000000000000) (-13064728618 / 1000000000000), orderedInterval (-44317237836 / 1000000000000) (-44317237835 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (385407344301797 / 800000000000) 3 (IntervalRat.scale (809 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-34620667712 / 1000000000000) (-34620653401 / 1000000000000), orderedInterval (11120030247 / 1000000000000) (11120044559 / 1000000000000)))) (orderedInterval (14775465919 / 1000000000000) (14775467384 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (347767616525263 / 4000000000000) 3 (IntervalRat.scale (809 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-20234626201 / 1000000000000) (-20234625960 / 1000000000000), orderedInterval (83260971971 / 1000000000000) (83260972213 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (934152735548611 / 4000000000000) 3 (IntervalRat.scale (809 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (50257599745 / 1000000000000) (50257602453 / 1000000000000), orderedInterval (-14254877619 / 1000000000000) (-14254874910 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (2536406395600887 / 4000000000000) 3 (IntervalRat.scale (809 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (8911165961 / 1000000000000) (8911165962 / 1000000000000), orderedInterval (30399594879 / 1000000000000) (30399594880 / 1000000000000)))) (orderedInterval (8431983140 / 1000000000000) (8431983274 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (1868305471098031 / 4000000000000) 3 (IntervalRat.scale (809 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (8625226335 / 1000000000000) (8625226349 / 1000000000000), orderedInterval (-35906235626 / 1000000000000) (-35906235612 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (3201373268973163 / 4000000000000) 3 (IntervalRat.scale (809 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-632621927 / 1000000000000) (-632621926 / 1000000000000), orderedInterval (-28195939695 / 1000000000000) (-28195939694 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (2358117060350017 / 4000000000000) 3 (IntervalRat.scale (809 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-9867068481 / 1000000000000) (-9867068465 / 1000000000000), orderedInterval (31353534536 / 1000000000000) (31353534552 / 1000000000000)))) (orderedInterval (-9083257586 / 1000000000000) (-9083257456 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate533_chunkChecks3_1 :
    compactCertificate533.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (3617957987594191 / 4000000000000) 3 (IntervalRat.scale (809 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (12627653072 / 1000000000000) (12627653073 / 1000000000000), orderedInterval (23325116061 / 1000000000000) (23325116062 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (2088829018054039 / 4000000000000) 3 (IntervalRat.scale (809 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (34796005758 / 1000000000000) (34796005967 / 1000000000000), orderedInterval (2853118194 / 1000000000000) (2853118403 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (3706663747984451 / 4000000000000) 3 (IntervalRat.scale (809 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-16508952492 / 1000000000000) (-16508952491 / 1000000000000), orderedInterval (-20349255358 / 1000000000000) (-20349255357 / 1000000000000)))) (orderedInterval (80615169730 / 1000000000000) (80615171328 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (3463246089142319 / 4000000000000) 3 (IntervalRat.scale (809 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-12588890203 / 1000000000000) (-12588890175 / 1000000000000), orderedInterval (24024070359 / 1000000000000) (24024070388 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (2471535824812127 / 4000000000000) 3 (IntervalRat.scale (809 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (7148914450 / 1000000000000) (7148914454 / 1000000000000), orderedInterval (-31298210188 / 1000000000000) (-31298210184 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (2802458206645833 / 4000000000000) 3 (IntervalRat.scale (809 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-22134199462 / 1000000000000) (-22134199461 / 1000000000000), orderedInterval (-20447250277 / 1000000000000) (-20447250276 / 1000000000000)))) (orderedInterval (14271591482 / 1000000000000) (14271591708 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (2336397481745977 / 4000000000000) 3 (IntervalRat.scale (809 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (17208656006 / 1000000000000) (17208656007 / 1000000000000), orderedInterval (28159357104 / 1000000000000) (28159357105 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (2064278030949517 / 4000000000000) 3 (IntervalRat.scale (809 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (35053580255 / 1000000000000) (35053581496 / 1000000000000), orderedInterval (-2233728507 / 1000000000000) (-2233727266 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (598308232470183 / 800000000000) 3 (IntervalRat.scale (809 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (24090906156 / 1000000000000) (24090906157 / 1000000000000), orderedInterval (16441556747 / 1000000000000) (16441556748 / 1000000000000)))) (orderedInterval (-3907085901 / 1000000000000) (-3907085625 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate533_chunkChecks3_2 :
    compactCertificate533.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (1654952058249701 / 4000000000000) 3 (IntervalRat.scale (809 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-6525011909 / 1000000000000) (-6525011901 / 1000000000000), orderedInterval (38687698169 / 1000000000000) (38687698177 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (1402921187870461 / 4000000000000) 3 (IntervalRat.scale (809 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-14329951999 / 1000000000000) (-14329951834 / 1000000000000), orderedInterval (40142494427 / 1000000000000) (40142494592 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (877882939649983 / 4000000000000) 3 (IntervalRat.scale (809 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (18167887089 / 1000000000000) (18167887090 / 1000000000000), orderedInterval (50660072514 / 1000000000000) (50660072515 / 1000000000000)))) (orderedInterval (7841663491 / 1000000000000) (7841663586 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (472128364650561 / 4000000000000) 3 (IntervalRat.scale (809 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-39265000168 / 1000000000000) (-39264991552 / 1000000000000), orderedInterval (62229975416 / 1000000000000) (62229984032 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (1281920352074683 / 4000000000000) 3 (IntervalRat.scale (809 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (32667242572 / 1000000000000) (32667242573 / 1000000000000), orderedInterval (30269120435 / 1000000000000) (30269120436 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (1750352646016091 / 4000000000000) 3 (IntervalRat.scale (809 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-37862987994 / 1000000000000) (-37862986453 / 1000000000000), orderedInterval (4650975063 / 1000000000000) (4650976605 / 1000000000000)))) (orderedInterval (828723886 / 1000000000000) (828724085 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (740117060350017 / 4000000000000) 3 (IntervalRat.scale (809 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-26041727318 / 1000000000000) (-26041727317 / 1000000000000), orderedInterval (-52488925898 / 1000000000000) (-52488925897 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (3008534760252257 / 4000000000000) 3 (IntervalRat.scale (809 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-25426700479 / 1000000000000) (-25426653953 / 1000000000000), orderedInterval (14155561426 / 1000000000000) (14155607952 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (2009561792122063 / 4000000000000) 3 (IntervalRat.scale (809 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (17711549763 / 1000000000000) (17711549764 / 1000000000000), orderedInterval (30860886380 / 1000000000000) (30860886381 / 1000000000000)))) (orderedInterval (18536494279 / 1000000000000) (18536519018 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate533_chunkChecks3 :
    compactCertificate533.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate533.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate533_chunkChecks3_0
    compactCertificate533_chunkChecks3_1 compactCertificate533_chunkChecks3_2

theorem compactCertificate533_chunkChecks4_0 :
    compactCertificate533.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (809 / 2) 4 (IntervalRat.scale (809 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-778975957 / 1000000000000) (-778975956 / 1000000000000), orderedInterval (-39663102555 / 1000000000000) (-39663102554 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (1191811476851909 / 4000000000000) 4 (IntervalRat.scale (809 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (-13064728619 / 1000000000000) (-13064728618 / 1000000000000), orderedInterval (-44317237836 / 1000000000000) (-44317237835 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (385407344301797 / 800000000000) 4 (IntervalRat.scale (809 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-34620667712 / 1000000000000) (-34620653401 / 1000000000000), orderedInterval (11120030247 / 1000000000000) (11120044559 / 1000000000000)))) (orderedInterval (-4505339882 / 1000000000000) (-4505338135 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (347767616525263 / 4000000000000) 4 (IntervalRat.scale (809 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-20234626201 / 1000000000000) (-20234625960 / 1000000000000), orderedInterval (83260971971 / 1000000000000) (83260972213 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (934152735548611 / 4000000000000) 4 (IntervalRat.scale (809 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (50257599745 / 1000000000000) (50257602453 / 1000000000000), orderedInterval (-14254877619 / 1000000000000) (-14254874910 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (2536406395600887 / 4000000000000) 4 (IntervalRat.scale (809 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (8911165961 / 1000000000000) (8911165962 / 1000000000000), orderedInterval (30399594879 / 1000000000000) (30399594880 / 1000000000000)))) (orderedInterval (-3662951298 / 1000000000000) (-3662951110 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (1868305471098031 / 4000000000000) 4 (IntervalRat.scale (809 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (8625226335 / 1000000000000) (8625226349 / 1000000000000), orderedInterval (-35906235626 / 1000000000000) (-35906235612 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (3201373268973163 / 4000000000000) 4 (IntervalRat.scale (809 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-632621927 / 1000000000000) (-632621926 / 1000000000000), orderedInterval (-28195939695 / 1000000000000) (-28195939694 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (2358117060350017 / 4000000000000) 4 (IntervalRat.scale (809 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-9867068481 / 1000000000000) (-9867068465 / 1000000000000), orderedInterval (31353534536 / 1000000000000) (31353534552 / 1000000000000)))) (orderedInterval (-731946834 / 1000000000000) (-731946596 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate533_chunkChecks4_1 :
    compactCertificate533.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (3617957987594191 / 4000000000000) 4 (IntervalRat.scale (809 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (12627653072 / 1000000000000) (12627653073 / 1000000000000), orderedInterval (23325116061 / 1000000000000) (23325116062 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (2088829018054039 / 4000000000000) 4 (IntervalRat.scale (809 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (34796005758 / 1000000000000) (34796005967 / 1000000000000), orderedInterval (2853118194 / 1000000000000) (2853118403 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (3706663747984451 / 4000000000000) 4 (IntervalRat.scale (809 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-16508952492 / 1000000000000) (-16508952491 / 1000000000000), orderedInterval (-20349255358 / 1000000000000) (-20349255357 / 1000000000000)))) (orderedInterval (-113971887203 / 1000000000000) (-113971883686 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (3463246089142319 / 4000000000000) 4 (IntervalRat.scale (809 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (-12588890203 / 1000000000000) (-12588890175 / 1000000000000), orderedInterval (24024070359 / 1000000000000) (24024070388 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (2471535824812127 / 4000000000000) 4 (IntervalRat.scale (809 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (7148914450 / 1000000000000) (7148914454 / 1000000000000), orderedInterval (-31298210188 / 1000000000000) (-31298210184 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (2802458206645833 / 4000000000000) 4 (IntervalRat.scale (809 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-22134199462 / 1000000000000) (-22134199461 / 1000000000000), orderedInterval (-20447250277 / 1000000000000) (-20447250276 / 1000000000000)))) (orderedInterval (9388525121 / 1000000000000) (9388525515 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (2336397481745977 / 4000000000000) 4 (IntervalRat.scale (809 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (17208656006 / 1000000000000) (17208656007 / 1000000000000), orderedInterval (28159357104 / 1000000000000) (28159357105 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (2064278030949517 / 4000000000000) 4 (IntervalRat.scale (809 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (35053580255 / 1000000000000) (35053581496 / 1000000000000), orderedInterval (-2233728507 / 1000000000000) (-2233727266 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (598308232470183 / 800000000000) 4 (IntervalRat.scale (809 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (24090906156 / 1000000000000) (24090906157 / 1000000000000), orderedInterval (16441556747 / 1000000000000) (16441556748 / 1000000000000)))) (orderedInterval (2776676122 / 1000000000000) (2776676515 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate533_chunkChecks4_2 :
    compactCertificate533.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (1654952058249701 / 4000000000000) 4 (IntervalRat.scale (809 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-6525011909 / 1000000000000) (-6525011901 / 1000000000000), orderedInterval (38687698169 / 1000000000000) (38687698177 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (1402921187870461 / 4000000000000) 4 (IntervalRat.scale (809 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-14329951999 / 1000000000000) (-14329951834 / 1000000000000), orderedInterval (40142494427 / 1000000000000) (40142494592 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (877882939649983 / 4000000000000) 4 (IntervalRat.scale (809 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (18167887089 / 1000000000000) (18167887090 / 1000000000000), orderedInterval (50660072514 / 1000000000000) (50660072515 / 1000000000000)))) (orderedInterval (1612834431 / 1000000000000) (1612834524 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (472128364650561 / 4000000000000) 4 (IntervalRat.scale (809 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-39265000168 / 1000000000000) (-39264991552 / 1000000000000), orderedInterval (62229975416 / 1000000000000) (62229984032 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (1281920352074683 / 4000000000000) 4 (IntervalRat.scale (809 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (32667242572 / 1000000000000) (32667242573 / 1000000000000), orderedInterval (30269120435 / 1000000000000) (30269120436 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (1750352646016091 / 4000000000000) 4 (IntervalRat.scale (809 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-37862987994 / 1000000000000) (-37862986453 / 1000000000000), orderedInterval (4650975063 / 1000000000000) (4650976605 / 1000000000000)))) (orderedInterval (3683339474 / 1000000000000) (3683339684 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (740117060350017 / 4000000000000) 4 (IntervalRat.scale (809 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-26041727318 / 1000000000000) (-26041727317 / 1000000000000), orderedInterval (-52488925898 / 1000000000000) (-52488925897 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (3008534760252257 / 4000000000000) 4 (IntervalRat.scale (809 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (-25426700479 / 1000000000000) (-25426653953 / 1000000000000), orderedInterval (14155561426 / 1000000000000) (14155607952 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (2009561792122063 / 4000000000000) 4 (IntervalRat.scale (809 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (17711549763 / 1000000000000) (17711549764 / 1000000000000), orderedInterval (30860886380 / 1000000000000) (30860886381 / 1000000000000)))) (orderedInterval (16735587400 / 1000000000000) (16735633369 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate533_chunkChecks4 :
    compactCertificate533.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate533.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate533_chunkChecks4_0
    compactCertificate533_chunkChecks4_1 compactCertificate533_chunkChecks4_2

theorem compactCertificate533_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate533.chunkCheck r b = true :=
  compactCertificate533.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate533_chunkChecks0
    · exact compactCertificate533_chunkChecks1
    · exact compactCertificate533_chunkChecks2
    · exact compactCertificate533_chunkChecks3
    · exact compactCertificate533_chunkChecks4)

theorem compactCertificate533_coefficient0 :
    compactCertificate533.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate533_coefficient1 :
    compactCertificate533.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate533_coefficient2 :
    compactCertificate533.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate533_coefficient3 :
    compactCertificate533.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate533_coefficient4 :
    compactCertificate533.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate533_coefficients : ∀ r : Fin 5,
    compactCertificate533.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate533_coefficient0
  · exact compactCertificate533_coefficient1
  · exact compactCertificate533_coefficient2
  · exact compactCertificate533_coefficient3
  · exact compactCertificate533_coefficient4

theorem compactCertificate533_lower : (1 : ℚ) ≤ compactCertificate533.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate533, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate533_proves {t : ℝ} (ht : t ∈ compactCertificate533.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate533.proves compactCertificate533_states compactCertificate533_chunks
    compactCertificate533_coefficients compactCertificate533_lower ht

end Erdos232
