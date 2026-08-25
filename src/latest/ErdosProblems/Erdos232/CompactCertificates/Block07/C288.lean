/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate288 : CompactCertificate where
  left := 162
  right := 163
  center := 325 / 2
  grid := fun i =>
    match i.val with
    | 0 => 52
    | 1 => 38
    | 2 => 62
    | 3 => 11
    | 4 => 30
    | 5 => 81
    | 6 => 60
    | 7 => 102
    | 8 => 75
    | 9 => 116
    | 10 => 67
    | 11 => 119
    | 12 => 111
    | 13 => 79
    | 14 => 90
    | 15 => 75
    | 16 => 66
    | 17 => 96
    | 18 => 53
    | 19 => 45
    | 20 => 28
    | 21 => 15
    | 22 => 41
    | 23 => 56
    | 24 => 24
    | 25 => 96
    | _ => 64
  point := fun i =>
    match i.val with
    | 0 => 325 / 2
    | 1 => 19151482322713 / 160000000000
    | 2 => 6193195891129 / 32000000000
    | 3 => 5588354777291 / 160000000000
    | 4 => 15011106998927 / 160000000000
    | 5 => 40758075578259 / 160000000000
    | 6 => 30022213997867 / 160000000000
    | 7 => 51443575397591 / 160000000000
    | 8 => 37893104801669 / 160000000000
    | 9 => 58137767414987 / 160000000000
    | 10 => 33565855667123 / 160000000000
    | 11 => 59563199905807 / 160000000000
    | 12 => 55651667687083 / 160000000000
    | 13 => 39715656022939 / 160000000000
    | 14 => 45033320996781 / 160000000000
    | 15 => 37544088087389 / 160000000000
    | 16 => 33171340423169 / 160000000000
    | 17 => 9614347369731 / 32000000000
    | 18 => 26593790800057 / 160000000000
    | 19 => 22543850979377 / 160000000000
    | 20 => 14106895198331 / 160000000000
    | 21 => 7586735155077 / 160000000000
    | 22 => 20599461776231 / 160000000000
    | 23 => 28126803953287 / 160000000000
    | 24 => 11893104801669 / 160000000000
    | 25 => 48344810733349 / 160000000000
    | _ => 32292093074891 / 160000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-4888950321 / 1000000000000) (-4888950308 / 1000000000000), orderedInterval (62415175949 / 1000000000000) (62415175963 / 1000000000000))
    | 1 => (orderedInterval (65014124395 / 1000000000000) (65014124396 / 1000000000000), orderedInterval (32769929929 / 1000000000000) (32769929930 / 1000000000000))
    | 2 => (orderedInterval (-25287986277 / 1000000000000) (-25287984458 / 1000000000000), orderedInterval (51542643771 / 1000000000000) (51542645590 / 1000000000000))
    | 3 => (orderedInterval (-123307345605 / 1000000000000) (-123307345604 / 1000000000000), orderedInterval (-53199610721 / 1000000000000) (-53199610720 / 1000000000000))
    | 4 => (orderedInterval (28686886578 / 1000000000000) (28686886579 / 1000000000000), orderedInterval (77065783849 / 1000000000000) (77065783850 / 1000000000000))
    | 5 => (orderedInterval (-43459510573 / 1000000000000) (-43459510572 / 1000000000000), orderedInterval (-24620660701 / 1000000000000) (-24620660700 / 1000000000000))
    | 6 => (orderedInterval (-4189606878 / 1000000000000) (-4189606868 / 1000000000000), orderedInterval (58108085686 / 1000000000000) (58108085696 / 1000000000000))
    | 7 => (orderedInterval (42586678737 / 1000000000000) (42586684131 / 1000000000000), orderedInterval (-12965444357 / 1000000000000) (-12965438962 / 1000000000000))
    | 8 => (orderedInterval (-47201415938 / 1000000000000) (-47201402605 / 1000000000000), orderedInterval (21549327779 / 1000000000000) (21549341112 / 1000000000000))
    | 9 => (orderedInterval (-11513061901 / 1000000000000) (-11513061840 / 1000000000000), orderedInterval (40258626718 / 1000000000000) (40258626779 / 1000000000000))
    | 10 => (orderedInterval (-4659893504 / 1000000000000) (-4659893503 / 1000000000000), orderedInterval (-54878787050 / 1000000000000) (-54878787048 / 1000000000000))
    | 11 => (orderedInterval (29505122678 / 1000000000000) (29505145903 / 1000000000000), orderedInterval (-29014616627 / 1000000000000) (-29014593402 / 1000000000000))
    | 12 => (orderedInterval (4646466225 / 1000000000000) (4646466230 / 1000000000000), orderedInterval (-42535618815 / 1000000000000) (-42535618810 / 1000000000000))
    | 13 => (orderedInterval (-37093802902 / 1000000000000) (-37093802901 / 1000000000000), orderedInterval (-34403680533 / 1000000000000) (-34403680532 / 1000000000000))
    | 14 => (orderedInterval (-22806365267 / 1000000000000) (-22806363466 / 1000000000000), orderedInterval (41774598052 / 1000000000000) (41774599853 / 1000000000000))
    | 15 => (orderedInterval (9531698141 / 1000000000000) (9531698180 / 1000000000000), orderedInterval (-51227801473 / 1000000000000) (-51227801433 / 1000000000000))
    | 16 => (orderedInterval (38198149758 / 1000000000000) (38198149759 / 1000000000000), orderedInterval (40052610981 / 1000000000000) (40052610982 / 1000000000000))
    | 17 => (orderedInterval (-16196628410 / 1000000000000) (-16196628121 / 1000000000000), orderedInterval (43114894366 / 1000000000000) (43114894655 / 1000000000000))
    | 18 => (orderedInterval (-29204209385 / 1000000000000) (-29204209384 / 1000000000000), orderedInterval (-54476877573 / 1000000000000) (-54476877572 / 1000000000000))
    | 19 => (orderedInterval (-20627630456 / 1000000000000) (-20627630455 / 1000000000000), orderedInterval (-63901734178 / 1000000000000) (-63901734177 / 1000000000000))
    | 20 => (orderedInterval (70921956316 / 1000000000000) (70921956317 / 1000000000000), orderedInterval (46401166158 / 1000000000000) (46401166159 / 1000000000000))
    | 21 => (orderedInterval (-101968934515 / 1000000000000) (-101968934514 / 1000000000000), orderedInterval (-53951077276 / 1000000000000) (-53951077275 / 1000000000000))
    | 22 => (orderedInterval (-46671014057 / 1000000000000) (-46671014056 / 1000000000000), orderedInterval (-52416942070 / 1000000000000) (-52416942069 / 1000000000000))
    | 23 => (orderedInterval (36324238213 / 1000000000000) (36324238214 / 1000000000000), orderedInterval (47875644754 / 1000000000000) (47875644755 / 1000000000000))
    | 24 => (orderedInterval (-25806347763 / 1000000000000) (-25806347302 / 1000000000000), orderedInterval (89048504629 / 1000000000000) (89048505090 / 1000000000000))
    | 25 => (orderedInterval (44758191136 / 1000000000000) (44758191141 / 1000000000000), orderedInterval (10105934121 / 1000000000000) (10105934126 / 1000000000000))
    | _ => (orderedInterval (56149081697 / 1000000000000) (56149081747 / 1000000000000), orderedInterval (1116919813 / 1000000000000) (1116919863 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-2815931117 / 1000000000000) (-2815930993 / 1000000000000)
      | 1 => orderedInterval (5474726586 / 1000000000000) (5474726606 / 1000000000000)
      | 2 => orderedInterval (-2454308828 / 1000000000000) (-2454308329 / 1000000000000)
      | 3 => orderedInterval (5894799318 / 1000000000000) (5894802696 / 1000000000000)
      | 4 => orderedInterval (-3476166042 / 1000000000000) (-3476166013 / 1000000000000)
      | 5 => orderedInterval (-2490581946 / 1000000000000) (-2490581921 / 1000000000000)
      | 6 => orderedInterval (8145938818 / 1000000000000) (8145938860 / 1000000000000)
      | 7 => orderedInterval (157838581 / 1000000000000) (157838601 / 1000000000000)
      | _ => orderedInterval (-14334022648 / 1000000000000) (-14334022590 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (28566385495 / 1000000000000) (28566385641 / 1000000000000)
      | 1 => orderedInterval (4492370016 / 1000000000000) (4492370039 / 1000000000000)
      | 2 => orderedInterval (1550288589 / 1000000000000) (1550289404 / 1000000000000)
      | 3 => orderedInterval (-30693930247 / 1000000000000) (-30693922525 / 1000000000000)
      | 4 => orderedInterval (-3692026906 / 1000000000000) (-3692026858 / 1000000000000)
      | 5 => orderedInterval (-1737461259 / 1000000000000) (-1737461221 / 1000000000000)
      | 6 => orderedInterval (12865036676 / 1000000000000) (12865036715 / 1000000000000)
      | 7 => orderedInterval (-2736410074 / 1000000000000) (-2736410056 / 1000000000000)
      | _ => orderedInterval (-1544357589 / 1000000000000) (-1544357512 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (3538242490 / 1000000000000) (3538242663 / 1000000000000)
      | 1 => orderedInterval (-8030857426 / 1000000000000) (-8030857394 / 1000000000000)
      | 2 => orderedInterval (7555882644 / 1000000000000) (7555884013 / 1000000000000)
      | 3 => orderedInterval (-31476974221 / 1000000000000) (-31476956506 / 1000000000000)
      | 4 => orderedInterval (8245416801 / 1000000000000) (8245416882 / 1000000000000)
      | 5 => orderedInterval (4756934432 / 1000000000000) (4756934493 / 1000000000000)
      | 6 => orderedInterval (-6521883701 / 1000000000000) (-6521883664 / 1000000000000)
      | 7 => orderedInterval (2449795279 / 1000000000000) (2449795297 / 1000000000000)
      | _ => orderedInterval (28889925662 / 1000000000000) (28889925772 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-29991669035 / 1000000000000) (-29991668831 / 1000000000000)
      | 1 => orderedInterval (-7240251377 / 1000000000000) (-7240251330 / 1000000000000)
      | 2 => orderedInterval (-4756345457 / 1000000000000) (-4756343111 / 1000000000000)
      | 3 => orderedInterval (138509715371 / 1000000000000) (138509755921 / 1000000000000)
      | 4 => orderedInterval (5112725361 / 1000000000000) (5112725499 / 1000000000000)
      | 5 => orderedInterval (-465506454 / 1000000000000) (-465506353 / 1000000000000)
      | 6 => orderedInterval (-11879348418 / 1000000000000) (-11879348382 / 1000000000000)
      | 7 => orderedInterval (4013857174 / 1000000000000) (4013857193 / 1000000000000)
      | _ => orderedInterval (5460867127 / 1000000000000) (5460867293 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-4375998977 / 1000000000000) (-4375998734 / 1000000000000)
      | 1 => orderedInterval (18865496114 / 1000000000000) (18865496186 / 1000000000000)
      | 2 => orderedInterval (-25219530262 / 1000000000000) (-25219526135 / 1000000000000)
      | 3 => orderedInterval (164004657575 / 1000000000000) (164004750664 / 1000000000000)
      | 4 => orderedInterval (-19882083796 / 1000000000000) (-19882083558 / 1000000000000)
      | 5 => orderedInterval (-10153298852 / 1000000000000) (-10153298680 / 1000000000000)
      | 6 => orderedInterval (6116903576 / 1000000000000) (6116903611 / 1000000000000)
      | 7 => orderedInterval (-3431160201 / 1000000000000) (-3431160182 / 1000000000000)
      | _ => orderedInterval (-68693862579 / 1000000000000) (-68693862320 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-5897707278 / 1000000000000) (-5897703083 / 1000000000000)
    | 1 => orderedInterval (7069894701 / 1000000000000) (7069903627 / 1000000000000)
    | 2 => orderedInterval (9406481960 / 1000000000000) (9406501556 / 1000000000000)
    | 3 => orderedInterval (98764044292 / 1000000000000) (98764087899 / 1000000000000)
    | _ => orderedInterval (57231122598 / 1000000000000) (57231220852 / 1000000000000)

theorem compactCertificate288_stateChecks0 :
    compactCertificate288.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 52 12 (325 / 2)) (orderedInterval (-4888950321 / 1000000000000) (-4888950308 / 1000000000000), orderedInterval (62415175949 / 1000000000000) (62415175963 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (19151482322713 / 160000000000)) (orderedInterval (65014124395 / 1000000000000) (65014124396 / 1000000000000), orderedInterval (32769929929 / 1000000000000) (32769929930 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 62 12 (6193195891129 / 32000000000)) (orderedInterval (-25287986277 / 1000000000000) (-25287984458 / 1000000000000), orderedInterval (51542643771 / 1000000000000) (51542645590 / 1000000000000))) = true
  rfl'

theorem compactCertificate288_stateChecks1 :
    compactCertificate288.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 11 12 (5588354777291 / 160000000000)) (orderedInterval (-123307345605 / 1000000000000) (-123307345604 / 1000000000000), orderedInterval (-53199610721 / 1000000000000) (-53199610720 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (15011106998927 / 160000000000)) (orderedInterval (28686886578 / 1000000000000) (28686886579 / 1000000000000), orderedInterval (77065783849 / 1000000000000) (77065783850 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 81 12 (40758075578259 / 160000000000)) (orderedInterval (-43459510573 / 1000000000000) (-43459510572 / 1000000000000), orderedInterval (-24620660701 / 1000000000000) (-24620660700 / 1000000000000))) = true
  rfl'

theorem compactCertificate288_stateChecks2 :
    compactCertificate288.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 60 12 (30022213997867 / 160000000000)) (orderedInterval (-4189606878 / 1000000000000) (-4189606868 / 1000000000000), orderedInterval (58108085686 / 1000000000000) (58108085696 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 102 12 (51443575397591 / 160000000000)) (orderedInterval (42586678737 / 1000000000000) (42586684131 / 1000000000000), orderedInterval (-12965444357 / 1000000000000) (-12965438962 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 75 12 (37893104801669 / 160000000000)) (orderedInterval (-47201415938 / 1000000000000) (-47201402605 / 1000000000000), orderedInterval (21549327779 / 1000000000000) (21549341112 / 1000000000000))) = true
  rfl'

theorem compactCertificate288_stateChecks3 :
    compactCertificate288.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 116 12 (58137767414987 / 160000000000)) (orderedInterval (-11513061901 / 1000000000000) (-11513061840 / 1000000000000), orderedInterval (40258626718 / 1000000000000) (40258626779 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (33565855667123 / 160000000000)) (orderedInterval (-4659893504 / 1000000000000) (-4659893503 / 1000000000000), orderedInterval (-54878787050 / 1000000000000) (-54878787048 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 119 12 (59563199905807 / 160000000000)) (orderedInterval (29505122678 / 1000000000000) (29505145903 / 1000000000000), orderedInterval (-29014616627 / 1000000000000) (-29014593402 / 1000000000000))) = true
  rfl'

theorem compactCertificate288_stateChecks4 :
    compactCertificate288.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 111 12 (55651667687083 / 160000000000)) (orderedInterval (4646466225 / 1000000000000) (4646466230 / 1000000000000), orderedInterval (-42535618815 / 1000000000000) (-42535618810 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 79 12 (39715656022939 / 160000000000)) (orderedInterval (-37093802902 / 1000000000000) (-37093802901 / 1000000000000), orderedInterval (-34403680533 / 1000000000000) (-34403680532 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 90 12 (45033320996781 / 160000000000)) (orderedInterval (-22806365267 / 1000000000000) (-22806363466 / 1000000000000), orderedInterval (41774598052 / 1000000000000) (41774599853 / 1000000000000))) = true
  rfl'

theorem compactCertificate288_stateChecks5 :
    compactCertificate288.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 75 12 (37544088087389 / 160000000000)) (orderedInterval (9531698141 / 1000000000000) (9531698180 / 1000000000000), orderedInterval (-51227801473 / 1000000000000) (-51227801433 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 66 12 (33171340423169 / 160000000000)) (orderedInterval (38198149758 / 1000000000000) (38198149759 / 1000000000000), orderedInterval (40052610981 / 1000000000000) (40052610982 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 96 12 (9614347369731 / 32000000000)) (orderedInterval (-16196628410 / 1000000000000) (-16196628121 / 1000000000000), orderedInterval (43114894366 / 1000000000000) (43114894655 / 1000000000000))) = true
  rfl'

theorem compactCertificate288_stateChecks6 :
    compactCertificate288.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 53 12 (26593790800057 / 160000000000)) (orderedInterval (-29204209385 / 1000000000000) (-29204209384 / 1000000000000), orderedInterval (-54476877573 / 1000000000000) (-54476877572 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (22543850979377 / 160000000000)) (orderedInterval (-20627630456 / 1000000000000) (-20627630455 / 1000000000000), orderedInterval (-63901734178 / 1000000000000) (-63901734177 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 28 12 (14106895198331 / 160000000000)) (orderedInterval (70921956316 / 1000000000000) (70921956317 / 1000000000000), orderedInterval (46401166158 / 1000000000000) (46401166159 / 1000000000000))) = true
  rfl'

theorem compactCertificate288_stateChecks7 :
    compactCertificate288.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 15 12 (7586735155077 / 160000000000)) (orderedInterval (-101968934515 / 1000000000000) (-101968934514 / 1000000000000), orderedInterval (-53951077276 / 1000000000000) (-53951077275 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 41 12 (20599461776231 / 160000000000)) (orderedInterval (-46671014057 / 1000000000000) (-46671014056 / 1000000000000), orderedInterval (-52416942070 / 1000000000000) (-52416942069 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 56 12 (28126803953287 / 160000000000)) (orderedInterval (36324238213 / 1000000000000) (36324238214 / 1000000000000), orderedInterval (47875644754 / 1000000000000) (47875644755 / 1000000000000))) = true
  rfl'

theorem compactCertificate288_stateChecks8 :
    compactCertificate288.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 24 12 (11893104801669 / 160000000000)) (orderedInterval (-25806347763 / 1000000000000) (-25806347302 / 1000000000000), orderedInterval (89048504629 / 1000000000000) (89048505090 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 96 12 (48344810733349 / 160000000000)) (orderedInterval (44758191136 / 1000000000000) (44758191141 / 1000000000000), orderedInterval (10105934121 / 1000000000000) (10105934126 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (32292093074891 / 160000000000)) (orderedInterval (56149081697 / 1000000000000) (56149081747 / 1000000000000), orderedInterval (1116919813 / 1000000000000) (1116919863 / 1000000000000))) = true
  rfl'

theorem compactCertificate288_states : ∀ j,
    BesselStateValid (compactCertificate288.point j) (compactCertificate288.state j) :=
  compactCertificate288.statesValid_of_checks3 compactCertificate288_stateChecks0
    compactCertificate288_stateChecks1 compactCertificate288_stateChecks2
    compactCertificate288_stateChecks3 compactCertificate288_stateChecks4
    compactCertificate288_stateChecks5 compactCertificate288_stateChecks6
    compactCertificate288_stateChecks7 compactCertificate288_stateChecks8

theorem compactCertificate288_chunkChecks0_0 :
    compactCertificate288.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (325 / 2) 0 (IntervalRat.scale (325 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-4888950321 / 1000000000000) (-4888950308 / 1000000000000), orderedInterval (62415175949 / 1000000000000) (62415175963 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (19151482322713 / 160000000000) 0 (IntervalRat.scale (325 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (65014124395 / 1000000000000) (65014124396 / 1000000000000), orderedInterval (32769929929 / 1000000000000) (32769929930 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (6193195891129 / 32000000000) 0 (IntervalRat.scale (325 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-25287986277 / 1000000000000) (-25287984458 / 1000000000000), orderedInterval (51542643771 / 1000000000000) (51542645590 / 1000000000000)))) (orderedInterval (-2815931117 / 1000000000000) (-2815930993 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (5588354777291 / 160000000000) 0 (IntervalRat.scale (325 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-123307345605 / 1000000000000) (-123307345604 / 1000000000000), orderedInterval (-53199610721 / 1000000000000) (-53199610720 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (15011106998927 / 160000000000) 0 (IntervalRat.scale (325 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (28686886578 / 1000000000000) (28686886579 / 1000000000000), orderedInterval (77065783849 / 1000000000000) (77065783850 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (40758075578259 / 160000000000) 0 (IntervalRat.scale (325 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-43459510573 / 1000000000000) (-43459510572 / 1000000000000), orderedInterval (-24620660701 / 1000000000000) (-24620660700 / 1000000000000)))) (orderedInterval (5474726586 / 1000000000000) (5474726606 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (30022213997867 / 160000000000) 0 (IntervalRat.scale (325 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-4189606878 / 1000000000000) (-4189606868 / 1000000000000), orderedInterval (58108085686 / 1000000000000) (58108085696 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (51443575397591 / 160000000000) 0 (IntervalRat.scale (325 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (42586678737 / 1000000000000) (42586684131 / 1000000000000), orderedInterval (-12965444357 / 1000000000000) (-12965438962 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (37893104801669 / 160000000000) 0 (IntervalRat.scale (325 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-47201415938 / 1000000000000) (-47201402605 / 1000000000000), orderedInterval (21549327779 / 1000000000000) (21549341112 / 1000000000000)))) (orderedInterval (-2454308828 / 1000000000000) (-2454308329 / 1000000000000))) = true
  rfl'

theorem compactCertificate288_chunkChecks0_1 :
    compactCertificate288.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (58137767414987 / 160000000000) 0 (IntervalRat.scale (325 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-11513061901 / 1000000000000) (-11513061840 / 1000000000000), orderedInterval (40258626718 / 1000000000000) (40258626779 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (33565855667123 / 160000000000) 0 (IntervalRat.scale (325 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-4659893504 / 1000000000000) (-4659893503 / 1000000000000), orderedInterval (-54878787050 / 1000000000000) (-54878787048 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (59563199905807 / 160000000000) 0 (IntervalRat.scale (325 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (29505122678 / 1000000000000) (29505145903 / 1000000000000), orderedInterval (-29014616627 / 1000000000000) (-29014593402 / 1000000000000)))) (orderedInterval (5894799318 / 1000000000000) (5894802696 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (55651667687083 / 160000000000) 0 (IntervalRat.scale (325 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (4646466225 / 1000000000000) (4646466230 / 1000000000000), orderedInterval (-42535618815 / 1000000000000) (-42535618810 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (39715656022939 / 160000000000) 0 (IntervalRat.scale (325 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-37093802902 / 1000000000000) (-37093802901 / 1000000000000), orderedInterval (-34403680533 / 1000000000000) (-34403680532 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (45033320996781 / 160000000000) 0 (IntervalRat.scale (325 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-22806365267 / 1000000000000) (-22806363466 / 1000000000000), orderedInterval (41774598052 / 1000000000000) (41774599853 / 1000000000000)))) (orderedInterval (-3476166042 / 1000000000000) (-3476166013 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (37544088087389 / 160000000000) 0 (IntervalRat.scale (325 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (9531698141 / 1000000000000) (9531698180 / 1000000000000), orderedInterval (-51227801473 / 1000000000000) (-51227801433 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (33171340423169 / 160000000000) 0 (IntervalRat.scale (325 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (38198149758 / 1000000000000) (38198149759 / 1000000000000), orderedInterval (40052610981 / 1000000000000) (40052610982 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (9614347369731 / 32000000000) 0 (IntervalRat.scale (325 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-16196628410 / 1000000000000) (-16196628121 / 1000000000000), orderedInterval (43114894366 / 1000000000000) (43114894655 / 1000000000000)))) (orderedInterval (-2490581946 / 1000000000000) (-2490581921 / 1000000000000))) = true
  rfl'

theorem compactCertificate288_chunkChecks0_2 :
    compactCertificate288.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (26593790800057 / 160000000000) 0 (IntervalRat.scale (325 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-29204209385 / 1000000000000) (-29204209384 / 1000000000000), orderedInterval (-54476877573 / 1000000000000) (-54476877572 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (22543850979377 / 160000000000) 0 (IntervalRat.scale (325 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-20627630456 / 1000000000000) (-20627630455 / 1000000000000), orderedInterval (-63901734178 / 1000000000000) (-63901734177 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (14106895198331 / 160000000000) 0 (IntervalRat.scale (325 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (70921956316 / 1000000000000) (70921956317 / 1000000000000), orderedInterval (46401166158 / 1000000000000) (46401166159 / 1000000000000)))) (orderedInterval (8145938818 / 1000000000000) (8145938860 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (7586735155077 / 160000000000) 0 (IntervalRat.scale (325 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-101968934515 / 1000000000000) (-101968934514 / 1000000000000), orderedInterval (-53951077276 / 1000000000000) (-53951077275 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (20599461776231 / 160000000000) 0 (IntervalRat.scale (325 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-46671014057 / 1000000000000) (-46671014056 / 1000000000000), orderedInterval (-52416942070 / 1000000000000) (-52416942069 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (28126803953287 / 160000000000) 0 (IntervalRat.scale (325 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (36324238213 / 1000000000000) (36324238214 / 1000000000000), orderedInterval (47875644754 / 1000000000000) (47875644755 / 1000000000000)))) (orderedInterval (157838581 / 1000000000000) (157838601 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (11893104801669 / 160000000000) 0 (IntervalRat.scale (325 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-25806347763 / 1000000000000) (-25806347302 / 1000000000000), orderedInterval (89048504629 / 1000000000000) (89048505090 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (48344810733349 / 160000000000) 0 (IntervalRat.scale (325 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (44758191136 / 1000000000000) (44758191141 / 1000000000000), orderedInterval (10105934121 / 1000000000000) (10105934126 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (32292093074891 / 160000000000) 0 (IntervalRat.scale (325 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (56149081697 / 1000000000000) (56149081747 / 1000000000000), orderedInterval (1116919813 / 1000000000000) (1116919863 / 1000000000000)))) (orderedInterval (-14334022648 / 1000000000000) (-14334022590 / 1000000000000))) = true
  rfl'

theorem compactCertificate288_chunkChecks0 :
    compactCertificate288.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate288.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate288_chunkChecks0_0
    compactCertificate288_chunkChecks0_1 compactCertificate288_chunkChecks0_2

theorem compactCertificate288_chunkChecks1_0 :
    compactCertificate288.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (325 / 2) 1 (IntervalRat.scale (325 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-4888950321 / 1000000000000) (-4888950308 / 1000000000000), orderedInterval (62415175949 / 1000000000000) (62415175963 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (19151482322713 / 160000000000) 1 (IntervalRat.scale (325 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (65014124395 / 1000000000000) (65014124396 / 1000000000000), orderedInterval (32769929929 / 1000000000000) (32769929930 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (6193195891129 / 32000000000) 1 (IntervalRat.scale (325 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-25287986277 / 1000000000000) (-25287984458 / 1000000000000), orderedInterval (51542643771 / 1000000000000) (51542645590 / 1000000000000)))) (orderedInterval (28566385495 / 1000000000000) (28566385641 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (5588354777291 / 160000000000) 1 (IntervalRat.scale (325 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-123307345605 / 1000000000000) (-123307345604 / 1000000000000), orderedInterval (-53199610721 / 1000000000000) (-53199610720 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (15011106998927 / 160000000000) 1 (IntervalRat.scale (325 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (28686886578 / 1000000000000) (28686886579 / 1000000000000), orderedInterval (77065783849 / 1000000000000) (77065783850 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (40758075578259 / 160000000000) 1 (IntervalRat.scale (325 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-43459510573 / 1000000000000) (-43459510572 / 1000000000000), orderedInterval (-24620660701 / 1000000000000) (-24620660700 / 1000000000000)))) (orderedInterval (4492370016 / 1000000000000) (4492370039 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (30022213997867 / 160000000000) 1 (IntervalRat.scale (325 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-4189606878 / 1000000000000) (-4189606868 / 1000000000000), orderedInterval (58108085686 / 1000000000000) (58108085696 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (51443575397591 / 160000000000) 1 (IntervalRat.scale (325 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (42586678737 / 1000000000000) (42586684131 / 1000000000000), orderedInterval (-12965444357 / 1000000000000) (-12965438962 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (37893104801669 / 160000000000) 1 (IntervalRat.scale (325 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-47201415938 / 1000000000000) (-47201402605 / 1000000000000), orderedInterval (21549327779 / 1000000000000) (21549341112 / 1000000000000)))) (orderedInterval (1550288589 / 1000000000000) (1550289404 / 1000000000000))) = true
  rfl'

theorem compactCertificate288_chunkChecks1_1 :
    compactCertificate288.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (58137767414987 / 160000000000) 1 (IntervalRat.scale (325 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-11513061901 / 1000000000000) (-11513061840 / 1000000000000), orderedInterval (40258626718 / 1000000000000) (40258626779 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (33565855667123 / 160000000000) 1 (IntervalRat.scale (325 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-4659893504 / 1000000000000) (-4659893503 / 1000000000000), orderedInterval (-54878787050 / 1000000000000) (-54878787048 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (59563199905807 / 160000000000) 1 (IntervalRat.scale (325 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (29505122678 / 1000000000000) (29505145903 / 1000000000000), orderedInterval (-29014616627 / 1000000000000) (-29014593402 / 1000000000000)))) (orderedInterval (-30693930247 / 1000000000000) (-30693922525 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (55651667687083 / 160000000000) 1 (IntervalRat.scale (325 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (4646466225 / 1000000000000) (4646466230 / 1000000000000), orderedInterval (-42535618815 / 1000000000000) (-42535618810 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (39715656022939 / 160000000000) 1 (IntervalRat.scale (325 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-37093802902 / 1000000000000) (-37093802901 / 1000000000000), orderedInterval (-34403680533 / 1000000000000) (-34403680532 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (45033320996781 / 160000000000) 1 (IntervalRat.scale (325 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-22806365267 / 1000000000000) (-22806363466 / 1000000000000), orderedInterval (41774598052 / 1000000000000) (41774599853 / 1000000000000)))) (orderedInterval (-3692026906 / 1000000000000) (-3692026858 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (37544088087389 / 160000000000) 1 (IntervalRat.scale (325 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (9531698141 / 1000000000000) (9531698180 / 1000000000000), orderedInterval (-51227801473 / 1000000000000) (-51227801433 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (33171340423169 / 160000000000) 1 (IntervalRat.scale (325 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (38198149758 / 1000000000000) (38198149759 / 1000000000000), orderedInterval (40052610981 / 1000000000000) (40052610982 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (9614347369731 / 32000000000) 1 (IntervalRat.scale (325 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-16196628410 / 1000000000000) (-16196628121 / 1000000000000), orderedInterval (43114894366 / 1000000000000) (43114894655 / 1000000000000)))) (orderedInterval (-1737461259 / 1000000000000) (-1737461221 / 1000000000000))) = true
  rfl'

theorem compactCertificate288_chunkChecks1_2 :
    compactCertificate288.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (26593790800057 / 160000000000) 1 (IntervalRat.scale (325 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-29204209385 / 1000000000000) (-29204209384 / 1000000000000), orderedInterval (-54476877573 / 1000000000000) (-54476877572 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (22543850979377 / 160000000000) 1 (IntervalRat.scale (325 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-20627630456 / 1000000000000) (-20627630455 / 1000000000000), orderedInterval (-63901734178 / 1000000000000) (-63901734177 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (14106895198331 / 160000000000) 1 (IntervalRat.scale (325 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (70921956316 / 1000000000000) (70921956317 / 1000000000000), orderedInterval (46401166158 / 1000000000000) (46401166159 / 1000000000000)))) (orderedInterval (12865036676 / 1000000000000) (12865036715 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (7586735155077 / 160000000000) 1 (IntervalRat.scale (325 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-101968934515 / 1000000000000) (-101968934514 / 1000000000000), orderedInterval (-53951077276 / 1000000000000) (-53951077275 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (20599461776231 / 160000000000) 1 (IntervalRat.scale (325 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-46671014057 / 1000000000000) (-46671014056 / 1000000000000), orderedInterval (-52416942070 / 1000000000000) (-52416942069 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (28126803953287 / 160000000000) 1 (IntervalRat.scale (325 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (36324238213 / 1000000000000) (36324238214 / 1000000000000), orderedInterval (47875644754 / 1000000000000) (47875644755 / 1000000000000)))) (orderedInterval (-2736410074 / 1000000000000) (-2736410056 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (11893104801669 / 160000000000) 1 (IntervalRat.scale (325 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-25806347763 / 1000000000000) (-25806347302 / 1000000000000), orderedInterval (89048504629 / 1000000000000) (89048505090 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (48344810733349 / 160000000000) 1 (IntervalRat.scale (325 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (44758191136 / 1000000000000) (44758191141 / 1000000000000), orderedInterval (10105934121 / 1000000000000) (10105934126 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (32292093074891 / 160000000000) 1 (IntervalRat.scale (325 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (56149081697 / 1000000000000) (56149081747 / 1000000000000), orderedInterval (1116919813 / 1000000000000) (1116919863 / 1000000000000)))) (orderedInterval (-1544357589 / 1000000000000) (-1544357512 / 1000000000000))) = true
  rfl'

theorem compactCertificate288_chunkChecks1 :
    compactCertificate288.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate288.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate288_chunkChecks1_0
    compactCertificate288_chunkChecks1_1 compactCertificate288_chunkChecks1_2

theorem compactCertificate288_chunkChecks2_0 :
    compactCertificate288.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (325 / 2) 2 (IntervalRat.scale (325 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-4888950321 / 1000000000000) (-4888950308 / 1000000000000), orderedInterval (62415175949 / 1000000000000) (62415175963 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (19151482322713 / 160000000000) 2 (IntervalRat.scale (325 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (65014124395 / 1000000000000) (65014124396 / 1000000000000), orderedInterval (32769929929 / 1000000000000) (32769929930 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (6193195891129 / 32000000000) 2 (IntervalRat.scale (325 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-25287986277 / 1000000000000) (-25287984458 / 1000000000000), orderedInterval (51542643771 / 1000000000000) (51542645590 / 1000000000000)))) (orderedInterval (3538242490 / 1000000000000) (3538242663 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (5588354777291 / 160000000000) 2 (IntervalRat.scale (325 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-123307345605 / 1000000000000) (-123307345604 / 1000000000000), orderedInterval (-53199610721 / 1000000000000) (-53199610720 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (15011106998927 / 160000000000) 2 (IntervalRat.scale (325 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (28686886578 / 1000000000000) (28686886579 / 1000000000000), orderedInterval (77065783849 / 1000000000000) (77065783850 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (40758075578259 / 160000000000) 2 (IntervalRat.scale (325 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-43459510573 / 1000000000000) (-43459510572 / 1000000000000), orderedInterval (-24620660701 / 1000000000000) (-24620660700 / 1000000000000)))) (orderedInterval (-8030857426 / 1000000000000) (-8030857394 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (30022213997867 / 160000000000) 2 (IntervalRat.scale (325 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-4189606878 / 1000000000000) (-4189606868 / 1000000000000), orderedInterval (58108085686 / 1000000000000) (58108085696 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (51443575397591 / 160000000000) 2 (IntervalRat.scale (325 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (42586678737 / 1000000000000) (42586684131 / 1000000000000), orderedInterval (-12965444357 / 1000000000000) (-12965438962 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (37893104801669 / 160000000000) 2 (IntervalRat.scale (325 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-47201415938 / 1000000000000) (-47201402605 / 1000000000000), orderedInterval (21549327779 / 1000000000000) (21549341112 / 1000000000000)))) (orderedInterval (7555882644 / 1000000000000) (7555884013 / 1000000000000))) = true
  rfl'

theorem compactCertificate288_chunkChecks2_1 :
    compactCertificate288.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (58137767414987 / 160000000000) 2 (IntervalRat.scale (325 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-11513061901 / 1000000000000) (-11513061840 / 1000000000000), orderedInterval (40258626718 / 1000000000000) (40258626779 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (33565855667123 / 160000000000) 2 (IntervalRat.scale (325 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-4659893504 / 1000000000000) (-4659893503 / 1000000000000), orderedInterval (-54878787050 / 1000000000000) (-54878787048 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (59563199905807 / 160000000000) 2 (IntervalRat.scale (325 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (29505122678 / 1000000000000) (29505145903 / 1000000000000), orderedInterval (-29014616627 / 1000000000000) (-29014593402 / 1000000000000)))) (orderedInterval (-31476974221 / 1000000000000) (-31476956506 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (55651667687083 / 160000000000) 2 (IntervalRat.scale (325 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (4646466225 / 1000000000000) (4646466230 / 1000000000000), orderedInterval (-42535618815 / 1000000000000) (-42535618810 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (39715656022939 / 160000000000) 2 (IntervalRat.scale (325 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-37093802902 / 1000000000000) (-37093802901 / 1000000000000), orderedInterval (-34403680533 / 1000000000000) (-34403680532 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (45033320996781 / 160000000000) 2 (IntervalRat.scale (325 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-22806365267 / 1000000000000) (-22806363466 / 1000000000000), orderedInterval (41774598052 / 1000000000000) (41774599853 / 1000000000000)))) (orderedInterval (8245416801 / 1000000000000) (8245416882 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (37544088087389 / 160000000000) 2 (IntervalRat.scale (325 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (9531698141 / 1000000000000) (9531698180 / 1000000000000), orderedInterval (-51227801473 / 1000000000000) (-51227801433 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (33171340423169 / 160000000000) 2 (IntervalRat.scale (325 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (38198149758 / 1000000000000) (38198149759 / 1000000000000), orderedInterval (40052610981 / 1000000000000) (40052610982 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (9614347369731 / 32000000000) 2 (IntervalRat.scale (325 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-16196628410 / 1000000000000) (-16196628121 / 1000000000000), orderedInterval (43114894366 / 1000000000000) (43114894655 / 1000000000000)))) (orderedInterval (4756934432 / 1000000000000) (4756934493 / 1000000000000))) = true
  rfl'

theorem compactCertificate288_chunkChecks2_2 :
    compactCertificate288.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (26593790800057 / 160000000000) 2 (IntervalRat.scale (325 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-29204209385 / 1000000000000) (-29204209384 / 1000000000000), orderedInterval (-54476877573 / 1000000000000) (-54476877572 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (22543850979377 / 160000000000) 2 (IntervalRat.scale (325 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-20627630456 / 1000000000000) (-20627630455 / 1000000000000), orderedInterval (-63901734178 / 1000000000000) (-63901734177 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (14106895198331 / 160000000000) 2 (IntervalRat.scale (325 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (70921956316 / 1000000000000) (70921956317 / 1000000000000), orderedInterval (46401166158 / 1000000000000) (46401166159 / 1000000000000)))) (orderedInterval (-6521883701 / 1000000000000) (-6521883664 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (7586735155077 / 160000000000) 2 (IntervalRat.scale (325 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-101968934515 / 1000000000000) (-101968934514 / 1000000000000), orderedInterval (-53951077276 / 1000000000000) (-53951077275 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (20599461776231 / 160000000000) 2 (IntervalRat.scale (325 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-46671014057 / 1000000000000) (-46671014056 / 1000000000000), orderedInterval (-52416942070 / 1000000000000) (-52416942069 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (28126803953287 / 160000000000) 2 (IntervalRat.scale (325 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (36324238213 / 1000000000000) (36324238214 / 1000000000000), orderedInterval (47875644754 / 1000000000000) (47875644755 / 1000000000000)))) (orderedInterval (2449795279 / 1000000000000) (2449795297 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (11893104801669 / 160000000000) 2 (IntervalRat.scale (325 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-25806347763 / 1000000000000) (-25806347302 / 1000000000000), orderedInterval (89048504629 / 1000000000000) (89048505090 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (48344810733349 / 160000000000) 2 (IntervalRat.scale (325 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (44758191136 / 1000000000000) (44758191141 / 1000000000000), orderedInterval (10105934121 / 1000000000000) (10105934126 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (32292093074891 / 160000000000) 2 (IntervalRat.scale (325 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (56149081697 / 1000000000000) (56149081747 / 1000000000000), orderedInterval (1116919813 / 1000000000000) (1116919863 / 1000000000000)))) (orderedInterval (28889925662 / 1000000000000) (28889925772 / 1000000000000))) = true
  rfl'

theorem compactCertificate288_chunkChecks2 :
    compactCertificate288.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate288.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate288_chunkChecks2_0
    compactCertificate288_chunkChecks2_1 compactCertificate288_chunkChecks2_2

theorem compactCertificate288_chunkChecks3_0 :
    compactCertificate288.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (325 / 2) 3 (IntervalRat.scale (325 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-4888950321 / 1000000000000) (-4888950308 / 1000000000000), orderedInterval (62415175949 / 1000000000000) (62415175963 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (19151482322713 / 160000000000) 3 (IntervalRat.scale (325 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (65014124395 / 1000000000000) (65014124396 / 1000000000000), orderedInterval (32769929929 / 1000000000000) (32769929930 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (6193195891129 / 32000000000) 3 (IntervalRat.scale (325 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-25287986277 / 1000000000000) (-25287984458 / 1000000000000), orderedInterval (51542643771 / 1000000000000) (51542645590 / 1000000000000)))) (orderedInterval (-29991669035 / 1000000000000) (-29991668831 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (5588354777291 / 160000000000) 3 (IntervalRat.scale (325 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-123307345605 / 1000000000000) (-123307345604 / 1000000000000), orderedInterval (-53199610721 / 1000000000000) (-53199610720 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (15011106998927 / 160000000000) 3 (IntervalRat.scale (325 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (28686886578 / 1000000000000) (28686886579 / 1000000000000), orderedInterval (77065783849 / 1000000000000) (77065783850 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (40758075578259 / 160000000000) 3 (IntervalRat.scale (325 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-43459510573 / 1000000000000) (-43459510572 / 1000000000000), orderedInterval (-24620660701 / 1000000000000) (-24620660700 / 1000000000000)))) (orderedInterval (-7240251377 / 1000000000000) (-7240251330 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (30022213997867 / 160000000000) 3 (IntervalRat.scale (325 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-4189606878 / 1000000000000) (-4189606868 / 1000000000000), orderedInterval (58108085686 / 1000000000000) (58108085696 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (51443575397591 / 160000000000) 3 (IntervalRat.scale (325 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (42586678737 / 1000000000000) (42586684131 / 1000000000000), orderedInterval (-12965444357 / 1000000000000) (-12965438962 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (37893104801669 / 160000000000) 3 (IntervalRat.scale (325 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-47201415938 / 1000000000000) (-47201402605 / 1000000000000), orderedInterval (21549327779 / 1000000000000) (21549341112 / 1000000000000)))) (orderedInterval (-4756345457 / 1000000000000) (-4756343111 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate288_chunkChecks3_1 :
    compactCertificate288.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (58137767414987 / 160000000000) 3 (IntervalRat.scale (325 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-11513061901 / 1000000000000) (-11513061840 / 1000000000000), orderedInterval (40258626718 / 1000000000000) (40258626779 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (33565855667123 / 160000000000) 3 (IntervalRat.scale (325 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-4659893504 / 1000000000000) (-4659893503 / 1000000000000), orderedInterval (-54878787050 / 1000000000000) (-54878787048 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (59563199905807 / 160000000000) 3 (IntervalRat.scale (325 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (29505122678 / 1000000000000) (29505145903 / 1000000000000), orderedInterval (-29014616627 / 1000000000000) (-29014593402 / 1000000000000)))) (orderedInterval (138509715371 / 1000000000000) (138509755921 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (55651667687083 / 160000000000) 3 (IntervalRat.scale (325 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (4646466225 / 1000000000000) (4646466230 / 1000000000000), orderedInterval (-42535618815 / 1000000000000) (-42535618810 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (39715656022939 / 160000000000) 3 (IntervalRat.scale (325 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-37093802902 / 1000000000000) (-37093802901 / 1000000000000), orderedInterval (-34403680533 / 1000000000000) (-34403680532 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (45033320996781 / 160000000000) 3 (IntervalRat.scale (325 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-22806365267 / 1000000000000) (-22806363466 / 1000000000000), orderedInterval (41774598052 / 1000000000000) (41774599853 / 1000000000000)))) (orderedInterval (5112725361 / 1000000000000) (5112725499 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (37544088087389 / 160000000000) 3 (IntervalRat.scale (325 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (9531698141 / 1000000000000) (9531698180 / 1000000000000), orderedInterval (-51227801473 / 1000000000000) (-51227801433 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (33171340423169 / 160000000000) 3 (IntervalRat.scale (325 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (38198149758 / 1000000000000) (38198149759 / 1000000000000), orderedInterval (40052610981 / 1000000000000) (40052610982 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (9614347369731 / 32000000000) 3 (IntervalRat.scale (325 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-16196628410 / 1000000000000) (-16196628121 / 1000000000000), orderedInterval (43114894366 / 1000000000000) (43114894655 / 1000000000000)))) (orderedInterval (-465506454 / 1000000000000) (-465506353 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate288_chunkChecks3_2 :
    compactCertificate288.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (26593790800057 / 160000000000) 3 (IntervalRat.scale (325 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-29204209385 / 1000000000000) (-29204209384 / 1000000000000), orderedInterval (-54476877573 / 1000000000000) (-54476877572 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (22543850979377 / 160000000000) 3 (IntervalRat.scale (325 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-20627630456 / 1000000000000) (-20627630455 / 1000000000000), orderedInterval (-63901734178 / 1000000000000) (-63901734177 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (14106895198331 / 160000000000) 3 (IntervalRat.scale (325 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (70921956316 / 1000000000000) (70921956317 / 1000000000000), orderedInterval (46401166158 / 1000000000000) (46401166159 / 1000000000000)))) (orderedInterval (-11879348418 / 1000000000000) (-11879348382 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (7586735155077 / 160000000000) 3 (IntervalRat.scale (325 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-101968934515 / 1000000000000) (-101968934514 / 1000000000000), orderedInterval (-53951077276 / 1000000000000) (-53951077275 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (20599461776231 / 160000000000) 3 (IntervalRat.scale (325 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-46671014057 / 1000000000000) (-46671014056 / 1000000000000), orderedInterval (-52416942070 / 1000000000000) (-52416942069 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (28126803953287 / 160000000000) 3 (IntervalRat.scale (325 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (36324238213 / 1000000000000) (36324238214 / 1000000000000), orderedInterval (47875644754 / 1000000000000) (47875644755 / 1000000000000)))) (orderedInterval (4013857174 / 1000000000000) (4013857193 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (11893104801669 / 160000000000) 3 (IntervalRat.scale (325 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-25806347763 / 1000000000000) (-25806347302 / 1000000000000), orderedInterval (89048504629 / 1000000000000) (89048505090 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (48344810733349 / 160000000000) 3 (IntervalRat.scale (325 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (44758191136 / 1000000000000) (44758191141 / 1000000000000), orderedInterval (10105934121 / 1000000000000) (10105934126 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (32292093074891 / 160000000000) 3 (IntervalRat.scale (325 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (56149081697 / 1000000000000) (56149081747 / 1000000000000), orderedInterval (1116919813 / 1000000000000) (1116919863 / 1000000000000)))) (orderedInterval (5460867127 / 1000000000000) (5460867293 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate288_chunkChecks3 :
    compactCertificate288.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate288.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate288_chunkChecks3_0
    compactCertificate288_chunkChecks3_1 compactCertificate288_chunkChecks3_2

theorem compactCertificate288_chunkChecks4_0 :
    compactCertificate288.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (325 / 2) 4 (IntervalRat.scale (325 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-4888950321 / 1000000000000) (-4888950308 / 1000000000000), orderedInterval (62415175949 / 1000000000000) (62415175963 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (19151482322713 / 160000000000) 4 (IntervalRat.scale (325 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (65014124395 / 1000000000000) (65014124396 / 1000000000000), orderedInterval (32769929929 / 1000000000000) (32769929930 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (6193195891129 / 32000000000) 4 (IntervalRat.scale (325 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-25287986277 / 1000000000000) (-25287984458 / 1000000000000), orderedInterval (51542643771 / 1000000000000) (51542645590 / 1000000000000)))) (orderedInterval (-4375998977 / 1000000000000) (-4375998734 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (5588354777291 / 160000000000) 4 (IntervalRat.scale (325 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-123307345605 / 1000000000000) (-123307345604 / 1000000000000), orderedInterval (-53199610721 / 1000000000000) (-53199610720 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (15011106998927 / 160000000000) 4 (IntervalRat.scale (325 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (28686886578 / 1000000000000) (28686886579 / 1000000000000), orderedInterval (77065783849 / 1000000000000) (77065783850 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (40758075578259 / 160000000000) 4 (IntervalRat.scale (325 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-43459510573 / 1000000000000) (-43459510572 / 1000000000000), orderedInterval (-24620660701 / 1000000000000) (-24620660700 / 1000000000000)))) (orderedInterval (18865496114 / 1000000000000) (18865496186 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (30022213997867 / 160000000000) 4 (IntervalRat.scale (325 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-4189606878 / 1000000000000) (-4189606868 / 1000000000000), orderedInterval (58108085686 / 1000000000000) (58108085696 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (51443575397591 / 160000000000) 4 (IntervalRat.scale (325 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (42586678737 / 1000000000000) (42586684131 / 1000000000000), orderedInterval (-12965444357 / 1000000000000) (-12965438962 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (37893104801669 / 160000000000) 4 (IntervalRat.scale (325 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-47201415938 / 1000000000000) (-47201402605 / 1000000000000), orderedInterval (21549327779 / 1000000000000) (21549341112 / 1000000000000)))) (orderedInterval (-25219530262 / 1000000000000) (-25219526135 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate288_chunkChecks4_1 :
    compactCertificate288.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (58137767414987 / 160000000000) 4 (IntervalRat.scale (325 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (-11513061901 / 1000000000000) (-11513061840 / 1000000000000), orderedInterval (40258626718 / 1000000000000) (40258626779 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (33565855667123 / 160000000000) 4 (IntervalRat.scale (325 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-4659893504 / 1000000000000) (-4659893503 / 1000000000000), orderedInterval (-54878787050 / 1000000000000) (-54878787048 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (59563199905807 / 160000000000) 4 (IntervalRat.scale (325 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (29505122678 / 1000000000000) (29505145903 / 1000000000000), orderedInterval (-29014616627 / 1000000000000) (-29014593402 / 1000000000000)))) (orderedInterval (164004657575 / 1000000000000) (164004750664 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (55651667687083 / 160000000000) 4 (IntervalRat.scale (325 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (4646466225 / 1000000000000) (4646466230 / 1000000000000), orderedInterval (-42535618815 / 1000000000000) (-42535618810 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (39715656022939 / 160000000000) 4 (IntervalRat.scale (325 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-37093802902 / 1000000000000) (-37093802901 / 1000000000000), orderedInterval (-34403680533 / 1000000000000) (-34403680532 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (45033320996781 / 160000000000) 4 (IntervalRat.scale (325 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-22806365267 / 1000000000000) (-22806363466 / 1000000000000), orderedInterval (41774598052 / 1000000000000) (41774599853 / 1000000000000)))) (orderedInterval (-19882083796 / 1000000000000) (-19882083558 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (37544088087389 / 160000000000) 4 (IntervalRat.scale (325 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (9531698141 / 1000000000000) (9531698180 / 1000000000000), orderedInterval (-51227801473 / 1000000000000) (-51227801433 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (33171340423169 / 160000000000) 4 (IntervalRat.scale (325 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (38198149758 / 1000000000000) (38198149759 / 1000000000000), orderedInterval (40052610981 / 1000000000000) (40052610982 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (9614347369731 / 32000000000) 4 (IntervalRat.scale (325 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-16196628410 / 1000000000000) (-16196628121 / 1000000000000), orderedInterval (43114894366 / 1000000000000) (43114894655 / 1000000000000)))) (orderedInterval (-10153298852 / 1000000000000) (-10153298680 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate288_chunkChecks4_2 :
    compactCertificate288.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (26593790800057 / 160000000000) 4 (IntervalRat.scale (325 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-29204209385 / 1000000000000) (-29204209384 / 1000000000000), orderedInterval (-54476877573 / 1000000000000) (-54476877572 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (22543850979377 / 160000000000) 4 (IntervalRat.scale (325 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (-20627630456 / 1000000000000) (-20627630455 / 1000000000000), orderedInterval (-63901734178 / 1000000000000) (-63901734177 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (14106895198331 / 160000000000) 4 (IntervalRat.scale (325 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (70921956316 / 1000000000000) (70921956317 / 1000000000000), orderedInterval (46401166158 / 1000000000000) (46401166159 / 1000000000000)))) (orderedInterval (6116903576 / 1000000000000) (6116903611 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (7586735155077 / 160000000000) 4 (IntervalRat.scale (325 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-101968934515 / 1000000000000) (-101968934514 / 1000000000000), orderedInterval (-53951077276 / 1000000000000) (-53951077275 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (20599461776231 / 160000000000) 4 (IntervalRat.scale (325 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-46671014057 / 1000000000000) (-46671014056 / 1000000000000), orderedInterval (-52416942070 / 1000000000000) (-52416942069 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (28126803953287 / 160000000000) 4 (IntervalRat.scale (325 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (36324238213 / 1000000000000) (36324238214 / 1000000000000), orderedInterval (47875644754 / 1000000000000) (47875644755 / 1000000000000)))) (orderedInterval (-3431160201 / 1000000000000) (-3431160182 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (11893104801669 / 160000000000) 4 (IntervalRat.scale (325 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-25806347763 / 1000000000000) (-25806347302 / 1000000000000), orderedInterval (89048504629 / 1000000000000) (89048505090 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (48344810733349 / 160000000000) 4 (IntervalRat.scale (325 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (44758191136 / 1000000000000) (44758191141 / 1000000000000), orderedInterval (10105934121 / 1000000000000) (10105934126 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (32292093074891 / 160000000000) 4 (IntervalRat.scale (325 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (56149081697 / 1000000000000) (56149081747 / 1000000000000), orderedInterval (1116919813 / 1000000000000) (1116919863 / 1000000000000)))) (orderedInterval (-68693862579 / 1000000000000) (-68693862320 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate288_chunkChecks4 :
    compactCertificate288.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate288.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate288_chunkChecks4_0
    compactCertificate288_chunkChecks4_1 compactCertificate288_chunkChecks4_2

theorem compactCertificate288_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate288.chunkCheck r b = true :=
  compactCertificate288.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate288_chunkChecks0
    · exact compactCertificate288_chunkChecks1
    · exact compactCertificate288_chunkChecks2
    · exact compactCertificate288_chunkChecks3
    · exact compactCertificate288_chunkChecks4)

theorem compactCertificate288_coefficient0 :
    compactCertificate288.coefficientCheck (0 : Fin 5) = true := by
  rfl'

theorem compactCertificate288_coefficient1 :
    compactCertificate288.coefficientCheck (1 : Fin 5) = true := by
  rfl'

theorem compactCertificate288_coefficient2 :
    compactCertificate288.coefficientCheck (2 : Fin 5) = true := by
  rfl'

theorem compactCertificate288_coefficient3 :
    compactCertificate288.coefficientCheck (3 : Fin 5) = true := by
  rfl'

theorem compactCertificate288_coefficient4 :
    compactCertificate288.coefficientCheck (4 : Fin 5) = true := by
  rfl'

theorem compactCertificate288_coefficients : ∀ r : Fin 5,
    compactCertificate288.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate288_coefficient0
  · exact compactCertificate288_coefficient1
  · exact compactCertificate288_coefficient2
  · exact compactCertificate288_coefficient3
  · exact compactCertificate288_coefficient4

theorem compactCertificate288_lower : (1 : ℚ) ≤ compactCertificate288.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate288, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate288_proves {t : ℝ} (ht : t ∈ compactCertificate288.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate288.proves compactCertificate288_states compactCertificate288_chunks
    compactCertificate288_coefficients compactCertificate288_lower ht

end Erdos232
